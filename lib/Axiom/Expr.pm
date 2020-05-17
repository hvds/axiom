package Axiom::Expr;

use v5.10;
use strict;
use warnings;

use Math::BigRat;

our $SUCCEED = qr{(?=)};
our $FAIL = qr{(?!)};
our $DICT;

my %listtype = map +($_ => 1), qw{ pluslist mullist };

sub new {
    my($class, $hash) = @_;
    my($type, $args) = @$hash{qw{ type args }};
    return $args->[0] if $type eq 'nothing';
    if ($listtype{$type}) {
        return $args->[0] if @$args == 1;
        $args = [ map {
            $_->type eq $type ? @{ $_->args } : $_
        } @$args ];
    }
    return bless {
        type => $type,
        args => $args,
    }, $class;
}

sub args { shift->{args} }
sub type { shift->{type} }
sub atom { 0 }
sub const { 0 }
sub iter { 0 }

sub _clean {
    my($self) = @_;
    return $self if $self->atom;
    my $type = $self->type;
    my $args = $self->args;
    $_ = $_->_clean for @$args;
    my $sub = {
        equals => undef,
        function => undef,
        expr => sub { return $self->args->[0] },
        braceexpr => sub { return $self->args->[0] },
        parenexpr => sub { return $self->args->[0] },
        pluslist => sub {
          retry_pluslist:
            # +(null) -> 0
            return Axiom::Expr::Const->new({
                type => 'integer',
                args => [ '0' ],
            }) if @$args == 0;
            # +(x) -> x
            return $args->[0] if @$args == 1;

            my @const = ();
            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                if ($arg->type eq 'pluslist') {
                    # +(a, +(b, c), d) -> +(a, b, c, d)
                    splice @$args, $i, 1, @{ $arg->args };
                    goto retry_pluslist;
                }
                if ($arg->const) {
                    if ($arg->args->[0] eq '0') {
                        # +(a, 0, b) -> +(a, b)
                        splice @$args, $i, 1;
                        goto retry_pluslist;
                    }
                    push @const, $i;
                }
            }
            if (@const > 1) {
                # +(a, c1, b, c2) -> +(a, eval(c1+c2), b)
                my $sum = Math::BigRat->new(0);
                $sum += Math::BigRat->new(
                    $_->args->[0],
                    $_->type eq 'rational' ? $_->args->[1] : 1,
                ) for @$args[@const];
                my($sumn, $sumd) = $sum->parts;
                my $repl = ($sumn == 0)
                    ? undef
                    : Axiom::Expr::Const->new({
                        type => 'rational',
                        args => [ "$sumn", "$sumd" ],
                    });
                splice(@$args, $_, 1) for reverse @const;
                splice(@$args, $const[0], 0, $repl) if $repl;
                goto retry_pluslist;
            }
            my(@con, @plus, @minus) = ();
            for (0 .. $#$args) {
                push @{
                    $args->[$_]->const ? \@con
                    : $args->[$_]->type eq 'negate' ? \@minus : \@plus
                }, $_;
            }
            for my $m (@minus) {
                my $me = $args->[$m]->args->[0];
                for my $p (@plus) {
                    next if $me->diff($args->[$p]);
                    # +(a, b, c, -b) -> +(a, c)
                    for (sort { $b <=> $a } $m, $p) {
                        splice @$args, $_, 1;
                    }
                    goto retry_pluslist;
                }
            }
            # This should probably change
            # +(-a, b, -const) -> +(b, -const, -a)
            # +(-a, b, const) -> +(const, b, -a)
            my @order = (@con && $args->[$con[0]]->args->[0] =~ /^-/)
                ? (@plus, @con, @minus)
                : (@con, @plus, @minus);
            @$args = @$args[@order];
            return $self;
        },
        negate => sub {
            my $arg = $args->[0];
            if ($arg->type eq 'negate') {
                # -(-(a)) -> a
                return $arg->args->[0];
            }
            if ($arg->const) {
                my $nargs = [ @{ $arg->args } ];
                $nargs->[0] = -$nargs->[0];
                # -(const) -> eval(-const)
                return Axiom::Expr::Const->new({
                    type => $arg->type,
                    args => $nargs,
                });
            }
            if ($arg->type eq 'pluslist') {
                # -(a - b) -> b - a
                return Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ map {
                        $_->type eq 'negate'
                            ? $_->args->[0]->copy
                            : Axiom::Expr->new({
                                type => 'negate',
                                args => [ $_->copy ],
                            });
                    } @{ $arg->args } ],
                });
            }
            return $self;
        },
        mullist => sub {
          retry_mullist:
            # x(null) -> 1
            return Axiom::Expr::Const->new({
                type => 'integer',
                args => [ '1' ],
            }) if @$args == 0;
            # x(a) -> a
            return $args->[0] if @$args == 1;

            my @const = ();
            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                if ($arg->type eq 'mullist') {
                    # x(a, x(b, c), d) -> x(a, b, c, d)
                    splice @$args, $i, 1, @{ $arg->args };
                    goto retry_mullist;
                }
                if ($arg->const) {
                    if ($arg->args->[0] eq '0') {
                        # x(a, 0, b) -> 0
                        return $arg;
                    }
                    if ($arg->type eq 'integer' && $arg->args->[0] eq '1') {
                        # x(a, 1, b) -> x(a, b)
                        splice @$args, $i, 1;
                        goto retry_mullist;
                    }
                    push @const, $i;
                }
            }
            if (@const > 1) {
                my $prod = Math::BigRat->new(1);
                $prod *= Math::BigRat->new(
                    $_->args->[0],
                    $_->type eq 'rational' ? $_->args->[1] : 1,
                ) for @$args[@const];
                my($prodn, $prodd) = $prod->parts;
                my $repl = ($prodn eq '1' && $prodd eq '1')
                    ? undef
                    : Axiom::Expr::Const->new({
                        type => 'rational',
                        args => [ "$prodn", "$prodd" ],
                    });
                # x(a, c1, b, c2) -> x(a, eval(c1 . c2), b)
                splice(@$args, $_, 1) for reverse @const;
                splice(@$args, $const[0], 0, $repl) if $repl;
                goto retry_mullist;
            }
            my(@con, @mul, @div) = ();
            for (0 .. $#$args) {
                push @{
                    $args->[$_]->const ? \@con
                    : $args->[$_]->type eq 'recip' ? \@div : \@mul
                }, $_;
            }
            for my $d (@div) {
                my $de = $args->[$d]->args->[0];
                for my $m (@mul) {
                    next if $de->diff($args->[$m]);
                    # x(a, b, c, 1/b) -> x(a, c)
                    for (sort { $b <=> $a } $d, $m) {
                        splice @$args, $_, 1;
                    }
                    goto retry_mullist;
                }
            }
            # Not sure what we want here
            # x(a, const p/q, 1/b, c, 1/d) -> x(const p/q, a, c, 1/b, 1/d)
            my @order = (@con, @mul, @div);
            @$args = @$args[@order];
            return $self;
        },
        recip => sub {
            my $arg = $args->[0];
            if ($arg->type eq 'recip') {
                # FIXME: x=0?
                # 1/(1/x) -> x
                return $arg->args->[0];
            }
            if ($arg->type eq 'integer') {
                # 1/1 -> 1
                return $arg if $arg->args->[0] eq '1';
                # 1/c -> eval(1/c)
                return Axiom::Expr::Const->new({
                    type => 'rational',
                    args => [ '1', $arg->args->[0] ],
                });
            }
            if ($arg->type eq 'rational') {
                # 1/(p/q) -> q/p
                return Axiom::Expr::Const->new({
                    type => 'rational',
                    args => [ @{ $arg->args }[1, 0] ],
                });
            }
            return $self;
        },
        pow => sub {
            # x^1 -> x
            if ($args->[1]->type eq 'integer' && $args->[1]->args->[0] eq '1') {
                return $args->[0];
            }
            # TODO: 0^x (x != 0), x^0 (x != 0)
            return $self;
        },
        rational => sub {
            if ($args->[1] eq '1') {
                # a/1 -> a
                return Axiom::Expr::Const->new({
                    type => 'integer',
                    args => [ $args->[0] ],
                });
            }
            return $self;
        }
    }->{$type};
    return $sub ? $sub->() : $self;
}

sub clean {
    my($self) = @_;
    return $self->copy->_clean;
}

sub str {
    my($self) = @_;
    sprintf '[%s %s]', $self->type,
            join ', ', map $_->str, @{ $self->args };
}

sub is_list { $listtype{ shift->type } }

sub locate {
    my($self, $location) = @_;
    return $self unless @$location;
    my $cur = $self;
    my $next;
    for my $i (0 .. $#$location) {
        $next = $cur->args->[$location->[$i] - 1];
        $cur = $next, next if defined $next && ref $next;
        die sprintf(
            "Invalid location: %s has only %s arguments for %s in %s\n",
            join('.', $i ? @$location[0 .. $i - 1] : 0),
            0 + @{ $cur->args },
            join('.', @$location),
            $self->str,
        );
    }
    return $cur;
}

sub copy {
    my($self) = @_;
    return $self->copy_with(sub { undef });
}

sub copy_with {
    my($self, $with) = @_;
    return $with->($self) // ref($self)->new({
        type => $self->type,
        args => [ map $_->copy_with($with), @{ $self->args } ],
    });
}

sub substitute {
    my($self, $location, $replace) = @_;
# FIXME: must introduce and re-bind any local variables in $replace
    return $replace unless @$location;
    my($off, @subloc) = @$location;
    my $args = $self->args;
    my @copy = map {
        $_ == $off - 1
            ? (@subloc
                ? $args->[$_]->substitute(\@subloc, $replace)
                : (($replace->is_list && $self->type eq $replace->type)
                    ? @{ $replace->args }
                    : $replace
                )
            )
            : $args->[$_]->copy
    } 0 .. $#$args;
    return ref($self)->new({ type => $self->type, args => \@copy });
}

sub subst_var {
    my($self, $var, $replace) = @_;
    my $vi = $var->binding->index;
    return $self->copy_with(sub {
        my($other) = @_;
        return $replace->copy if $other->type eq 'name'
                && $other->binding->index == $vi;
        return undef;
    });
}

sub parse {
    my($class, $dict, $text, $debug) = @_;
    local $DICT = $dict;
    if ($text =~ _parsere($debug)) {
        return $/{Relation};
    } else {
        die "No match: <$text>\n";
    }
}

sub diff {
    my($self, $other, $map) = @_;
    $map //= [];
    $self->type eq $other->type or return [];
    my($sa, $oa) = ($self->args, $other->args);
    @$sa == @$oa or return [];
    my $diff;
    for my $i (0 .. $#$sa) {
        my $_diff = $sa->[$i]->diff($oa->[$i], $map) // next;
        return [] if $diff;
        $diff = [ $i + 1, @{ $_diff } ];
    }
    return $diff;
}

package Axiom::Expr::Const {
    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        my $type = (@{ $hash->{args} } > 1 && $hash->{args}[1] != 1)
                ? 'rational' : 'integer';
        my $args = ($type eq 'rational')
                ? $hash->{args} : [ $hash->{args}[0] ];
        return bless { type => $type, args => $args }, $class;
    }
    sub const { 1 }
    sub atom { 1 }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // ref($self)->new({
            type => $self->type,
            args => [ @{ $self->args } ],
        });
    }
    sub str { join '/', @{ shift->args } }
    sub diff {
        my($self, $other, $map) = @_;
        my $type = $self->type;
        return [] unless $type eq $other->type;
        my $argc = { integer => 1, rational => 2 }->{$type}
                // die "I don't know how many args a $type has";
        my($sa, $oa) = ($self->args, $other->args);
        ($sa->[$_] == $oa->[$_]) or return []
                for (0 .. $argc - 1);
        return undef;
    }
};

package Axiom::Expr::Name {
    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        return bless { type => 'name', args => $hash->{args} }, $class;
    }
    sub atom { 1 }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // do {
            my $other = ref($self)->new({
                type => $self->type,
                args => [ @{ $self->args } ],
            });
            $other->bind($self->binding);
            $other;
        };
    }
    sub str {
        my($self) = @_;
        return sprintf '%s %s', $self->bindtype, $self->name;
    }
    sub diff {
        my($self, $other, $map) = @_;
        return [] unless $self->type eq $other->type
                && $self->bindtype eq $other->bindtype
# FIXME: use the map
                && $self->name eq $other->name;
        return undef;
    }
    sub name { shift->args->[0] }
    sub bind {
        my($self, $binding) = @_;
        $self->{binding} = $binding;
        return;
    }
    sub binding { shift->{binding} }
    sub bindtype { shift->binding->type }
};

package Axiom::Expr::Iter {
    our @ISA = qw{Axiom::Expr};
    sub iter { 1 }
    sub range {
        my($self) = @_;
        my($from, $to) = @{ $self->args }[1, 2];
        my $diff = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $to->copy,
                Axiom::Expr->new({
                    type => 'negate',
                    args => [ $from->copy ],
                }),
            ],
        })->clean;
        die sprintf(
            "Cannot expand non-constant range: %s .. %s is not constant\n",
            $from->{''}, $to->{''},
        ) unless $diff->const;
        return [ map Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $from->copy,
                Axiom::Expr::Const->new({
                    type => 'integer',
                    args => [ "$_" ],
                }),
            ],
        }), 0 .. $diff->args->[0] ];
    }
    sub value_at {
        my($self, $expr) = @_;
        my($var, $targ) = @{ $self->args }[0, 3];
        return $targ->subst_var($var, $expr);
    }
};

sub _grammar {
    use Regexp::Grammars;
    state $grammar = qr{
        <grammar: Axiom::Expr>
        <nocontext:>
        <debug: same>
        <objrule: Axiom::Expr=Relation>
            (?:
                \( <[args=Relation]> \) <.ImpliesToken> \( <[args=Relation]> \)
                <type=(?{ 'implies' })>
            |
                <[args=Expr]> <.EqualsToken> <[args=Expr]>
                <type=(?{ 'equals' })>
            )
        <objrule: Axiom::Expr=Expr>
            <[args=PlusList]>
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=PlusList>
            <[args=SignedAtom]>+ % <.PlusSeparator> <!SignToken>
            <type=(?{ 'pluslist' })>
        <objrule: Axiom::Expr=SignedAtom>
            (?: <ws> <[Sign=SignToken]> )* <[args=MulList]>
            <type=(?{
                my $count = grep $_ = '-', @{ $MATCH{Sign} // [] };
                ($count % 2) ? 'negate' : 'nothing';
            })>
        <objrule: Axiom::Expr=MulList>
            (?: 1 (?= <.DivideToken> ) | <[args=Cuddled]> )
            (?:
                <.MultiplyToken>
                (?: 1 (?= <.DivideToken> ) | <[args=Cuddled]> )
            )* <!MultiplyToken>
            <args=(?{ [ map @{ $_->args }, @{ $MATCH{args} } ] })>
            (?: <.DivideToken> <[args=Recip]> )* <!DivideToken>
            <type=(?{ 'mullist' })>
        <objrule: Axiom::Expr=Cuddled>
            (?:
                <[args=PowExpr]>+ <[args=BarePowExpr]>?
            |
                <[args=BarePowExpr]>
            ) (?! \w )
            <type=(?{ 'cuddled' })>
        <objrule: Axiom::Expr=Recip>
            (?: <[args=PowExpr]> | <[args=BarePowExpr]> )
            (?! \w ) <!MultiplyToken>
            <type=(?{ 'recip' })>
        <objrule: Axiom::Expr=BarePowExpr>
            <[args=Factorial]> <.PowerToken> <[args=Factorial]> (?! \w )
            <type=(?{ 'pow' })>
        <objrule: Axiom::Expr=PowExpr>
            <[args=Factorial]> (?: <.PowerToken> <[args=BraceExpr]> )?
            <!PowerToken>
            <type=(?{ @{ $MATCH{args} } > 1 ? 'pow' : 'nothing' })>
        <objrule: Axiom::Expr=Factorial>
#FIXME
            <[args=Atom]> <[FactorialToken]>* <!FactorialToken>
            (?{
                my $count = @{ $MATCH{FactorialToken} // [] };
                if ($count) {
                    push @{ $MATCH{args} }, $count;
                    $MATCH{type} = 'factorial';
                } else {
                    $MATCH{type} = 'nothing';
                }
            })
        <objrule: Axiom::Expr=BraceExpr>
            \{ <[args=Expr]> \}
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=Atom>
            (?:
                <[args=Integer]>
                | <[args=Function]>
                | <[args=Variable]>
                | <[args=Sum]>
                | <[args=ParenExpr]>
            )
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=ParenExpr>
            \( <[args=Expr]> \)
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=Function>
            <FuncName> \( <[args=ArgList]> \)
            (?{
                $MATCH{args} = [ $MATCH{FuncName},
                        map @{ $_->{args} }, @{ $MATCH{args} } ];
            })
            <type=(?{ 'function' })>
        <objrule: Axiom::Expr::Iter=Sum>
            <.SumToken> <[args=SumStart]> <[args=SumEnd]>
            (?{
                # split SumStart into variable and start value, extract SumEnd
                splice @{ $MATCH{args} }, 0, 1, @{ $MATCH{args}[0]{args} };
                $MATCH{args}[2] = $MATCH{args}[2]{args}[0];

                # introduce the local variable into the dictionary for the
                # duration of the subexpression
                my $var = $MATCH{args}[0];
                local $Axiom::Expr::DICT->dict->{$var->name} = $var->binding;
            })
            <[args=BraceExpr]>
            (?{
                my $var = $MATCH{args}[0];
                local $Axiom::Expr::DICT->dict->{$var->name} = undef;
            })
            <type=(?{ 'sum' })>

        <rule: ArgList>
            <[args=Expr]>+ % <.CommaToken>
        <rule: SumStart>
            _ \{ <[args=AssignExpr]> \}
            (?{ $MATCH = { args => $MATCH{args}[0]{args} } })
        <rule: AssignExpr>
            <[args=NewVariable]> <.AssignToken> <[args=Expr]>
        <rule: SumEnd>
            <.PowerToken> (?:
                \{ <[args=Expr]> \}
                | <[args=Atom]>
            )

        <rule: FuncName>
            <[args=Name]> (??{
                my $name = $MATCH{args}[0];
                my $func = $Axiom::Expr::DICT->lookup($name->name);
                if ($func && $func->type eq 'func') {
                    $name->bind($func);
                    $MATCH = $name;
                    $Axiom::Expr::SUCCEED;
                } else {
                    $Axiom::Expr::FAIL;
                }
            })
        <rule: Variable>
            <[args=Name]> (??{
                my $name = $MATCH{args}[0];
                my $var = $Axiom::Expr::DICT->lookup($name->name);
                if ($var && ($var->type eq 'var' || $var->type eq 'local')) {
                    $name->bind($var);
                    $MATCH = $name;
                    $Axiom::Expr::SUCCEED;
                } else {
                    $Axiom::Expr::FAIL;
                }
            })
        <rule: NewVariable>
            <[args=Name]> (??{
                my $name = $MATCH{args}[0];
                my $var = $Axiom::Expr::DICT->lookup($name->name);
                if ($var) {
                    $Axiom::Expr::FAIL;
                } else {
                    $var = $Axiom::Expr::DICT->introduce($name->name);
                    $name->bind($var);
                    $MATCH = $name;
                    $Axiom::Expr::SUCCEED;
                }
            })

        <objtoken: Axiom::Expr::Name>
            <[args=(?: [a-zA-Z] (?: _ (?: \d \b ) )? )]>
            <type=(?{ 'name' })>
        <objtoken: Axiom::Expr::Const=Integer>
            <[args=(?: \d+ (?! \d ) )]>
            <type=(?{ 'integer' })>

        <token: ImpliesToken> ->
        <token: EqualsToken> =
        <token: PlusSeparator> <PlusToken> | <?MinusToken>
        <token: SignToken> <Sign=PlusToken> | <Sign=MinusToken>
            (?{ $MATCH = $MATCH{Sign} })
        <token: PlusToken> \+
        <token: MinusToken> \-
        # should this be \\sol ?
        <token: DivideToken> /
        # should this be \\middot ?
        <token: MultiplyToken> \.
        <token: PowerToken> \^
        <token: FactorialToken> !
        <token: CommaToken> ,
        <token: SumToken> \\sum
        (?# Assign and Equals are ambiguous, I think that is ok )
        <token: AssignToken> =
        <token: ws> \s*+
    }x;
    return;
}
BEGIN { _grammar() }

sub _parsere {
    my($debug) = @_;

    use Regexp::Grammars;
    return $debug
        ? (state $dsre = qr{
            <extends: Axiom::Expr>
            <debug: match>
            ^ <Relation> \z
        }x)
        : (state $sre = qr{
            <extends: Axiom::Expr>
            ^ <Relation> \z
        }x);
}

1;
