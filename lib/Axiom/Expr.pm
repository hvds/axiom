package Axiom::Expr;

use v5.10;
use strict;
use warnings;

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

sub clean {
    my($self) = @_;
    return if $self->atom;
    my $prev = 0;
    my $args = $self->args;
    while (1) {
        my $improve = $prev;
        for (0 .. $#$args) {
            my $new = $args->[$_]->clean or next;
            $args->[$_] = $new;
            ++$improve;
        }
        last if $improve == $prev;
        $prev = $improve;
    }

    my $type = $self->type;
    my $sub = {
        equals => undef,
        function => undef,
        expr => sub { return $self->args->[0] },
        braceexpr => sub { return $self->args->[0] },
        parenexpr => sub { return $self->args->[0] },
        pluslist => sub {
            my $changed = 0;
          retry_pluslist:
            return Axiom::Expr::Const->new({
                type => 'integer',
                args => [ '0' ],
            }) if @$args == 0;
            return $args->[0] if @$args == 1;
            for (0 .. $#$args) {
                my $arg = $args->[$_];
                if ($arg->type eq 'pluslist') {
                    splice @$args, $_, 1, @{ $arg->args };
                    $changed = 1;
                    goto retry_pluslist if @$args < 2;
                    redo;
                }
                if ($arg->type eq 'integer' && $arg->args->[0] eq '0') {
                    splice @$args, $_, 1;
                    $changed = 1;
                    goto retry_pluslist if @$args < 2;
                    redo;
                }
            }
            my(@plus, @minus) = ();
            for (0 .. $#$args) {
                push @{$args->[$_]->type eq 'negate' ? \@minus : \@plus}, $_;
            }
            for my $m (@minus) {
                my $me = $args->[$m]->args->[0];
                for my $p (@plus) {
                    next if $me->diff($args->[$p]);
                    for (sort { $b <=> $a } $m, $p) {
                        splice @$args, $_, 1;
                    }
                    $changed = 1;
                    goto retry_pluslist;
                }
            }
            if (@plus && @minus && $minus[0] < $plus[-1]) {
                @$args = @$args[@plus, @minus];
                $changed = 1;
            }
            return $changed ? $self : undef;
        },
        negate => sub {
            if ($args->[0]->type eq 'negate') {
                return $args->[0]->args->[0];
            }
            if ($args->[0]->type eq 'integer' && $args->[0]->args->[0] eq '0') {
                return $args->[0];
            }
            return undef;
        },
        mullist => sub {
            my $changed = 0;
          retry_mullist:
            return Axiom::Expr::Const->new({
                type => 'integer',
                args => [ '1' ],
            }) if @$args == 0;
            return $args->[0] if @$args == 1;
            for (0 .. $#$args) {
                my $arg = $args->[$_];
                if ($arg->type eq 'mullist') {
                    splice @$args, $_, 1, @{ $arg->args };
                    $changed = 1;
                    goto retry_mullist if @$args < 2;
                    redo;
                }
                if ($arg->type eq 'integer' && $arg->args->[0] eq '1') {
                    splice @$args, $_, 1;
                    $changed = 1;
                    goto retry_mullist if @$args < 2;
                    redo;
                }
            }
            my(@mul, @div) = ();
            for (0 .. $#$args) {
                push @{$args->[$_]->type eq 'recip' ? \@div : \@mul}, $_;
            }
            for my $d (@div) {
                my $de = $args->[$d]->args->[0];
                for my $m (@mul) {
                    next if $de->diff($args->[$m]);
                    for (sort { $b <=> $a } $d, $m) {
                        splice @$args, $_, 1;
                    }
                    $changed = 1;
                    goto retry_mullist;
                }
            }
            if (@mul && @div && $div[0] < $mul[-1]) {
                @$args = @$args[@mul, @div];
                $changed = 1;
            }
            return $changed ? $self : undef;
        },
        recip => sub {
            if ($args->[0]->type eq 'recip') {
                return $args->[0]->args->[0];
            }
            if ($args->[0]->type eq 'integer' && $args->[0]->args->[0] eq '1') {
                return $args->[0];
            }
            return undef;
        },
        pow => sub {
            if ($args->[1]->type eq 'integer' && $args->[1]->args->[0] eq '1') {
                return $args->[0];
            }
            return undef;
        },
    }->{$type};
    return $sub && $sub->();
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
        $cur = $next, next if defined $next;
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
    return ref($self)->new({
        type => $self->type,
        args => [ map $_->copy, @{ $self->args } ],
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
        $diff = [ $i, @{ $_diff } ];
    }
    return $diff;
}

package Axiom::Expr::Const {
    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        return bless { type => 'integer', args => $hash->{args} }, $class;
    }
    sub atom { 1 }
    sub copy {
        my($self) = @_;
        return ref($self)->new({
            type => $self->type,
            args => [ @{ $self->args } ],
        });
    }
    sub str { sprintf '%s', shift->args->[0] }
    sub diff {
        my($self, $other, $map) = @_;
        return [ $self, $other ] unless $self->type eq $other->type
                && $self->args->[0] == $other->args->[0];
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
    sub copy {
        my($self) = @_;
        my $other = ref($self)->new({
            type => $self->type,
            args => [ @{ $self->args } ],
        });
        $other->bind($self->binding);
        return $other;
    }
    sub str {
        my($self) = @_;
        return sprintf '%s %s', $self->bindtype, $self->name;
    }
    sub diff {
        my($self, $other, $map) = @_;
        return [ $self, $other ] unless $self->type eq $other->type
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
        <objrule: Axiom::Expr=Sum>
            <.SumToken> <[args=SumStart]> <[args=SumEnd]>
            (?{
                # split the SumStart into variable and start value
                splice @{ $MATCH{args} }, 0, 1, @{ $MATCH{args}[0]{args} };
                my $var = $MATCH{args}[0];
                local $Axiom::Expr::DICT->dict->{$var->name} = $var->binding;
                1;    
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
