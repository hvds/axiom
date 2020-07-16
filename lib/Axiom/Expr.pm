package Axiom::Expr;

use v5.10;
use strict;
use warnings;

use Math::BigRat;
use List::Util ();
use Carp qw{ confess };

our $SUCCEED = qr{(?=)};
our $FAIL = qr{(?!)};
our $DICT;

my %listtype = map +($_ => 1), qw{ pluslist mullist };

my %classtype = (
    (map +($_ => 'Axiom::Expr::Const'), qw{ integer rational }),
    (map +($_ => 'Axiom::Expr::Name'), qw{ name }),
    (map +($_ => 'Axiom::Expr::Iter'), qw{ sum prod }),
    (map +($_ => 'Axiom::Expr::Quant'), qw{ forall exists }),
);

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
    my $targclass = $classtype{$type} // 'Axiom::Expr';
    $class = $targclass unless $class->isa($targclass);
    return bless {
        type => $type,
        args => $args,
    }, $class;
}

sub local_dict {
    my($class, $localdict) = @_;
    return Axiom::Expr::LocalDict->new($localdict);
}

sub args { shift->{args} }
sub type { shift->{type} }
sub rawexpr {
    my($self) = @_;
    # FIXME: better serialization for unparsed objects
    return $self->{''} // $self->str;
}

sub is_atom { 0 }
sub is_const { 0 }
sub is_iter { 0 }
sub is_quant { 0 }
sub is_list { $listtype{ shift->type } }
sub has_newvar { 0 }

sub is_neg {
    my($self) = @_;
    my $type = $self->type;
    return $type eq 'negate' || (
        $type eq 'mullist' && $self->args->[0]->is_neg
    );
}
sub negate {
    my($self) = @_;
    my $type = $self->type;
    if ($type eq 'negate') {
        return $self->args->[0]->copy;
    } elsif ($type eq 'mullist') {
        my $other = $self->copy;
        $other->args->[0] = $other->args->[0]->negate;
        return $other;
    }
    return Axiom::Expr->new({
        type => 'negate',
        args => [ $self->copy ],
    });
}
sub recip {
    my($self) = @_;
    my $type = $self->type;
    if ($type eq 'recip') {
        return $self->args->[0]->copy;
    }
    return Axiom::Expr->new({
        type => 'recip',
        args => [ $self->copy ],
    });
}

sub _clean {
    my($self) = @_;
    return undef if $self->is_atom;
    my $type = $self->type;
    my $args = $self->args;
    for (@$args) {
        my $new = $_->_clean // next;
        $_ = $new;
        redo;
    }
    my $sub = {
        equals => undef,
        function => undef,
        expr => sub { return $self->args->[0] },
        braceexpr => sub { return $self->args->[0] },
        parenexpr => sub { return $self->args->[0] },
        forall => sub {
            my($var, $child) = @$args;
            if ($child->type eq 'forall'
                && $var->name gt $child->args->[0]->name
            ) {
                # \b \a x -> \a \b x
                return Axiom::Expr->new({
                    type => 'forall',
                    args => [
                        $child->args->[0]->copy,
                        Axiom::Expr->new({
                            type => 'forall',
                            args => [
                                $var->copy,
                                $child->args->[1]->copy,
                            ],
                        }),
                    ],
                });
            }
            return undef;
        },
        pluslist => sub {
            # +(null) -> 0
            return Axiom::Expr->new({
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
                    return $self;
                }
                if ($arg->is_const) {
                    if ($arg->args->[0] eq '0') {
                        # +(a, 0, b) -> +(a, b)
                        splice @$args, $i, 1;
                        return $self;
                    }
                    push @const, $i;
                }
            }

            if (@const > 1) {
                # +(a, c1, b, c2) -> +(a, eval(c1+c2), b)
                my $sum = Math::BigRat->new(0);
                $sum += $_->rat for @$args[@const];
                my $repl = ($sum == 0)
                    ? undef
                    : Axiom::Expr::Const->new_rat($sum);
                splice(@$args, $_, 1) for reverse @const;
                splice(@$args, $const[0], 0, $repl) if $repl;
                return $self;
            }

            my(@con, @plus, @minus) = ();
            for (0 .. $#$args) {
                push @{
                    $args->[$_]->is_const ? \@con
                    : $args->[$_]->is_neg ? \@minus : \@plus
                }, $_;
            }

            if (@plus && @minus) {
                for my $m (@minus) {
                    my $nm = $args->[$m]->negate;
                    for my $p (@plus) {
                        next if $nm->diff($args->[$p]);
                        # +(a, b, c, -b) -> +(a, c)
                        for (sort { $b <=> $a } $m, $p) {
                            splice @$args, $_, 1;
                        }
                        return $self;
                    }
                }
            }

            # This should probably change
            # +(-a, b, -const) -> +(b, -const, -a)
            # +(-a, b, const) -> +(const, b, -a)
            my @order = (@con && $args->[$con[0]]->args->[0] =~ /^-/)
                ? (@plus, @con, @minus)
                : (@con, @plus, @minus);
            if (grep $order[$_] > $order[$_ + 1], 0 .. @order - 2) {
                @$args = @$args[@order];
                return $self;
            }
            return undef;
        },
        negate => sub {
            my $arg = $args->[0];
            # -(-(a)) -> a
            return $arg->args->[0] if $arg->type eq 'negate';

            # -(const) -> eval(-const)
            return $arg->negate if $arg->is_const;

            # -(a - b) -> b - a
            return Axiom::Expr->new({
                type => 'pluslist',
                args => [ map $_->negate, @{ $arg->args } ],
            }) if $arg->type eq 'pluslist';

            # -(a.b) -> (-a).b
            if ($arg->type eq 'mullist') {
                $arg->args->[0] = $arg->args->[0]->negate;
                return $arg;
            }

            # -x -> (-1 . x)
            return Axiom::Expr->new({
                type => 'mullist',
                args => [
                    Axiom::Expr->new({ type => 'integer', args => [ '-1' ] }),
                    $arg,
                ],
            });
        },
        mullist => sub {
            # x(null) -> 1
            return Axiom::Expr->new({
                type => 'integer',
                args => [ '1' ],
            }) if @$args == 0;

            # x(a) -> a
            return $args->[0] if @$args == 1;

            my(@const, @neg) = ();
            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                if ($arg->type eq 'mullist') {
                    # x(a, x(b, c), d) -> x(a, b, c, d)
                    splice @$args, $i, 1, @{ $arg->args };
                    return $self;
                }
                if ($arg->is_const) {
                    if ($arg->args->[0] eq '0') {
                        # x(a, 0, b) -> 0
                        return $arg;
                    }
                    if ($arg->type eq 'integer' && $arg->args->[0] eq '1') {
                        # x(a, 1, b) -> x(a, b)
                        splice @$args, $i, 1;
                        return $self;
                    }
                    push @const, $i;
                } elsif ($arg->is_neg) {
                    push @neg, $i;
                }
            }

            if (@const > 1) {
                my $prod = Math::BigRat->new(1);
                $prod *= $_->rat for @$args[@const];
                my $repl = ($prod == 1)
                    ? undef
                    : Axiom::Expr::Const->new_rat($prod);
                # x(a, c1, b, c2) -> x(a, eval(c1 . c2), b)
                splice(@$args, $_, 1) for reverse @const;
                splice(@$args, $const[0], 0, $repl) if $repl;
                return $self;
            } elsif (@const == 1) {
                my $rat = $args->[ $const[0] ]->rat;
                if ($rat == 1) {
                    # a.1.b -> a.b
                    splice @$args, $const[0], 1;
                    return $self;
                }
            }

            if (@neg) {
                # 3.(-a).(-b).(-c) -> (-3)abc
                # (-a).b -> (-1).ab
                $args->[$_] = $args->[$_]->negate for @neg;
                if (@neg & 1) {
                    unless (@const) {
                        unshift @$args, Axiom::Expr::Const->new_rat(
                            Math::BigRat->new('1')
                        );
                        @const = (0);
                    }
                    $args->[ $const[0] ] = $args->[ $const[0] ]->negate;
                }
                return $self;
            }

            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                next unless $arg->type eq 'pluslist';
                splice @$args, $i, 1;
                # x(a, b+c, d) -> +(abd, acd)
                return Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ map Axiom::Expr->new({
                        type => 'mullist',
                        args => [ $_, @$args ],
                    }), @{ $arg->{args} } ],
                });
            }

            for my $d (0 .. $#$args - 1) {
                my $dr = $args->[$d]->recip;
                for my $m ($d + 1 .. $#$args) {
                    if (!$dr->diff($args->[$m])) {
                        # x(a, b, c, 1/b) -> x(a, c)
                        for (sort { $b <=> $a } $d, $m) {
                            splice @$args, $_, 1;
                        }
                        return $self;
                    }
                }
            }

            my(@con, @mul, @pow, @div) = ();
            for (0 .. $#$args) {
                push @{
                    $args->[$_]->is_const ? \@con
                    : $args->[$_]->type eq 'pow' ? \@pow
                    : $args->[$_]->type eq 'recip' ? \@div : \@mul
                }, $_;
            }
            # Not sure what we want here
            # x(a, const p/q, 1/b, c, 1/d) -> x(const p/q, a, c, 1/b, 1/d)
            my @order = (@con, @mul, @pow, @div);
            my $changed = grep { $order[$_] > $order[$_ + 1] } 0 .. @order - 2;
            @$args = @$args[@order] if $changed;

            return $changed ? $self : undef;
        },
        recip => sub {
            my $arg = $args->[0];
            # 1/(1/x) -> x (FIXME: x=0?)
            return $arg->args->[0] if $arg->type eq 'recip';

            # 1/(p/q) -> q/p
            return Axiom::Expr::Const->new_rat(1 / $arg->rat) if $arg->is_const;

            # 1/(a.b) -> 1/a . 1/b
            return Axiom::Expr->new({
                type => 'mullist',
                args => [ map Axiom::Expr->new({
                    type => 'recip',
                    args => [ $_ ],
                }), @{ $arg->args } ],
            }) if $arg->type eq 'mullist';

            # 1/(a^b) -> (1/a)^b
            return Axiom::Expr->new({
                type => 'pow',
                args => [
                    Axiom::Expr->new({
                        type => 'recip',
                        args => [ $arg->args->[0]->copy ],
                    }),
                    $arg->args->[1]->copy,
                ],
            }) if $arg->type eq 'pow';

            return undef;
        },
        pow => sub {
            my($val, $pow) = @{ $args };
            # x^1 -> x
            if ($pow->type eq 'integer') {
                return $val if $pow->args->[0] eq '1';
                return Axiom::Expr::Const->new_rat(
                    $val->rat ** $pow->args->[0]
                ) if $val->is_const;
            }

            # pow(a, b+c) -> pow(a, b) x pow(a, c)
            return Axiom::Expr->new({
                type => 'mullist',
                args => [
                    map Axiom::Expr->new({
                        type => 'pow',
                        args => [ $val->copy, $_ ],
                    })->clean, @{ $pow->{args} }
                ],
            }) if $pow->type eq 'pluslist';

            # pow(a, -b) -> 1 / pow(a, b)
            return Axiom::Expr->new({
                type => 'recip',
                args => [ Axiom::Expr->new({
                    type => 'pow',
                    args => [ $val->copy, $pow->negate ],
                }) ],
            }) if $pow->is_neg;

            # TODO: 0^x (x != 0), x^0 (x != 0)
            return undef;
        },
    }->{$type};
    return $sub ? $sub->() : undef;
}

sub _clean_copied {
    my($self) = @_;
    while (1) {
        my $new = $self->_clean // return $self;
        $self = $new;
    }
}

sub clean {
    my($self) = @_;
    return $self->copy->_clean_copied;
}

sub str {
    my($self) = @_;
    sprintf '[%s %s]', $self->type,
            join ', ', map $_->str, @{ $self->args };
}

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

sub common_loc {
    my($self, $vi) = @_;
    my @all;
    $self->walk_locn(sub {
        my($expr, $loc) = @_;
        push @all, $loc if $expr->type eq 'name'
                && !$expr->binding->is_func
                && $expr->binding->id == $vi;
    });
    die "Variable index $vi not found in expr @{[ $self->str ]}" unless @all;
    return List::Util::reduce(sub {
        my @new;
        while (@$a && @$b) {
            my $la = shift @$a;
            my $lb = shift @$b;
            last if $la != $lb;
            push @new, $la;
        }
        [@new];
    }, @all);
}

sub dict_at {
    my($self, $loc) = @_;
    my $dict = $self->{dict}->clone;
    return $self->_dict_at($dict, [ @$loc ]);
}

sub _dict_at {
    my($self, $dict, $loc) = @_;
    return $dict unless @$loc;
    my $this = shift(@$loc) - 1;
    return $self->args->[$this]->_dict_at($dict, $loc);
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
    my $vi;
    if ($var->binding) {
        $vi = $var->binding->id;
    } else {
        confess("var @{[ $var->name ]} is unbound\n");
    }
    return $self->subst_vars({ $vi => $replace });
}

sub subst_vars {
    my($self, $map) = @_;
    return $self->copy_with(sub {
        my($other) = @_;
        return undef unless $other->type eq 'name';
        my $oi = $other->binding->id;
        return undef unless $map->{$oi};
        return $map->{$oi}->copy;
    });
}

sub walk_tree {
    my($self, $cb) = @_;
    $cb->($self);
    unless ($self->is_atom) {
        $_->walk_tree($cb) for @{ $self->args };
    }
    return;
}

sub walk_locn {
    my($self, $cb, $loc) = @_;
    $loc //= [];
    $cb->($self, $loc);
    unless ($self->is_atom) {
        my $args = $self->args;
        for my $i (0 .. $#$args) {
            $args->[$i]->walk_locn($cb, [ @$loc, $i + 1 ]);
        }
    }
    return;
}

sub is_independent {
    my($self, $var) = @_;
    my $id = $var->binding->id;
    my $seen = 0;
    $self->clean->walk_tree(sub {
        my($this) = @_;
        $seen ||= $this->type eq 'name' && $this->binding->id == $id;
    });
    return $seen ? 0 : 1;
}

sub parse {
    my($class, $dict, $text, $debug) = @_;
    my $local = $class->local_dict($dict);
    if ($text =~ _parsere($debug)) {
        return $/{Relation};
    } else {
        die "No match: <$text>\n";
    }
}

sub _diff {
    my($self, $other, $map) = @_;
    $map //= [];
    $self->type eq $other->type or return [];
    my($sa, $oa) = ($self->args, $other->args);
    @$sa == @$oa or return [];
    my $diff;
    if ($self->is_list) {
        my @sd = map {
            my $this_diff = $sa->[$_]->_diff($oa->[$_], $map);
            $this_diff ? [ $_, $this_diff ] : ();
        } 0 .. $#$sa;
        if (@sd > 1) {
            my @od = @sd;
          DiffListPair:
            for (my $si = 0; $si < @sd; ++$si) {
                my $s = $sa->[$sd[$si][0]];
                for (my $oi = 0; $oi < @od; ++$oi) {
                    next if $s->_diff($oa->[$od[$oi][0]]);
                    splice @sd, $si, 1;
                    splice @od, $oi, 1;
                    last DiffListPair if $si >= @sd;
                    redo DiffListPair;
                }
            }
            return undef unless @sd;
            return [] if $sd[0][0] != $od[0][0];
        }
        return [] if @sd > 1;
        $diff = [ $sd[0][0] + 1, @{ $sd[0][1] } ]
                if @sd;
    } else {
        for my $i (0 .. $#$sa) {
            my $_diff = $sa->[$i]->_diff($oa->[$i], $map) // next;
            return [] if $diff;
            $diff = [ $i + 1, @{ $_diff } ];
        }
    }
    return $diff;
}

sub diff {
    my($self, $other, $map) = @_;
    my $where = $self->_diff($other, $map);
    return undef unless $where;
    return undef unless $self->clean->_diff($other->clean, $map);
    return $where;
}

sub find_expr {
    my($self, $expr) = @_;
    return [] if !$self->_diff($expr);
    return undef if $self->is_atom;
    my $args = $self->args;
    for my $i (0 .. $#$args) {
        my $loc = $args->[$i]->find_expr($expr);
        return [ $i, @$loc ] if $loc;
    }
    return undef;
}

sub _resolve {
    my($self, $dict) = @_;
    $_->_resolve($dict) for @{ $self->args };
    return;
}

sub resolve {
    my($self, $dict) = @_;
    $dict = $dict->clone;   # not copy, must preserve ids
    $self->{dict} = $dict;  # store at top level of expr only
    $self->_resolve($dict);
    return;
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
    sub new_rat {
        my($class, $rat) = @_;
        return $class->new({ args => [ $rat->parts ] });
    }
    sub is_const { 1 }
    sub is_atom { 1 }
    sub is_neg { shift->args->[0] < 0 }
    sub negate {
        my($self) = @_;
        my $other = $self->copy;
        $other->args->[0] = -$other->args->[0];
        return $other;
    }
    sub recip {
        my($self) = @_;
        return Axiom::Expr::Const->new_rat(1 / $self->rat);
    }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // ref($self)->new({
            type => $self->type,
            args => [ @{ $self->args } ],
        });
    }
    sub str { join '/', @{ shift->args } }
    sub rat {
        my($self) = @_;
        my $args = $self->args;
        use Math::BigRat;
        return Math::BigRat->new(
            $args->[0], $self->type eq 'integer' ? '1' : $args->[1],
        );
    }
    sub _diff {
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
    sub _resolve { }
};

package Axiom::Expr::Name {
    use Carp qw{ confess };

    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        return bless { type => 'name', args => $hash->{args} }, $class;
    }
    sub is_atom { 1 }
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
        return sprintf '%s %s%s', $self->bindtype, $self->name,
                $self->binding ? "_" . $self->binding->id : "";
    }
    sub _diff {
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
    sub bindtype {
        my($self) = @_;
        my $binding = $self->binding;
        confess("var ", $self->name, " is unbound") unless $binding;
        return $binding->type;
    }
    sub _resolve {
        my($self, $dict) = @_;
        my $binding = $self->binding;
        return if $binding && $binding->is_func;

        $binding = $dict->lookup($self->name) or confess sprintf(
            "Cannot resolve var %s, not in dictionary\n",
            $self->name,
        );
        $binding->is_func and die sprintf(
            "Cannot resolve var %s, is reserved as function name\n",
            $self->name,
        );
        $self->bind($binding);
        return;
    }
    sub _resolve_new {
        my($self, $dict) = @_;
        my $binding = $dict->introduce($self->name);
        $self->bind($binding);
        return $binding;
    }
};

package Axiom::Expr::Iter {
    our @ISA = qw{Axiom::Expr};
    sub is_iter { 1 }
    sub has_newvar { 1 }
    sub intro_newvar { 0 }
    sub affect_newvar { 3 }
    sub range {
        my($self) = @_;
        my($from, $to) = @{ $self->args }[1, 2];
        my $diff = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $to->copy,
                $from->negate,
            ],
        })->clean;
        die sprintf(
            "Cannot expand non-constant range: %s .. %s is not constant\n",
            $from->rawexpr, $to->rawexpr,
        ) unless $diff->is_const;
        return [ map Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $from->copy,
                Axiom::Expr->new({
                    type => 'integer',
                    args => [ "$_" ],
                }),
            ],
        }), 0 .. $diff->args->[0] ];
    }
    sub value_at {
        my($self, $expr) = @_;
# FIXME: expr may have variables that need resolving/checking
        my($var, $targ) = @{ $self->args }[0, 3];
        return $targ->subst_var($var, $expr);
    }
    sub _resolve {
        my($self, $dict) = @_;
        my($var, $from, $to, $expr) = @{ $self->args };
        my $bind = $var->_resolve_new($dict);
        $_->_resolve($dict) for ($from, $to);
        my $local = $dict->local_name($var->name, $bind);
        $expr->_resolve($dict);
        return;
    }
    sub _dict_at {
        my($self, $dict, $loc) = @_;
        return $dict unless @$loc;
        my $this = shift(@$loc) - 1;
        my $result = $self->args->[$this]->_dict_at($dict, $loc);
        if ($this == 3) {
            my $var = $self->args->[0];
            $result->dict->{$var->name} = $var->binding;
        }
        return $result;
    }
};

package Axiom::Expr::Quant {
    our @ISA = qw{Axiom::Expr};
    sub is_quant { 1 }
    sub has_newvar { 1 }
    sub intro_newvar { 0 }
    sub affect_newvar { 1 }
    sub _resolve {
        my($self, $dict) = @_;
        my($var, $expr) = @{ $self->args };
        my $bind = $var->_resolve_new($dict);
        my $local = $dict->local_name($var->name, $bind);
        $expr->_resolve($dict);
        return;
    }
    sub _dict_at {
        my($self, $dict, $loc) = @_;
        return $dict unless @$loc;
        my $this = shift(@$loc) - 1;
        my $result = $self->args->[$this]->_dict_at($dict, $loc);
        if ($this == 1) {
            my $var = $self->args->[0];
            $result->dict->{$var->name} = $var->binding;
        }
        return $result;
    }
};

sub _grammar {
    use Regexp::Grammars;
    state $grammar = qr{
        <grammar: Axiom::Expr>
        <debug: same>
        <objrule: Axiom::Expr=Relation>
            (?:
                <.OpenParen> <[args=Relation]> <.CloseParen>
                <.ImpliesToken>
                <.OpenParen> <[args=Relation]> <.CloseParen>
                <type=(?{ 'implies' })>
            |
                <[args=Expr]> <.EqualsToken> <[args=Expr]>
                <type=(?{ 'equals' })>
            |
                <.ForallToken> <[args=Variable]> : <[args=Relation]>
                <type=(?{ 'forall' })>
            |
                <.ExistsToken> <[args=Variable]> : <[args=Relation]>
                <type=(?{ 'exists' })>
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
            <.OpenBrace> <[args=Expr]> <.CloseBrace>
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
            <.OpenParen> <[args=Expr]> <.CloseParen>
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=Function>
            <FuncName> \( <[args=ArgList]> \)
            (?{
                $MATCH{args} = [ $MATCH{FuncName},
                        map @{ $_->{args} }, @{ $MATCH{args} } ];
            })
            <type=(?{ 'function' })>
        <objrule: Axiom::Expr=Sum>
            <.SumToken> <[args=SumStart]> <[args=SumEnd]> <[args=BraceExpr]>
            (?{
                # split SumStart into variable and start value, extract SumEnd
                splice @{ $MATCH{args} }, 0, 1, @{ $MATCH{args}[0]{args} };
                $MATCH{args}[2] = $MATCH{args}[2]{args}[0];
            })
            <type=(?{ 'sum' })>

        <rule: ArgList>
            <[args=Expr]>+ % <.CommaToken>
        <rule: SumStart>
            _ \{ <[args=AssignExpr]> \}
            (?{ $MATCH = { args => $MATCH{args}[0]{args} } })
        <rule: AssignExpr>
            <[args=Variable]> <.AssignToken> <[args=Expr]>
        <rule: SumEnd>
            <.PowerToken> (?:
                \{ <[args=Expr]> \}
                | <[args=Atom]>
            )
        <rule: RemapExpr>
            <[args=Variable]> <.BindToken> <[args=Expr]>
        <rule: FuncName>
            <[args=Name]> (??{
                my $name = $MATCH{args}[0];
                my $func = $Axiom::Expr::DICT->lookup($name->name);
                if ($func && $func->is_func) {
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
                if ($var && $var->is_func) {
                    $Axiom::Expr::FAIL;
                } else {
                    $MATCH = $name;
                    $Axiom::Expr::SUCCEED;
                }
            })

        <objtoken: Axiom::Expr=Name>
            <[args=(?: [a-zA-Z] (?: _ (?: \d \b ) )? )]>
            <type=(?{ 'name' })>
        <objtoken: Axiom::Expr=Integer>
            <[args=(?: \d+ (?! \d ) )]>
            <type=(?{ 'integer' })>

        <token: OpenParen> \(
        <token: CloseParen> \)
        <token: OpenBrace> \{
        <token: CloseBrace> \}
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
        <token: ForallToken> \\A | \\forall
        <token: ExistsToken> \\E | \\exists
        (?# Assign and Equals are ambiguous, I think that is ok )
        <token: AssignToken> =
        <token: BindToken> :=
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

package Axiom::Expr::LocalDict {
    sub new {
        my($class, $dict) = @_;
        my $old = $Axiom::Expr::DICT;
        my $restore = sub { $Axiom::Expr::DICT = $old };
        my $self = bless \$restore, $class;
        $Axiom::Expr::DICT = $dict;
        return $self;
    }
    DESTROY {
        my($self) = @_;
        $$self->();
    }
};

1;
