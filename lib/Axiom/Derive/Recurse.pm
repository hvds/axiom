package Axiom::Derive::Recurse;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Recurse - recursively apply a mapping equality

=head1 USAGE

  derive: recurse ( line? )
  rule: [ line, var, expr1, expr2 ]

Given a I<line> equating some function C<f> of I<var> to some function
of C<f> of I<expr1>, recursively evaluates the result of substituting the
same equality into the right hand side I<expr2> times.

More specifically: given C< f(x) = af(g(x)) + bh(x) + c >, we iteratively
replace C< af(g(x)) > with the equivalent evaluation of the whole RHS
C<n> times to give:
  f(x) = a^n f(g^n(x)) + sum_0^{n-1}{ a^i (bh(g^i(x)) + c) }

Eg given C< f(x) = f(x - 1) + 1 >, C< recurse(x := x - 1, x) > will construct
C< f(x) = f(0) + \sum_{i=0}^{x - 1}{ 1 } >.

TODO: currently supports I<expr1> only of the forms C< x := x + a >
and C< x := ax >; could handle C< x := ax + b >. Not sure if there are
more structures we need to support for the RHS.

FIXME: include the location at which to find f(expr1) in the rule args,
instead of deriving that in validate.

=cut

*_zero = \&Axiom::Derive::_zero;
*_one = \&Axiom::Derive::_one;

sub rulename { 'recurse' }

sub derivere { <<'RE' }
    <rule: recurse>
        recurse (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
RE

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);

    # Find the LHS and RHS of the underlying expression; for the LHS, find
    # locations of variables within it that are declared by an enfolding
    # "forall".
    my $loc = [];
    my(%id, @var);
    my $eq = $starting;
    while ($eq->type eq 'forall') {
        push @$loc, 2;
        (my($var), $eq) = @{ $eq->args };
        $id{$var->name} = $var->binding->id;
    }
    $eq->type eq 'equals' or die sprintf(
        "Don't know how to derive recurse over a %s\n", $eq->type,
    );
    my($lhs, $rhs) = @{ $eq->args };
    $lhs->walk_tree(sub {
        my($e) = @_;
        return unless $e->type eq 'name';
        my $name = $e->name;
        if (defined($id{$name}) && $e->binding->id == $id{$name}) {
            delete $id{$name};
            push @var, $e;
        }
        return;
    });

    # Now find mappings for any one of the variables found above that result
    # in a subexpression of the RHS.
    my @choice;
    $rhs->walk_tree(sub {
        my($e) = @_;
        for my $v (@var) {
            my $map = $self->find_mapping($lhs, $e, [ $v ]);
            push @choice, [ $v, $map->{$v->name} ] if $map;
        }
        return;
    });

    # Now similarly look for mappings that result in subexpressions of the RHS
    # of the target: any such that can represent a recursed form of one of
    # the mappings found above gives us a possibility to try.
    my $teq = $target;
    while ($teq->type eq 'forall') {
        $teq = $teq->args->[1];
    }
    $teq->type eq 'equals' or die sprintf(
        "Don't know how to derive recurse to give a %s\n", $teq->type,
    );
    my $trhs = $teq->args->[1];
    my @result;
    $trhs->walk_tree(sub {
        my($e) = @_;
        for my $v (@var) {
            # FIXME: left and right are from different expressions,
            # equivalent non-$v variables may not have the same id.
            my $map = $self->find_mapping($lhs, $e, [ $v ]);
            # FIXME: deduplicate
            push @result, [ $v, $map->{$v->name} ] if $map;
        }
        return;
    });

    my @vargs;
    my $try = sub {
        my($var, $map, $count) = @_;
        $var = $var->copy;
        $map = $map->copy;
        @vargs = ($line, $var, $map, $count);
        local $self->{working} = $self->working;
        return 0 unless eval { validate($self, \@vargs) };
        return 0 if $target->diff($self->working);
        return 1;
    };

    for (@choice) {
        my($var, $map) = @$_;

        # We only support x -> x + e and x -> x . e for now.
        my($plus, $times);
        $plus = _subv($map, $var);
        $plus = undef unless $plus->is_independent($var);
        if (!$plus) {
            $times = _divv($map, $var);
            unless ($times->is_independent($var)) {
                die sprintf(
                    "unable to resolve iterator '%s := %s' to derive recurse",
                    $var->str, $map->str,
                );
            }
        }

        for (@result) {
            my($tvar, $tmap) = @$_;
            next unless $var->name eq $tvar->name;
            if ($plus) {
                my $count = Axiom::Expr->new({
                    type => 'mullist',
                    args => [
                        _subv($tmap, $var),
                        $plus->recip,
                    ],
                })->clean;
                return \@vargs if $try->($var, $map, $count);
            } else {
                my $count = Axiom::Expr->new({
                    type => 'pow',
                    args => [
                        _divv($tmap, $var),
                        $times->recip,
                    ],
                })->clean;
                return \@vargs if $try->($var, $map, $count);
            }
        }
    }
    die "don't know how to derive this recurse";
}

sub validate {
    my($self, $args) = @_;
    my($line, $var, $iter, $count) = @$args;
    my $starting = $self->line($line)->copy;
    $starting->resolve($self->dict);
    my $source_dict = $starting->dict_at([]);

    my $loc = [];
    my $eq = $starting;
    while ($eq->is_quant) {
        push @$loc, 2;
        $eq = $eq->args->[1];
    }

    my $subdict = $starting->dict_at($loc);
    $_->resolve($subdict) for ($var, $iter, $count);

    # Given f(x) = af(g(x)) + bh(x) + c, we iteratively replace
    # af(g(x)) with the equivalent evaluation of the whole RHS
    # n times to give
    #  f(x) = a^n f(g^n(x)) + sum_0^{n-1}{ a^i (bh(g^i(x)) + c) }

    $eq->type eq 'equals' or die sprintf(
        "Don't know how to apply recurse over a %s\n", $eq->type,
    );
    my($lhs, $rhs) = @{ $eq->args };
    my $base_pow = _f_pow($var, $iter, $count) or die sprintf(
        "Don't know how to recurse iteration %s := %s\n",
        $var->name, $iter->rawexpr,
    );

    $lhs->is_independent($var) and die sprintf(
        "LHS of recurse expression is independent of %s\n", $var->name,
    );
    my $expect = $lhs->subst_var($var, $iter);
    my $rloc = $rhs->find_expr($expect) or die sprintf(
        "Unable to find %s in %s\n",
        $expect->str, $rhs->str,
    );
    my $prod = _one();
    my $cur;
    for (0 .. $#$rloc) {
        $cur = $_ ? $cur->args->[ $rloc->[$_ - 1] - 1 ] : $rhs;
        my $type = $cur->type;
        if ($type eq 'pluslist') {
            next;
        } elsif ($type eq 'negate') {
            $prod = $prod->negate;
            next;
        } elsif ($type eq 'mullist') {
            my $next_rloc = $rloc->[$_] - 1;
            my $args = $cur->args;
            $prod = Axiom::Expr->new({
                type => 'mullist',
                args => [ $prod, @$args[ grep $_ != $next_rloc, 0 .. $#$args ] ],
            });
            next;
        } elsif ($type eq 'recip') {
            $prod = $prod->recip;
            next;
        } else {
            die sprintf(
                "Don't know how to recurse %s with RHS structure %s\n",
                $expect->str, $cur->str,
            );
        }
    }

    $prod = $prod->clean;
    my $rest = Axiom::Expr->new({
        type => 'pluslist',
        args => [
            $rhs,
            Axiom::Expr->new({
                type => 'mullist',
                args => [ $prod->copy, $expect->copy ],
            })->negate,
        ],
    })->clean;
    my $itervar = do {
        my $binding = $source_dict->insert_local('i');
        my $new = Axiom::Expr->new({
            type => 'name',
            args => [ $binding->name ],
        });
        $new->bind($binding);
        $new;
    };
    my $rest_iter = Axiom::Expr->new({
        type => 'sum',
        args => [
            $itervar,
            _zero(),
            Axiom::Expr->new({
                type => 'pluslist',
                args => [
                    $count->copy,
                    _one()->negate,
                ],
            }),
            Axiom::Expr->new({
                type => 'mullist',
                args => [
                    Axiom::Expr->new({
                        type => 'pow',
                        args => [
                            $prod->copy,
                            $itervar,
                        ],
                    }),
                    $rest->subst_var($var, _f_pow($var, $iter, $itervar)),
                ],
            }),
        ],
    });

    # (f(x) = af(g(x)) + bh(x) + c)
    # -> f(x) = a^n . f(g^n(x)) + \sum_{i=0}^{n-1}{a^i(bh(g^i(x)) + c)}
    my $repl = Axiom::Expr->new({
        type => 'equals',
        args => [
            $lhs->copy,
            Axiom::Expr->new({
                type => 'pluslist',
                args => [
                    Axiom::Expr->new({
                        type => 'mullist',
                        args => [
                            Axiom::Expr->new({
                                type => 'pow',
                                args => [
                                    $prod->copy,
                                    $count->copy,
                                ],
                            }),
                            $lhs->subst_var($var, $base_pow),
                        ],
                    }),
                    $rest_iter,
                ],
            }),
        ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    $self->rule(sprintf 'recurse(%s%s := %s, %s)',
        $self->_linename($line), $var->name, $iter->rawexpr, $count->rawexpr,
    );

    return 1;
}

sub _subv {
    my($e, $v) = @_;
    return Axiom::Expr->new({
        type => 'pluslist',
        args => [ $e->copy, $v->negate ],
    })->clean;
}

sub _divv {
    my($e, $v) = @_;
    return Axiom::Expr->new({
        type => 'mullist',
        args => [ $e->copy, $v->recip ],
    })->clean;
}

# Given (x, f(x), n) return f^x(n) if we know how to construct it, else undef.
sub _f_pow {
    my($var, $iter, $count) = @_;

    my $try = _subv($iter, $var);
    if ($try->is_independent($var)) {
        # (x := x + a) -> (x + an)
        return Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $var->copy,
                Axiom::Expr->new({
                    type => 'mullist',
                    args => [ $try, $count ],
                }),
            ],
        })->clean;
    }

    $try = _divv($iter, $var);
    if ($try->is_independent($var)) {
        # (x := ax) -> (a^n . x)
        return Axiom::Expr->new({
            type => 'mullist',
            args => [
                Axiom::Expr->new({
                    type => 'pow',
                    args => [ $try, $count ],
                }),
                $var,
            ],
        })->clean;
    }

    # Could handle ax + b (if we can discern it), not sure what else.
    return undef;
}

1;
