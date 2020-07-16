package Axiom::Derive::Recurse;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Recurse - recursively apply a mapping equality

=head1 USAGE

  recurse ( optline, var := expr1, expr2 )

Given an I<optline> equating some function C<f> of I<var> to some function
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

=cut

*_zero = \&Axiom::Derive::_zero;
*_one = \&Axiom::Derive::_one;

sub rulename { 'recurse' }
sub rulere { <<'RE' }
    <rule: recurse>
        recurse \( <[args=optline]> <[args=pair]> , <[args=Expr]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 1) })
        (?{ splice @{ $MATCH{args} }, 1, 1, @{ $MATCH{args}[1] } })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $var, $iter, $count) = @$args;
    my $starting = $self->line($line);

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
        $cur = $_ ? $cur->args->[ $rloc->[$_ - 1] ] : $rhs;
        my $type = $cur->type;
        if ($type eq 'pluslist') {
            next;
        } elsif ($type eq 'negate') {
            $prod = $prod->negate;
            next;
        } elsif ($type eq 'mullist') {
            my $next_rloc = $rloc->[$_];
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
    my $itervar = $self->new_local('i');
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

    push @{ $self->rules }, sprintf(
        'recurse(%s%s := %s, %s)',
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
