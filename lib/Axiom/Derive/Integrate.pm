package Axiom::Derive::Integrate;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Integrate - find the integral of a polynomial

=head1 USAGE

  derive: integrate ( line? )
  rule: [ line, location, expr ]

Replaces \int_{x=a}^b{e} with \eval_{x=a}^b{f}, where e = df/dx.

=cut

sub rulename { 'integrate' }

sub derive_args {
    q{
        (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
    };
}

sub _derivative {
    my($self, $var, $expr) = @_;
    return Axiom::Expr->new_const(0)
            if $expr->is_independent($var);
    my $type = $expr->type;
    my $cb = {
        negate => sub {
            my $arg = $expr->args->[0];
            return $self->_derivative($var, $arg)->negate;
        },
        pluslist => sub {
            return Axiom::Expr->new({
                type => 'pluslist',
                args => [ map $self->_derivative($var, $_), @{ $expr->args } ],
            });
        },
        mullist => sub {
            my $args = $expr->args;
            my $deriv = [ map $self->_derivative($var, $_), @$args ];
            return Axiom::Expr->new({
                type => 'pluslist',
                args => [ map {
                    local $args->[$_] = $deriv->[$_];
                    Axiom::Expr->new({
                        type => 'mullist',
                        args => [ map $_->copy, @$args ],
                    });
                } 0 .. $#$args ],
            });
        },
        name => sub {
            return Axiom::Expr->new_const(1);
        },
        pow => sub {
            my($left, $right) = @{ $expr->args };
            return Axiom::Expr->new({
                type => 'mullist',
                args => [
                    $right->copy,
                    $self->_derivative($var, $left),
                    Axiom::Expr->new({
                        type => 'pow',
                        args => [
                            $left->copy,
                            Axiom::Expr->new({
                                type => 'pluslist',
                                args => [
                                    $right->copy,
                                    Axiom::Expr->new_const(-1),
                                ],
                            }),
                        ],
                    }),
                ],
            });
        },
    }->{$type} // return $self->set_error(
        "don't know how to find derivative of a $type (@{[ $expr->str ]})"
    );
    return $cb->();
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);
    my $loc = $starting->diff($target);

    my $te = $target->locate($loc);
    return $self->set_error("rhs not inteval but @{[ $te->type ]}")
            unless $te->type eq 'inteval';

    my($tvar, $tfrom, $tto, $texpr) = @{ $te->args };
    return $self->validate([ $line, $loc, $texpr ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $eval) = @$args;
    my $starting = $self->line($line);

    my $int = $starting->locate($loc);
    return $self->set_error(sprintf(
        "Don't know how to integrate a %s\n", $int->type,
    )) unless $int->type eq 'integral';

    # for resolving, we need a state in which the \int{...} variable has
    # already been introduced
    my $dloc = [ @$loc, 4 ];
    my $subdict = $starting->dict_at($dloc);

    my $repl;
    my($var, $from, $to, $expr) = @{ $int->args };
    $repl = Axiom::Expr->new({
        type => 'inteval',
        args => [ $var, $from, $to, $eval ],
    });

    $eval->resolve($subdict);
    $var->resolve($subdict);
    my $reverse = $self->_derivative($var, $eval);
    $reverse->resolve($subdict);
    if (my $diff = $reverse->diff($expr)) {
        return $self->set_error(sprintf(
            "Expressions differ at\n  %s\n  %s\nclean:\n  %s\n  %s\n",
            (map $_->locate($diff)->str, $expr, $reverse),
            (map $_->clean->str, $expr, $reverse)
        ));
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'integrate(%s%s, %s)',
            $self->_linename($line), join('.', @$loc), $eval->str);

    return 1;
}

1;
