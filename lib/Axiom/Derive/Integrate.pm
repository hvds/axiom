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

sub _integrate {
    my($self, $var, $expr) = @_;
    return Axiom::Expr->new({
        type => 'mullist',
        args => [ $var->copy, $expr->copy ]
    }) if $expr->is_independent($var);

    my $type = $expr->type;
    my $cb = {
        negate => sub {
            my $arg = $expr->args->[0];
            return +($self->_integrate($var, $arg) || return 0)->negate;
        },
        pluslist => sub {
            return Axiom::Expr->new({
                type => $type,
                args => [
                    map +($self->_integrate($var, $_) || return 0),
                            @{ $expr->args }
                ],
            });
        },
        mullist => sub {
            my(@i, $d);
            for (@{ $expr->args }) {
                if ($_->is_independent($var)) {
                    push @i, $_;
                } elsif (defined $d) {
                    return $self->set_error(
                            "subexpr @{[ $expr->str ]} not flat");
                } else {
                    $d = $_;
                }
            }
            return Axiom::Expr->new({
                type => $type,
                args => [
                    map($_->copy, @i),
                    $self->_integrate($var, $d) || return 0,
                ],
            });
        },
        name => sub {
            return Axiom::Expr->new({
                type => 'mullist',
                args => [
                    Axiom::Expr->new({
                        type => 'pow',
                        args => [
                            $var->copy,
                            Axiom::Expr::Const->new({ args => [ 2 ] }),
                        ],
                    }),
                    Axiom::Expr::Const->new({args => [1, 2]}),
                ],
            });
        },
        pow => sub {
            my($left, $right) = @{ $expr->args };
            my $rv = $right->rat;
            if ($left->type eq 'name' && !$left->is_independent($var)
                && $right->is_const && $rv != -1
            ) {
                return Axiom::Expr->new({
                    type => 'mullist',
                    args => [
                        Axiom::Expr->new({
                            type => 'pow',
                            args => [
                                $var->copy,
                                Axiom::Expr::Const->new_rat($rv + 1),
                            ],
                        }),
                        Axiom::Expr::Const->new_rat($rv + 1)->recip,
                    ],
                });
            }
            return $self->set_error(
                "don't know how to integrate power (@{[ $expr->str ]}"
            );
        },
    }->{$type} // return $self->set_error(
        "don't know how to integrate a $type (@{[ $expr->str ]}"
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

    while (1) {
        my $se = $starting->locate($loc);
        my $te = $target->locate($loc);
        return $self->set_error("lhs not integral but @{[ $se->type ]}")
                unless $se->type eq 'integral';
        return $self->set_error("rhs not inteval but @{[ $te->type ]}")
                unless $te->type eq 'inteval';

        my($var, $ofrom, $oto, $oexpr) = @{ $se->args };
        my $int = $self->_integrate($var, $oexpr) || return 0;
        return 1 if $self->validate([ $line, $loc, $int ]);
        warn $self->clear_error;
    }
    return $self->set_error("don't know how to derive this");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $eval) = @$args;
    my $starting = $self->line($line);

    my $int = $starting->locate($loc);
    my $subdict = $starting->dict_at($loc);
    $eval->resolve($subdict);

    my $repl;
    if ($int->type eq 'integral') {
        my($var, $from, $to, $expr) = @{ $int->args };
        $repl = Axiom::Expr->new({
            type => 'inteval',
            args => [ $var, $from, $to, $eval ],
        });
    } else {
        return $self->set_error(sprintf(
            "Don't know how to integrate a %s\n", $int->type,
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
