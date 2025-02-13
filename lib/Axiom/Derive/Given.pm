package Axiom::Derive::Given;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Given - use given constraints

=head1 USAGE

  derive: given ( line? )
  rule: [ line ]

From C<\Ax: P -> (Q = R)>, derive either C<\Ax: \given_{P}{Q} = R> or
C<\Ax: \given_{P}{Q} = \given_{P}{R}>.

In principle we could allow an inequality to replace the equality, but
we have no current use for that.

=cut

sub rulename { 'given' }

sub derive_args {
    (1, q{ <[args=optline]> });
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    return $self->validate([ $line ]);
}

sub validate {
    my($self, $args) = @_;
    my($line) = @$args;
    my $fo = $self->box($line);     # \Ax: P -> (Q = R)
    my $foi = $fo->unwrap;          # P -> (Q = R)
    $foi->assert_type('implies');
    my($fop, $foe) = map $foi->arg($_), (0, 1); # P, Q = R
    $foe->assert_type('req');
    my($foq, $for) = map $foe->arg($_), (0, 1); # Q, R

    my $to = $self->tbox;
    my $toe = $to->unwrap;
    $toe->assert_type('req');
    my($topq, $topr) = map $toe->arg($_), (0, 1);

    my $left = Axiom::Expr->new({
        type => 'given',
        args => [ $fop->expr->copy, $foq->expr->copy ],
    });
    my $right = $for->expr->copy;
    # FIXME: unsafe to assume that $tr->type eq 'given' means it is this one
    $right = Axiom::Expr->new({
        type => 'given',
        args => [ $fop->copy, $right ],
    }) if $topr->expr->type eq 'given';
    my $result = $toe->wrapall(Axiom::Expr->new({
        type => 'req',
        args => [ $left, $right ],
    }));
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'given(%s)', $self->_linename($line));
    return 1;
}

1;
