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
    my $fo = $self->box($line);
    my $to = $self->tbox;
    my $fe = $fo->expr;
    return $self->set_error(sprintf(
        'Expect implies, not %s', $fe->type
    )) unless $fe->type eq 'implies';
    my($fp, $fqr) = @{ $fe->args };
    return $self->set_error(sprintf(
        'Expect implication of req, not %s', $fqr->type
    )) unless $fqr->type eq 'req';
    my($fq, $fr) = @{ $fqr->args };

    my $left = Axiom::Expr->new({
        type => 'given',
        args => [ $fp->copy, $fq->copy ],
    });
    # FIXME: unsafe to assume that $tr->type eq 'given' means it is this one
    my $right = $fr->copy;
    $right = Axiom::Expr->new({
        type => 'given',
        args => [ $fp->copy, $right ],
    }) if $to->expr->type eq 'given';
    my $result = $to->wrapall(Axiom::Expr->new({
        type => $fqr->type,
        args => [ $left, $right ],
    }));
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'given(%s)', $self->_linename($line));
    return 1;
}

1;
