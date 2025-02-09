package Axiom::Derive::Ponens;

use v5.10;
use strict;
use warnings;
use List::Util qw{ first };

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Ponens - apply modus ponens

=head1 USAGE

  derive: ponens ( line?, line2 )
  rule: [ line, line2, varmap ]

Given prior theorems of the form C< P(a) > and C<< \Ax: P(x) -> Q(x) >>,
proves C< Q(a) >.

=cut

sub rulename { 'ponens' }

sub derive_args {
    (2, q{ <[args=optline]> \s* <[args=line]> });
}

sub derive {
    my($self, $args) = @_;
    my($line, $line2) = @$args;
    my $fo = $self->box($line2);        # \Ax: (\Ay: P1) -> (\Ay: Q1)
    my $foi = $fo->unwrap;              # (\Ay: P1) -> (\Ay: Q1)
    $foi->assert_type('implies') or return;
    my $fop = $foi->arg(0);             # \Ay: P1
    $fop = $fop->unwrap;                # P1

    my $vo = $self->box($line);         # \Ay: P2
    my $vop = $vo->unwrap;              # P2
    my $map = $fop->find_mapping($vop) or return;
    return $self->validate([ $line, $line2, $map ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $line2, $map) = @$args;
    my $fo = $self->box($line2);        # P1 -> Q1
    my $vo = $self->box($line);         # P2
    my $to = $self->tbox;               # Q2

    my $foi = $fo->unwrap;
    $foi->assert_type('implies');
    my($fop, $foq) = map $foi->arg($_)->unwrap, (0, 1);

    my $vop = $vo->unwrap;
    my $fopw = $vop->rewrap_map($fop, $map);
    $fopw->match($vo) or return;

    my $toq = $to->unwrap;
    my $foqw = $toq->rewrap_map($foq, $map);
    my $final = $foqw->expr;

    $self->validate_diff($final) or return;
    $self->rule(sprintf 'ponens(%s%s, %s)',
            $self->_linename($line), $line2, $self->_varmap2($map));

    return 1;
}

1;
