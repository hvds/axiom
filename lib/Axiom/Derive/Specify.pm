package Axiom::Derive::Specify;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Specify - fix a specific value for a universal quantifier

=head1 USAGE

  derive: specify ( line? )
  rule: [ line, var, expr ]

Given a prior theorem of the form C< \Aa: \Ab: P(a, b) >, can construct
new theorems such as C< P(x, y) >, C< \Aa: \Ac: \Ad: P(a, c+d-e) > or
C< \Aa: \Ab: P(b, a) >.

=head1 RESTRICTIONS

Values specified for each variable must be a number over their entire
range.

New quantified variables may not shadow free variables in the original
theorem. New free variables may not shadow unspecified quantified
variables in the original theorem.

Quantified variables at the top level are expected to appear in alphabetical
order both before and after, derivation may fail if this is not the case.

=cut

sub rulename { 'specify' }

sub derive_args {
    (1, q{ <[args=line]>? });
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $foe = $self->box($line)->unwrap;
    my $toe = $self->tbox->unwrap;
    my $map = $foe->find_mapping($toe) or return;
    return $self->validate([ $line, $map ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $map) = @$args;
    my $foe = $self->box($line)->unwrap;
    my $toe = $self->tbox->unwrap;

    # Replace the quantifier wrappings with those of the target
    my $expr = $toe->rewrap_map($foe, $map)->expr;
    $self->validate_diff($expr) or return;
    $self->rule(sprintf 'specify(%s%s)',
            $self->_linename($line), $self->_varmap2($map));

    return 1;
}

1;
