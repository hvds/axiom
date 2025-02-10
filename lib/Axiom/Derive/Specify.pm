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
    my $fo = $self->box($line);
    my $to = $self->tbox;
    my $fe = $fo->expr;
    my $te = $to->expr;
    my $fv = $fo->allvar;
    my $map = $self->find_mapping($fe, $te, $fv);

    # if we didn't find it, maybe one side has been simplified to the point
    # we no longer recognise it
    if (!$map && !$fe->is_atom && $fe->type eq $te->type) {
        my $fa = $fe->args;
        my $ta = $te->args;
        if (@$fa == @$ta) {
            for (0 .. $#$fa) {
                $map = $self->find_mapping($fa->[$_], $ta->[$_], $fv);
                last if $map;
            }
        }
    }
    return $self->set_error("don't know how to derive this specify")
            unless $map;

    my %vmap = (args => [
        map +{ args => [ $_->copy, $map->{$_->name} ] }, @$fv,
    ]);
    return $self->validate([ $line, \%vmap ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $map) = @$args;
    my $fo = $self->box($line);
    my $to = $self->tbox;

    # find the binding id of each variable to be replaced
    my $dict = $fo->dict_at;
    my %vmap = map {
        my($var, $expr) = @{ $_->{args} };
        $var->resolve($dict);
        my $id = $var->binding->id;
        +($id => $expr);
    } @{ $map->{args} // [] };

    # Replace the quantifier wrappings with those of the target
    my $expr = $fo->rewrap($to);
    $expr->apply_map($self->dict->clone, \%vmap);
    $self->validate_diff($expr) or return;
    $self->rule(sprintf 'specify(%s%s)',
            $self->_linename($line), $self->_varmap($map));

    return 1;
}

1;
