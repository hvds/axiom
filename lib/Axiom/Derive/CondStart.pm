package Axiom::Derive::CondStart;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::CondStart - open new scope for Conditional Proof

=head1 USAGE

  derive: condstart
  rule: [ varlist ]

Starts a conditional proof, introducing the resulting expression as
temporarily axiomatic. The variables listed in I<varlist> are introduced
as free variables for the scope of the conditional proof.

=cut

sub rulename { 'condstart' }

sub derive_args {
    q{
        <args=(?{ [] })>
    };
}

sub late_resolve { 1 }

sub derive {
    my($self, $args) = @_;
    return $self->validate([ [
        map Axiom::Expr->new({ type => 'name', args => [ $_ ] }),
                @{ $self->new_vars($self->expr) }
    ] ]);
}

sub validate {
    my($self, $args) = @_;
    my($varlist) = @$args;

    my $dict = $self->dict->clone;
    $dict->insert($_->name, 'var') for @$varlist;

    my $result = $self->expr;
    $result->resolve($dict);
    $self->validate_diff($result) or return;
    $self->{dict} = $dict;
    $self->scope(1);
    $self->rule(sprintf 'condstart({ %s })',
            join ', ', map $_->name, @$varlist);

    return 1;
}

1;
