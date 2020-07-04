package Axiom::Derive::CondStart;

use v5.10;
use strict;
use warnings;

=head1 NAME

Axiom::Derive::CondStart - open new scope for Conditional Proof

=head1 USAGE

  condstart ( varlist )

Starts a conditional proof, introducing the resulting expression as
temporarily axiomatic. The variables listed in I<varlist> are introduced
as free variables for the scope of the conditional proof.

=cut

sub rulename { 'condstart' }
sub rulere { <<'RE' }
    <rule: condstart> condstart \( <[args=varlist]> \)
        (?{ $MATCH{args}[0] = $MATCH{args}[0]{args} })
RE

sub validate {
    my($self, $args) = @_;
    my($varlist) = @$args;

    my $dict = $self->dict->clone;
    $dict->insert($_->name, 'var') for @$varlist;

    my $result = $self->expr;
    $result->resolve($dict);
    $self->working($self->expr);

    $self->{dict} = $dict;
    $self->scope(1);

    push @{ $self->rules }, sprintf 'condstart({ %s })',
            join ', ', map $_->name, @$varlist;

    return 1;
}

1;
