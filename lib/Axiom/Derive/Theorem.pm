package Axiom::Derive::Theorem;

use v5.10;
use strict;
use warnings;

=head1 NAME

Axiom::Derive::Theorem - name a theorem being derived

=head1 USAGE

  theorem ( name )

The final result of this derivation, once validated, can be referred
to later by the given name.

=cut

sub rulename { 'theorem' }
sub rulere { <<'RE' }
    <rule: theorem> theorem (?: <[args=rulename]> | <args=(?{ [] })> )
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
RE

sub validate {
    my($self, $args) = @_;
    if (@$args) {
        push @{ $self->working_name }, $args->[0];
        push @{ $self->rules }, "theorem $args->[0]";
    } else {
        push @{ $self->rules }, 'theorem';
    }
    return 1;
}

1;
