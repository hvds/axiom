package Axiom::Derive::Theorem;

use v5.10;
use strict;
use warnings;

=head1 NAME

Axiom::Derive::Theorem - name a theorem being derived

=head1 USAGE

  derive: theorem ( name? )
  rule: [ name? ]

The final result of this derivation, once validated, can be referred
to later by the given name.

=cut

sub rulename { 'theorem' }

sub derivere { <<'RE' }
    <rule: theorem> theorem (?: <[args=rulename]> | <args=(?{ [] })> )
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
RE

sub derive {
    my($self, $args) = @_;
    return $args;
}

sub validate {
    my($self, $args) = @_;
    if (@$args) {
        my($name) = @$args;
        $self->name($name);
        $self->rule("theorem $name");
    } else {
        $self->rule('theorem');
    }
    return 1;
}

1;
