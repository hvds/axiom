package Axiom::Derive::Theorem;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Theorem - name a theorem being derived

=head1 USAGE

  derive: theorem ( name? )
  rule: [ name? ]

The final result of this derivation, once validated, can be referred
to later by the given name within the same scope. If at file scope,
it is also exported by C<import> of that file, with a prefix of the
file basename.

=cut

sub rulename { 'theorem' }

sub derive_args {
    q{
        (?: <[args=rulename]> | <args=(?{ [] })> )
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
    };
}

sub late_resolve {
    my($self, $include) = @_;
    return +($include && $self->context->in_scope) ? 1 : 0;
}

sub derive {
    my($self, $args) = @_;
    return $self->validate($args);
}

sub include {
    my($self, $args) = @_;
    return $self->null if $self->context->in_scope;
    return $self->validate($args, 1);
}

sub validate {
    my($self, $args, $including) = @_;
    if (@$args) {
        my $name = $args->[0] // '';
        $self->name($name);
        $self->rule("theorem $name");
    } else {
        $self->rule('theorem');
    }
    unless ($including) {
        $self->validate_diff($self->working) or return;
    }
    return 1;
}

1;
