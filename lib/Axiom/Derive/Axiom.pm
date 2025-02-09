package Axiom::Derive::Axiom;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Axiom - introduce an axiom

=head1 USAGE

  derive: axiom ( name? )
  rule: [ name? ]

Always valid, the resulting expression is accepted as an axiom with
the given name within the same scope. If at file scope, it is also
exported by C<import> of that file, with a prefix of the file basename.

=cut

sub rulename { 'axiom' }

sub derive_args {
    (0, q{});
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
    my $name = $self->name;
    $self->export_name if length $name;
    $self->rule(sprintf 'axiom%s', length($name) ? " $name" : '');
    unless ($including) {
        $self->working($self->expr);
    }
    return 1;
}

1;
