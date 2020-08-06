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
the given name.

=cut

sub rulename { 'axiom' }

sub derive_args {
    q{
        (?:
            <[args=rulename]>
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        |
            <args=(?{ [] })>
        )
    };
}

sub derive {
    my($self, $args) = @_;
    return $self->validate($args);
}

*include = \&derive;

sub validate {
    my($self, $args) = @_;
    $self->working($self->expr);
    if (@$args) {
        my($name) = @$args;
        $self->name($name);
        $self->rule("axiom $name");
    } else {
        $self->rule('axiom');
    }
    return 1;
}

1;
