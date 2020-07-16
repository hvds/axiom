package Axiom::Derive::Axiom;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;
use Scalar::Util qw{ weaken };
use List::Util qw{ first };

=head1 NAME

Axiom::Derive::Axiom - introduce an axiom

=head1 USAGE

  axiom ( name )

Always valid, the resulting expression is accepted as an axiom with
the given name.

=cut

sub rulename { 'axiom' }

sub rulere { <<'RE' }
    <rule: axiom> axiom (?:
        <[args=rulename]>
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
    |
        <args=(?{ [] })>
    )
RE

*derivere = \&rulere;

sub derive {
    my($self, $args) = @_;
    return $args;
}

sub validate {
    my($self, $args) = @_;
    $self->working($self->expr);
    if (@$args) {
        push @{ $self->working_name }, $args->[0];
        push @{ $self->rules }, "axiom $args->[0]";
    } else {
        push @{ $self->rules }, 'axiom';
    }
    return 1;
}

1;
