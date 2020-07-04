package Axiom::Derive::Add;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Add - add an expression to both sides of a theorem

=head1 USAGE

  add ( optline, expr )

Given a prior theorem of the form C< P = Q >, constructs the new theorem
C< P + expr = Q + expr >.

The equality may be wrapped in an arbitrary number of quantifiers.

=cut

sub rulename { 'add' }
sub rulere { <<'RE' }
    <rule: add>
        add \( <[args=optline]> <[args=Expr]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $expr) = @$args;
    my $starting = $self->line($line);

    my $loc = [];
    my $eq = $starting;
    while ($eq->is_quant) {
        push @$loc, 2;
        $eq = $eq->args->[1];
    }
    $eq->type eq 'equals' or die sprintf(
        "don't know how to add to a %s\n", $eq->type
    );

    my $repl = Axiom::Expr->new({
        type => $eq->type,
        args => [ map Axiom::Expr->new({
            type => 'pluslist',
            args => [ $_->copy, $expr->copy ],
        }), @{ $eq->args } ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'add(%s%s)',
            $self->_linename($line), $expr->rawexpr;

    return 1;
}

1;
