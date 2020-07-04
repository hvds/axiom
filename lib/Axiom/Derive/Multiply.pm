package Axiom::Derive::Multiply;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Multiply - multiply both sides of an equate by some expr

=head1 USAGE

  multiply ( optline, expr )

Given a prior theorem of the form C< P = Q >, constructs the new theorem
C< P . expr = Q . expr >.

=cut

sub rulename { 'multiply' }
sub rulere { <<'RE' }
    <rule: multiply>
        multiply \( <[args=optline]> <[args=Expr]> \)
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
        "don't know how to multiply a %s\n", $starting->type,
    );

    my $repl = Axiom::Expr->new({
        type => $eq->type,
        args => [ map Axiom::Expr->new({
            type => 'mullist',
            args => [ $_->copy, $expr->copy ],
        }), @{ $eq->args } ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'multiply(%s%s)',
            $self->_linename($line), $expr->rawexpr;

    return 1;
}

1;
