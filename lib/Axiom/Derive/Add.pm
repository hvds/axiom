package Axiom::Derive::Add;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Add - add an expression to both sides of a theorem

=head1 USAGE

  derive: add ( line? )
  rule: [ line, expr ]

Given a prior theorem of the form C< P = Q >, constructs the new theorem
C< P + expr = Q + expr >.

The equality may be wrapped in an arbitrary number of quantifiers.

=cut

sub rulename { 'add' }

sub derivere { <<'RE' }
    <rule: add>
        add (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
RE

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $from_base = $self->line($line);
    my $from = $from_base;
    my $to = $self->expr;
    my $loc = [];
    while ($from->is_quant) {
        push @$loc, 2;
        $from = $from->args->[1];
        $to->is_quant or die "mismatched quantifiers";
        $to = $to->args->[1];
    }
    $from->type eq 'equals' or die "No equals to derive from";
    $to->type eq 'equals' or die "No equals to derive to";
    my $expr = Axiom::Expr->new({
        type => 'pluslist',
        args => [
            $to->args->[0]->copy,
            Axiom::Expr->new({
                type => 'negate',
                args => [ $from->args->[0]->copy ],
            }),
        ],
    });
    $expr->resolve($from_base->dict_at($loc));
    $expr = $expr->clean;
    return [ $line, $expr ];
}

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
    $self->rule(sprintf 'add(%s%s)', $self->_linename($line), $expr->rawexpr);

    return 1;
}

1;
