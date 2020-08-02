package Axiom::Derive::Multiply;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Multiply - multiply both sides of an equate by some expr

=head1 USAGE

  derive: multiply ( line? )
  rule: [ line, expr ]

Given a prior theorem of the form C< P = Q >, constructs the new theorem
C< P . expr = Q . expr >.

=cut

sub rulename { 'multiply' }

sub derivere { <<'RE' }
    <rule: multiply>
        multiply (?: \( <[args=line]>? \) )?
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
        type => 'mullist',
        args => [
            $to->args->[0]->copy,
            Axiom::Expr->new({
                type => 'recip',
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
