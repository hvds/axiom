package Axiom::Derive::Multiply;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
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

sub derive_args {
    q{
        (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
    };
}

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
        $to->is_quant
                or return $self->set_error('mismatched quantifiers');
        $to = $to->args->[1];
    }
    $from->type eq 'equals'
            or return $self->set_error('No equals to derive from');
    $to->type eq 'equals'
            or return $self->set_error('No equals to derive from');
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
    return $self->validate([ $line, $expr ]);
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
    $eq->type eq 'equals' or return $self->set_error(sprintf(
        "don't know how to multiply a %s\n", $starting->type,
    ));

    my $repl = Axiom::Expr->new({
        type => $eq->type,
        args => [ map Axiom::Expr->new({
            type => 'mullist',
            args => [ $_->copy, $expr->copy ],
        }), @{ $eq->args } ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'multiply(%s%s)',
            $self->_linename($line), $expr->rawexpr);

    return 1;
}

1;
