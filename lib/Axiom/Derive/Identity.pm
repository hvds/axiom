package Axiom::Derive::Identity;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Identity - introduce theorem X = X

=head1 USAGE

  identity ( varlist, expr )

Constructs a theorem of the form C< \Aa: \Ab: ... expr = expr >.

=cut

sub rulename { 'identity' }

sub derivere { <<'RE' }
    <rule: identity> identity <args=(?{ [] })>
RE

sub derive {
    my($self, $args) = @_;
    my $target = $self->expr;
    $target->resolve($self->dict);

    my @vars;
    my $loc = [];
    my $expr = $target;
    while ($expr->is_quant) {
        push @vars, $expr->args->[0]->name;
        $expr = $expr->args->[1];
        push @$loc, 2;
    }
    $expr->type eq 'equals' or die "no equals to derive to";
    $expr = $expr->args->[0];
    my $raw = $expr->rawexpr;
    $raw =~ s/\s+\z//;
    $expr = $expr->copy;
    $expr->{''} = $raw;
    $expr->resolve($target->dict_at($loc));
    return [
        [ map Axiom::Expr->new({ type => 'name', args => [ $_ ] }), @vars ],
        $expr,
    ];
}

sub validate {
    my($self, $args) = @_;
    my($varlist, $expr) = @$args;

    my $result = Axiom::Expr->new({
        type => 'equals',
        args => [ $expr->copy, $expr->copy ],
    });
    for my $var (reverse @$varlist) {
        $result = Axiom::Expr->new({
            type => 'forall',
            args => [ $var, $result ],
        });
    }

    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'identity({ %s }, %s)',
            join(', ', map $_->name, @$varlist), $expr->rawexpr;

    return 1;
}

1;
