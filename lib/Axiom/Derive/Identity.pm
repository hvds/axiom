package Axiom::Derive::Identity;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Identity - introduce theorem X = X

=head1 USAGE

  derive: identity
  rule: [ varlist, expr ]

Constructs a theorem of the form C< \Aa: \Ab: ... expr = expr >.

=cut

sub rulename { 'identity' }

sub derive_args {
    q{
        <args=(?{ [] })>
    };
}

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
    $expr->type eq 'equals'
            or return $self->set_error('no equals to derive to');
    $expr = $expr->args->[0];
    my $raw = $expr->rawexpr;
    $raw =~ s/\s+\z//;
    $expr = $expr->copy;
    $expr->{''} = $raw;
    $expr->resolve($target->dict_at($loc));
    return $self->validate([
        [ map Axiom::Expr->new({ type => 'name', args => [ $_ ] }), @vars ],
        $expr,
    ]);
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
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'identity({ %s }, %s)',
            join(', ', map $_->name, @$varlist), $expr->rawexpr);

    return 1;
}

1;
