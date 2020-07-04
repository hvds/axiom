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
sub rulere { <<'RE' }
    <rule: identity> identity \( <[args=varlist]> , <[args=Expr]> \)
        (?{ $MATCH{args}[0] = $MATCH{args}[0]{args} })
RE

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
