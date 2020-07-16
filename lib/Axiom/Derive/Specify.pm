package Axiom::Derive::Specify;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Specify - fix a specific value for a universal quantifier

=head1 USAGE

  specify ( optline, var := expr )

Given a prior theorem of the form C< \Aa: P(a) >, constructs the
new theorem C< P(x) >.

=cut

sub rulename { 'specify' }

sub rulere { <<'RE' }
    <rule: specify> specify \( <[args=optline]> <[args=pair]> \)
        (?{ @{ $MATCH{args} } = (
            $MATCH{args}[0]{args}, @{ $MATCH{args}[1]{args} }
        ) })
RE

*derivere = \&rulere;

sub derive {
    my($self, $args) = @_;
    return $args;
}

sub validate {
    my($self, $args) = @_;
    my($line, $var, $value) = @$args;
    my $starting = $self->line($line);

    my $expr = $starting;
    my $loc = [];
    while (1) {
        $expr->type eq 'forall' or die sprintf(
            'Need forall for specify(), not %s', $expr->type,
        );
        my($fvar, $fexpr) = @{ $expr->args };
        if ($fvar->name ne $var->name) {
            push @$loc, 2;
            $expr = $fexpr;
            next;
        }
        $var = $fvar;
        $expr = $fexpr;
        last;
    }

    # note _not_ including $var
    my $subdict = $starting->dict_at($loc);
    $value->resolve($subdict);

    my $repl = $expr->subst_var($var, $value);
    my $result = $starting->substitute($loc, $repl);
    $self->working($result);

    push @{ $self->rules }, sprintf 'specify(%s%s, %s)',
            $self->_linename($line), $var->rawexpr, $value->rawexpr;

    return 1;
}

1;
