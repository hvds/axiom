package Axiom::Derive::Factor;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Factor - rearrange a subexpression by factoring

=head1 USAGE

  factor ( optline, location, expr )

Factors the given I<expr> out of the subexpression at I<location>.

Eg given C< x = 2/y + 3/y(y+1) + 1 >, C< factor(2, 1/y) > will construct
C< x = (1 / y)(2 + 3/(y + 1) + y) >.

TODO: we currently support only factoring from type C<pluslist> or C<sum>.

=cut

*_one = \&Axiom::Derive::_one;

sub rulename { 'factor' }
sub rulere { <<'RE' }
    <rule: factor>
        factor \( <[args=optline]> <[args=location]> , <[args=Expr]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $expr) = @$args;
    my $starting = $self->line($line);

    my $targ = $starting->locate($loc);
    my $subdict = $starting->dict_at($loc);
    $expr->resolve($subdict);

    my $repl;
    if ($targ->type eq 'pluslist') {
        $repl = Axiom::Expr->new({
            type => 'mullist',
            args => [ $expr, Axiom::Expr->new({
                type => 'pluslist',
                args => [ map _div($_, $expr), @{ $targ->args } ],
            }) ],
        });
    } elsif ($targ->type eq 'sum') {
        $repl = Axiom::Expr->new({
            type => 'mullist',
            args => [ $expr, Axiom::Expr->new({
                type => 'sum',
                args => [
                    map($_->copy, @{ $targ->args }[0 .. 2]),
                    _div($targ->args->[3], $expr),
                ],
            }) ],
        });
    } else {
        die sprintf "don't know how to factor a %s\n", $targ->type;
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'factor(%s%s, %s)',
            $self->_linename($line), join('.', @$loc), $expr->rawexpr;

    return 1;
}

sub _div {
    my($e1, $e2) = @_;
    my($t1, $t2) = map $_->type, ($e1, $e2);
    return _one() if !$e1->diff($e2);
    my $a1 = $e1->args;
    my $r2 = ($t2 eq 'recip')
        ? $e2->args->[0]
        : Axiom::Expr->new({
            type => 'recip',
            args => [ $e2 ],
        });
    if ($t1 eq 'mullist') {
        my($index) = grep !$a1->[$_]->diff($e2), 0 .. $#$a1;
        if (defined $index) {
            return Axiom::Expr->new({
                type => 'mullist',
                args => [ map {
                    $_ == $index ? () : $a1->[$_]->copy
                } 0 .. $#$a1 ],
            });
        }
        return Axiom::Expr->new({
            type => 'mullist',
            args => [ map($_->copy, @$a1), $r2 ],
        });
    }
    if ($t1 eq 'negate' && $a1->[0]->type eq 'mullist') {
        return Axiom::Expr->new({
            type => 'negate',
            args => [ _div($a1->[0], $e2) ],
        });
    }
    return Axiom::Expr->new({
        type => 'mullist',
        args => [ $e1, $r2 ],
    });
}

1;
