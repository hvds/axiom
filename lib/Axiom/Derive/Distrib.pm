package Axiom::Derive::Distrib;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Distrib - derive new theorem by distributing some operator

=head1 USAGE

  distrib ( optline, location, arg1, arg2 )

For the subexpression at the given I<location>, distribute the expression
at its I<arg1>th argument over its I<arg2>th argument.

Eg given C< x = y(y + 1) >, the derivation C< distrib(2, 1, 2) > will
construct C< x = y . y + y >.

TODO: we currently support only type C<mullist> at I<location>, and only
with type C<pluslist> or C<sum> at I<arg2>.

=cut

sub rulename { 'distrib' }
sub rulere { <<'RE' }
    <rule: distrib>
        distrib \(
            <[args=optline]> <[args=location]> , <[args=arg]> , <[args=arg]>
        \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $from, $over) = @$args;
    my $starting = $self->line($line);

    my $expr = $starting->locate($loc);
    my $efrom = $expr->args->[$from - 1]
            // die sprintf "arg %s missing in %s\n", $from, $expr->str;
    my $eover = $expr->args->[$over - 1]
            // die sprintf "arg %s missing in %s\n", $over, $expr->str;

    my $repl;
    if ($expr->type eq 'mullist'
        && ($eover->type eq 'pluslist' || $eover->type eq 'sum')
    ) {
        my $eargs = $eover->args;
        my $combined = ($eover->type eq 'pluslist')
            ? Axiom::Expr->new({
                type => 'pluslist',
                args => [
                    map Axiom::Expr->new({
                        type => 'mullist',
                        args => [ $_, $efrom ],
                    }), map $_->copy, @$eargs
                ],
            })
            : Axiom::Expr->new({
                type => 'sum',
                args => [
                    $eargs->[0]->copy,
                    $eargs->[1]->copy,
                    $eargs->[2]->copy,
                    Axiom::Expr->new({
                        type => 'mullist',
                        args => [ $eargs->[3]->copy, $efrom ],
                    }),
                ],
            });

        $repl = Axiom::Expr->new({
            type => 'mullist',
            args => [ map {
                $_ == $from - 1
                    ? ()
                : $_ == $over - 1
                    ? $combined
                    : $expr->args->[$_]->copy
            } 0 .. $#{ $expr->args } ],
        });
    } else {
        die sprintf "don't know how to distribute a %s over a %s\n",
                $efrom->type, $eover->type;
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'distrib(%s%s, %s, %s)',
            $self->_linename($line), join('.', @$loc), $from, $over;

    return 1;
}

1;
