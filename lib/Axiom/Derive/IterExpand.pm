package Axiom::Derive::IterExpand;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::IterExpand - write out an iterator in full

=head1 USAGE

  iterexpand ( optline, location )

Fully expands the iterator at I<location>. Requires that the range of
the iterator is constant and finite.

Eg given C< x = \sum_{i=1}^3{y^i} >, C< iterexpand(2) > will construct
C< x = y + y^2 + y^3 >.

TODO: currently supports only type C<sum>.

TODO: could also support non-constant ranges in some cases, eg when the
expression does not depend on the iterator variable.

=cut

sub rulename { 'iterexpand' }
sub rulere { <<'RE' }
    <rule: iterexpand>
        iterexpand \( <[args=optline]> <[args=location]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $loc) = @$args;
    my $starting = $self->line($line);

    my $iter = $starting->locate($loc);
    my $repl;
    die sprintf "Cannot iterate over a %s\n", $iter->type
            unless $iter->is_iter;

    if ($iter->type eq 'sum') {
        $repl = Axiom::Expr->new({
            type => 'pluslist',
            args => [ map $iter->value_at($_), @{ $iter->range } ],
        });
    } else {
        die sprintf "don't know how to expand a %s\n", $iter->type;
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'iterexpand(%s%s)',
            $self->_linename($line), join('.', @$loc);

    return 1;
}

1;
