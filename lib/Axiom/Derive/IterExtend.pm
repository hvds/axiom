package Axiom::Derive::IterExtend;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::IterExtend - change the range of an iterator

=head1 USAGE

  iterextend ( optline, location, which, dir )

Modifies the iterator at I<location> by adding or removing one element,
at either the I<from> or the I<to> end.

We modify the I<to> value if I<which> is C<1>, or I<from> if I<which> is
C<-1>. We extend upwards if I<dir> is C<1>, or downwards if I<dir> is C<-1>.
In every case we add or subtract the appropriate balancing expression.

Eg given C< x = \sum_{i=1}^n{y^i} >, C<iterextend(2, -1, -1)> will derive
C< x = \sum_{i=0}^n{y^i} - y^0 >.

TODO: currently supports only type C<sum>.

=cut

sub rulename { 'iterextend' }
sub rulere { <<'RE' }
    <rule: iterextend>
        iterextend \( <[args=optline]> <[args=location]> ,
                <[args=num]> (?: , <[args=num]> )? \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $which, $dir) = @$args;
    my $starting = $self->line($line);

    my $iter = $starting->locate($loc);
    my $repl;

    if ($iter->type eq 'sum') {
        my($var, $from, $to, $expr) = @{ $iter->args };
        my $base = ($which > 0) ? $to : $from;
        my $var_at = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $base->copy,
                Axiom::Expr->new({
                    type => 'integer',
                    args => [ $dir > 0 ? '1' : '-1' ],
                }),
            ],
        });
        my $newfrom = ($which > 0) ? $from->copy : $var_at;
        my $newto = ($which > 0) ? $var_at : $to->copy;
        my($sign, $diff) = ($which > 0)
            ? ($dir > 0) ? (-1, $var_at) : (1, $to)
            : ($dir > 0) ? (1, $from) : (-1, $var_at);
        my $value = $iter->value_at($diff);
        $repl = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                Axiom::Expr->new({
                    type => 'sum',
                    args => [
                        $var->copy,
                        $newfrom,
                        $newto,
                        $expr->copy,
                    ],
                }),
                ($sign > 0
                    ? $value
                    : Axiom::Expr->new({
                        type => 'negate',
                        args => [ $value ],
                    }),
                ),
            ],
        });
    } else {
        die sprintf "Don't know how to extend a %s\n", $iter->type;
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'iterextend(%s%s, %s, %s)',
            $self->_linename($line), join('.', @$loc), $which, $dir;

    return 1;
}

1;
