package Axiom::Derive::IterExpand;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::IterExpand - write out an iterator in full

=head1 USAGE

  derive: iterexpand ( line? )
  rule: [ line, location ]

Fully expands the iterator at I<location>. Requires that the range of
the iterator is constant and finite.

Eg given C< x = \sum_{i=1}^3{y^i} >, C< iterexpand(2) > will construct
C< x = y + y^2 + y^3 >.

TODO: currently supports only type C<sum>.

TODO: could also support non-constant ranges in some cases, eg when the
expression does not depend on the iterator variable.

=cut

sub rulename { 'iterexpand' }

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
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);
    my $loc = $starting->diff($target);
    my $sfrom = $starting->locate($loc);
    if ($sfrom->is_iter) {
        return $self->validate([ $line, $loc ]);
    }

    if ($sfrom->is_list) {
        my $afrom = $sfrom->args;
        my @i = grep $afrom->[$_]->is_iter, 0 .. $#$afrom;
        if (@i == 1) {
            return $self->validate([ $line, [ @$loc, $i[0] + 1 ] ]);
        }
        my $sto = $target->locate($loc);
        if ($sto->type eq $sfrom->type) {
            for my $cmpto (@{ $sto->args }) {
                next unless $cmpto->is_iter;
                for (0 .. $#i) {
                    my $cmpfrom = $afrom->[$i[$_]];
                    next if $cmpfrom->diff($cmpto);
                    splice @i, $_, 1;
                    last;
                }
                last if @i == 1;
            }
            if (@i == 1) {
                return $self->validate([ $line, [ @$loc, $i[0] + 1 ] ]);
            }
        }
    }
    return $self->set_error("don't know how to derive");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc) = @$args;
    my $starting = $self->line($line);

    my $iter = $starting->locate($loc);
    return $self->set_error(sprintf(
        "Cannot iterate over a %s\n", $iter->type,
    )) unless $iter->is_iter;
    my $combiner = $iter->combiner;
    my $repl = Axiom::Expr->new({
        type => $combiner,
        args => [ map $iter->value_at($_), @{ $iter->range } ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'iterexpand(%s%s)',
            $self->_linename($line), join('.', @$loc));

    return 1;
}

1;
