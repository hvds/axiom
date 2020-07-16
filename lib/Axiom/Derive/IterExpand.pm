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

sub derivere { <<'RE' }
    <rule: iterexpand>
        iterexpand (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
RE

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);
    my $loc = $starting->diff($target);
    my $sfrom = $starting->locate($loc);
    if ($sfrom->is_iter) {
        return [ $line, $loc ];
    }

    if ($sfrom->is_list) {
        my $afrom = $sfrom->args;
        my @i = grep $afrom->[$_]->is_iter, 0 .. $#$afrom;
        if (@i == 1) {
            return [ $line, [ @$loc, $i[0] + 1 ] ];
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
                return [ $line, [ @$loc, $i[0] + 1 ] ];
            }
        }
    }
    die "don't know how to derive";
}

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
