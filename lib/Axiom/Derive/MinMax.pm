package Axiom::Derive::MinMax;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::MinMax - choose a minimum or maximum

=head1 USAGE

  derive: minmax ( line?, [ *with wline ] )
  rule: [ line, location, which, with ]

Replace C< \min(a, b) > or C< \max(a, b) > with either C<a> or C<b>, using
evidence from iterator ranges and/or the supplied 'with' line as needed.

=cut

sub rulename { 'minmax' }

sub derive_args {
    q{
        \(
            <[args=optline]>
            (?: \s* <.WithToken> \s* <[args=line]> )?
        \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 1) })
    };
}

sub derive {
    my($self, $args) = @_;
    my($line, $with) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);
    my $loc = $starting->diff($target);

    my $iter = $starting->iter_locn($loc);
    my @maybe;
    while (my($se, $loc) = $iter->()) {
        my $set = $se->type;
        push @maybe, [ $se, $loc ] if $set eq 'min' || $set eq 'max';
    };

    my($aloc, $ai);
    MAYBE: for (@maybe) {
        my($se, $mloc) = @$_;
        my $sa = $se->args;
        for my $i (0 .. $#$sa) {
            my $expr = $starting->substitute($mloc, $sa->[$i]);
            next if $expr->diff($target, 1);
            ($aloc, $ai) = ($mloc, $i);
            last MAYBE;
        }
    }
    return $self->set_error(sprintf(
        "Can't find min/max to substitute"
    )) unless $aloc;
    return $self->validate([ $line, $loc, $ai, $with ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $argi, $with) = @$args;
    my $starting = $self->line($line)->copy;
    $starting->resolve($self->dict);
    my $dict = $starting->dict_at([]);

    my $expr = $starting->locate($loc);
    my $type = $expr->type;
    return $self->set_error(sprintf(
        'Expect type min or max, not %s', $type
    )) unless $type eq 'min' || $type eq 'max';
    my $ea = $expr->args;
    return $self->set_error(sprintf(
        'Expr does not have argument %s', $argi
    )) unless 0 <= $argi && $argi <= $#$ea;
    my $rel = ($type eq 'min') ? 'rle' : 'rge';

    # is this argument provably the min/max of its group?
    for my $argj (0 .. $#$ea) {
        next if $argi == $argj;
        next if $self->check_range(Axiom::Expr->new({
            type => $rel,
            args => [ map $_->copy, @$ea[$argi, $argj] ],
        }), $starting, $loc, $with);
        return undef;
    }

    my $result = $starting->substitute($loc, $ea->[$argi]);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'minmax(%s%s, %s%s)',
        $self->_linename($line), join('.', @$loc),
        $argi, $with ? ", $with" : ''
    );

    return 1;
}

1;
