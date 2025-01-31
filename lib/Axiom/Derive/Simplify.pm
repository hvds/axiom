package Axiom::Derive::Simplify;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Simplify - pick one or more statements from an andlist

=head1 USAGE

  derive: simplify ( line? )
  rule: [ line, expr ]

Given a prior theorem of the form C< P & Q & R >, constructs a new theorem
such as C< P & R >.

The C<andlist> may be wrapped in an arbitrary number of qualifiers.

=cut

sub rulename { 'simplify' }

sub derive_args {
    (1, q{ <[args=line]>? });
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $from_base = $self->line($line);
    my $from = $from_base;
    my $to = $self->expr;
    my $loc = [];
    while ($from->is_quant) {
        push @$loc, 2;
        $from = $from->args->[1];
        $to->is_quant
                or return $self->set_error('mismatched quantifiers');
        $to = $to->args->[1];
    }
    $from->type eq 'andlist'
            or return $self->set_error('No andlist to derive from');
    my $expr = $to->copy;
    $expr->resolve($from_base->dict_at($loc));
    $expr = $expr->clean;
    return $self->validate([ $line, $expr ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $expr) = @$args;
    my $starting = $self->line($line);

    my $loc = [];
    my $and = $starting;
    while ($and->is_quant) {
        push @$loc, 2;
        $and = $and->args->[1];
    }
    $and->type eq 'andlist' or return $self->set_error(sprintf(
        "don't know how to simplify a %s\n", $and->type
    ));

    my $targ = ($expr->type eq 'andlist') ? $expr->args : [ $expr ];
  TARG:
    for my $t (@$targ) {
        $t = $t->clean;
        for my $s (@{ $and->args }) {
            next TARG if !$t->diff($s->clean, 1);
        }
        return $self->set_error(
            sprintf 'no match found for target expression %s', $t->str
        );
    }

    my $result = $starting->substitute($loc, $expr->copy);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'simplify(%s%s)',
            $self->_linename($line), $expr->rawexpr);
    return 1;
}

1;
