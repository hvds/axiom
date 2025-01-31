package Axiom::Derive::Ponens;

use v5.10;
use strict;
use warnings;
use List::Util qw{ first };

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Ponens - apply modus ponens

=head1 USAGE

  derive: ponens ( line?, line2 )
  rule: [ line, line2 ]

Given prior theorems I<line> of the form C< \Ax: P(x) > and
C<< \Ax: P(x) -> Q(x) >>, proves C< \Ax: Q(x) >.

=cut

sub rulename { 'ponens' }

sub derive_args {
    (2, q{ <[args=optline]> \s* <[args=line]> });
}

sub derive {
    my($self, $args) = @_;
    $self->validate($args);
}

sub validate {
    my($self, $args) = @_;
    my($line, $line2) = @$args;
    my $base = $self->line($line2);     # P1 -> Q1
    my $prior = $self->line($line);     # P2
    my $target = $self->expr;           # Q2
    $target->resolve($self->dict);

    my @basevar;
    my $e = $base;
    while ($e->type eq 'forall') {
        (my($var), $e) = @{ $e->args };
        push @basevar, $var;
    }
    return $self->set_error(sprintf(
        "Can't use ponens with a %s", $e->type
    )) unless $e->type eq 'implies';
    my($p1, $q1) = @{ $e->args };

    my(@p1var, @p2var);
    while ($p1->type eq 'forall') {
        (my($var), $p1) = @{ $p1->args };
        push @p1var, $var;
    }
    my $p1v = 0;

    $e = $prior;
    while ($e->type eq 'forall') {
        (my($var), $e) = @{ $e->args };
        if ($p1v < @p1var && $var->name eq $p1var[$p1v]->name) {
            ++$p1v;
        } else {
            push @p2var, $var;
        }
    }
    my $p2 = $e;
    return $self->set_error(sprintf(
        'antecedent %s does not satisfy prior vars [%s]',
        $p1->str, join(', ', map $_->name, @p1var[$p1v .. $#p1var])
    )) if $p1v < @p1var;
    return $self->set_error(sprintf(
        'antecedent %s does not match prior %s',
        $p1->str, $p2->str
    )) if $p1->diff($p2, 1);

    my(@q1var, @q2var);
    while ($q1->type eq 'forall') {
        (my($var), $q1) = @{ $q1->args };
        push @q1var, $var;
    }
    my $q1v = 0;

    $e = $target;
    while ($e->type eq 'forall') {
        (my($var), $e) = @{ $e->args };
        if ($q1v < @q1var && $var->name eq $q1var[$q1v]->name) {
            ++$q1v;
        } else {
            push @q2var, $var;
        }
    }
    my $q2 = $e;
    return $self->set_error(sprintf(
        'conclusion %s does not satisfy target vars [%s]',
        $q1->str, join(', ', map $_->name, @q1var[$q1v .. $#q1var])
    )) if $q1v < @q1var;
    return $self->set_error(sprintf(
        'conclusion %s does not match target %s',
        $q1->str, $q2->str
    )) if $q1->diff($q2, 1);

    my(@pvar, @qvar);
    for my $var (@basevar) {
        my $name = $var->name;
        unless ($p2->is_independent($var)) {
            my $pi = first { $p2var[$_]->name eq $name } 0 .. $#p2var;
            return $self->set_error(sprintf(
                'missing var %s in prior %s',
                $name, $prior->str
            )) unless defined $pi;
            push @pvar, splice @p2var, $pi, 1;
        }
        unless ($q2->is_independent($var)) {
            my $qi = first { $q2var[$_]->name eq $name } 0 .. $#q2var;
            return $self->set_error(sprintf(
                'missing var %s in target %s',
                $name, $target->str
            )) unless defined $qi;
            push @qvar, splice @q2var, $qi, 1;
        }
    }

    my $result = $q1->copy;
    $result = Axiom::Expr->new({
        type => 'forall',
        args => [ $_->copy, $result ],
    }) for (reverse(@q1var), reverse(@qvar));
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'ponens(%s%s)',
            $self->_linename($line), $line2);

    return 1;
}

1;
