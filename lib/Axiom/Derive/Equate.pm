package Axiom::Derive::Equate;

use v5.10;
use strict;
use warnings;

=head1 NAME

Axiom::Derive::Equate - substitute from an equality

=head1 USAGE

  equate ( optline, location, line, varmap )

Given a prior theorem I<line> of the form C< P(a, b, ...) = Q(a, b, ... ) >,
attempts to substitute P for Q (or Q for P) at I<location> in the I<optline>,
substituting C<a, b, ...> as necessary via the I<varmap>.

=cut

sub rulename { 'equate' }

sub rulere { <<'RE' }
    <rule: equate>
        equate \( <[args=optline]> <[args=location]> ,
                <[args=line]> (?: , <[args=varmap]> )? \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 2) })
RE

sub derivere { <<'RE' }
    <rule: equate>
        equate \( <[args=optline]> <[args=line]> , <[args=varmap]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
RE

sub derive {
    my($self, $args) = @_;
    my($line, $eqline, $map) = @$args;
    my $starting = $self->line($line);

    my $from = $self->line($eqline);
    my $from_expr = $from;
    my $from_loc = [];
    while ($from_expr->type eq 'forall') {
        push @$from_loc, 2;
        $from_expr = $from_expr->args->[1];
    }
    $from_expr->type eq 'equals' or die sprintf(
        "Can't equate() with a %s\n", $from_expr->type,
    );
    my $from_dict = $from->dict_at($from_loc);
    my @from_var = map {
        my($var, $expr) = @{ $_->{args} };
        $var->resolve($from_dict);
        $var->binding->id;
    } @{ $map->{args} // [] };

    my $target = $self->expr;
    $target->resolve($self->dict);
    my(@loc) = $starting->diff($target);
    while (@loc) {
        my $loc = shift @loc;
        my $dict = $starting->dict_at($loc);
        my $se = $starting->locate($loc);
        my %vmap = map {
            my($var, $expr) = @{ $map->{args}->[$_]->{args} };
            $expr->resolve($dict);
            ($from_var[$_] => $expr);
        } (0 .. $#{ $map->{args} // [] });
        my $equate = $from_expr->subst_vars(\%vmap);
        my($left, $right) = @{ $equate->args };
        if (! $se->diff($left)) {
            return [ $line, $loc, $eqline, $map ];
        } elsif (! $se->diff($right)) {
            return [ $line, $loc, $eqline, $map ];
        }
        next if $se->is_atom;
        push @loc, map [ @$loc, $_ + 1 ], 0 .. $#{ $se->args };
    }
    die "don't know how to derive this equate";
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $eqline, $map) = @$args;
    my $starting = $self->line($line);

    my $expr = $starting->locate($loc);
    my $from = $self->line($eqline);
    my $from_expr = $from;
    my $from_loc = [];
    while ($from_expr->type eq 'forall') {
        push @$from_loc, 2;
        $from_expr = $from_expr->args->[1];
    }
    $from_expr->type eq 'equals' or die sprintf(
        "Can't equate() with a %s\n", $from_expr->type,
    );
    my $from_dict = $from->dict_at($from_loc);
    my $to_dict = $starting->dict_at($loc);

    my %vmap = map {
        my($var, $expr) = @{ $_->{args} };
        $var->resolve($from_dict);
        $expr->resolve($to_dict);
        +($var->binding->id => $expr)
    } @{ $map->{args} // [] };
    my $equate = $from_expr->subst_vars(\%vmap);

    my $repl;
    my($left, $right) = @{ $equate->args };
    if (! $expr->diff($left)) {
        $repl = $right;
    } elsif (! $expr->diff($right)) {
        $repl = $left;
    } else {
        die sprintf(
            "Neither side of equate %s matches target %s\n",
            $equate->str, $expr->str,
        );
    }

    my $result = $starting->substitute($loc, $repl);
    $self->working($result);

    push @{ $self->rules }, sprintf 'equate(%s%s, %s, %s)',
            $self->_linename($line), join('.', @$loc),
            $eqline, $self->_varmap($map);

    return 1;
}

1;
