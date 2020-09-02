package Axiom::Derive::Equate;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Equate - substitute from an equality

=head1 USAGE

  derive: equate ( line?, eqline )
  rule: [ line, location, eqline, varmap ]

Given a prior theorem I<eqline> of the form C< P(a, b, ...) = Q(a, b, ... ) >,
attempts to substitute P for Q (or Q for P) at I<location> in I<line>,
substituting C<a, b, ...> as necessary via the I<varmap>.

FIXME: rule args should specify which side of I<eqline> is to be used,
rather than deriving that each time in validate.

=cut

sub rulename { 'equate' }

sub derive_args {
    q{
        \( <[args=optline]> \s* <[args=line]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
    };
}

sub derive {
    my($self, $args) = @_;
    my($line, $eqline) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);

    my $from = $self->line($eqline);
    my $from_expr = $from;
    my @vars;
    while ($from_expr->type eq 'forall') {
        (my($var), $from_expr) = @{ $from_expr->args };
        push @vars, $var;
    }
    $from_expr->type eq 'equals' or return $self->set_error(sprintf(
        "Can't equate() with a %s\n", $from_expr->type,
    ));

    my $iter = $starting->iter_locn;
    while (my($se, $loc) = $iter->()) {
        for my $from (@{ $from_expr->args }) {
            my $map = $self->find_mapping($from, $se, \@vars)
                    or next;
            my @vargs = ($line, $loc, $eqline, { args => [
                map +{ args => [ $_->copy, $map->{$_->name} ] }, @vars,
            ] });
            # FIXME: validate can die in eg $expr->resolve($to_dict)
            return 1 if eval { $self->validate(\@vargs) };
            $self->clear_error;
        }
    };
    return $self->set_error("don't know how to derive this equate");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $eqline, $map) = @$args;
    my $starting = $self->line($line)->copy;
    $starting->resolve($self->dict);
    my $dict = $starting->dict_at([]);

    my $expr = $starting->locate($loc);
    my $from = $self->line($eqline);
    my $from_expr = $from;
    my $from_loc = [];
    while ($from_expr->type eq 'forall') {
        push @$from_loc, 2;
        $from_expr = $from_expr->args->[1];
    }
    $from_expr->type eq 'equals' or return $self->set_error(sprintf(
        "Can't equate() with a %s\n", $from_expr->type,
    ));
    my $from_dict = $from->dict_at($from_loc);
    my $to_dict = $starting->dict_at($loc);

    my %vmap = map {
        my($var, $expr) = @{ $_->{args} };
        $var->resolve($from_dict);
        $expr->resolve($to_dict);
        +($var->binding->id => $expr)
    } @{ $map->{args} // [] };
    $from_expr->walk_tree(sub {
        my($e) = @_;
        return unless $e->has_newvar;
        my $var = $e->args->[ $e->intro_newvar ];
        my $id = $var->binding->id;
        return if $vmap{$id};
        my $nvar = $var->copy;
        my $nbinding = $nvar->_resolve_new($dict);
        $vmap{$id} = $nvar;
        return;
    });
    my $equate = $from_expr->subst_vars(\%vmap);

    my $repl;
    my($left, $right) = @{ $equate->args };
    if (! $expr->diff($left)) {
        $repl = $right;
    } elsif (! $expr->diff($right)) {
        $repl = $left;
    } else {
        return $self->set_error(sprintf(
            "Neither side of equate %s matches target %s\n",
            $equate->str, $expr->str,
        ));
    }

    my $result = $starting->substitute($loc, $repl);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'equate(%s%s, %s, %s)',
            $self->_linename($line), join('.', @$loc),
            $eqline, $self->_varmap($map));

    return 1;
}

1;
