package Axiom::Derive::Give;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Give - apply a \given clause

=head1 USAGE

  derive: give ( line? )
  rule: [ line, loc ]

Given a location in a prior theorem with one or more constraints provided
by outer iterators or given clauses, add a given clause to a selected
expression duplicating one or more of those constraints.

=cut

sub rulename { 'give' }

sub derive_args {
    q{
        (?: \(
            <[args=optline]>
            (?: \s* <[args=line]> )?
        \) )?
        (?{
            $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 1);
            $MATCH{args}[0] //= '';
        })
    };
}

sub derive {
    my($self, $args) = @_;
    my($line, $with) = @$args;
    my $source = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);
    my $loc = $source->diff($target, 1);
    return $self->validate([ $line, $loc, $with ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $with) = @$args; 
    my $source = $self->line($line);
    my $target = $self->expr;
    $_->resolve($self->dict) for ($source, $target);

    my $se = $source->locate($loc);
    my $te = $target->locate($loc);

    return $self->set_error(sprintf(
        'expect target to be type given, not %s', $te->type
    )) unless $te->type eq 'given';
    my($tg, $te2) = @{ $te->args };
    return $self->set_error(sprintf(
        'expect target to wrap the source, but have %s versus %s',
        $se->str, $te2->str
    )) if $se->diff($te2, 1);

    return undef unless $self->check_range($tg, $source, $loc, $with);
    my $repl = Axiom::Expr->new({
        type => 'given',
        args => [ $tg->copy, $se->copy ],
    });
    $repl->resolve($source->dict_at($loc));

    my $result = $source->substitute($loc, $repl);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'give(%s%s)',
            $self->_linename($line), join('.', @$loc));

    return 1;
}

1;
