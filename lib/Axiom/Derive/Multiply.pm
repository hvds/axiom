package Axiom::Derive::Multiply;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Multiply - multiply both sides of a relation by some expr

=head1 USAGE

  derive: multiply ( line? )
  rule: [ line, expr ]

Given a prior theorem of the form C< P = Q >, constructs the new theorem
C< P . expr = Q . expr >. If the prior theorem is an inequality, this is
permitted only if the sign of the multiplying expression is known.

=cut

sub rulename { 'multiply' }

sub derive_args {
    q{
        (?: \( <[args=optline]> (?: \s* <.ValueToken> \s* <[args=Expr]> )? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} // '';
        })
    };
}

sub derive {
    my($self, $args) = @_;
    my($line, $value) = @$args;
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
    $from->is_relation
            or return $self->set_error('No relation to derive from');
    $to->is_relation
            or return $self->set_error('No relation to derive to');
    my $expr = $value // do {
        my $v = $to->args->[0];
        my $i = ($v->is_const && $v->rat == 0) ? 1 : 0;
        Axiom::Expr->new({
            type => 'mullist',
            args => [
                $to->args->[$i]->copy,
                Axiom::Expr->new({
                    type => 'recip',
                    args => [ $from->args->[$i]->copy ],
                }),
            ],
        });
    };
    $expr->resolve($from_base->dict_at($loc));
    $expr = $expr->clean;
    return $self->validate([ $line, $expr ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $expr) = @$args;
    my $starting = $self->line($line);

    my $loc = [];
    my $rel = $starting;
    while ($rel->is_quant) {
        push @$loc, 2;
        $rel = $rel->args->[1];
    }
    $rel->is_relation or return $self->set_error(sprintf(
        "don't know how to multiply a %s", $starting->type,
    ));

    my $targ_type;
    if ($rel->type eq 'req') {
        $targ_type = 'req';
    } elsif ($expr->is_const) {
        $targ_type = ($expr->rat < 0) ? $rel->inverse_type : $rel->type;
    } else {
        # TODO support 'with' argument to constrain the expr
        return $self->set_error(sprintf(
            "can't multiply inequality by non-const '%s'", $expr->str
        ));
    }

    my $repl = Axiom::Expr->new({
        type => $targ_type,
        args => [ map Axiom::Expr->new({
            type => 'mullist',
            args => [ $_->copy, $expr->copy ],
        }), @{ $rel->args } ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'multiply(%s%s)',
            $self->_linename($line), $expr->rawexpr);

    return 1;
}

1;
