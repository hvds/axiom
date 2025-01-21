package Axiom::Derive::Add;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Add - add an expression to both sides of a relation

=head1 USAGE

  derive: add ( line? )
  rule: [ line, expr ]

Given a prior theorem of the form C< P = Q >, constructs the new theorem
C< P + expr = Q + expr >.

The relation may be wrapped in an arbitrary number of quantifiers.

=cut

sub rulename { 'add' }

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
    my $from_base = $self->line($line);
    my $from = $from_base;
    my $to = $self->expr;
    my($floc, $tloc) = ([], []);
    while ($from->is_quant) {
        push @$floc, 2;
        $from = $from->args->[1];
    }
    $from->is_relation
            or return $self->set_error('No relation to derive from');
    while ($to->is_quant) {
        push @$tloc, 2;
        $to = $to->args->[1];
    }
    $to->is_relation
            or return $self->set_error('No relation to derive to');
    my $expr = Axiom::Expr->new({
        type => 'pluslist',
        args => [
            $to->args->[0]->copy,
            Axiom::Expr->new({
                type => 'negate',
                args => [ $from->args->[0]->copy ],
            }),
        ],
    });
    my $dict = $self->expr->dict_at($tloc);
    $expr->resolve($dict);
    $expr = $expr->clean;
    return $self->validate([ $line, $expr ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $expr) = @$args;
    my $starting = $self->line($line);

    my $loc = [];
    my @quant;
    my %seen;
    my $rel = $starting;
    while ($rel->is_quant) {
        push @$loc, 2;
        my($var, $re) = @{ $rel->args };
        push @quant, [ $rel->type, $var->name ];
        $seen{$var->name} = 1;
        $rel = $re;
    }
    $rel->is_relation or return $self->set_error(sprintf(
        "don't know how to add to a %s\n", $rel->type
    ));

    $expr->walk_tree(sub {
        my($e) = @_;
        if ($e->has_newvar) {
            my $v = $e->args->[ $e->intro_newvar ];
            $seen{$v->name} = 1;
        }
        return unless $e->type eq 'name' && $e->bindtype eq 'local';
        my $n = $e->name;
        return if $seen{$n}++;
        push @quant, [ 'forall', $n ];
    });

    my $result = Axiom::Expr->new({
        type => $rel->type,
        args => [ map Axiom::Expr->new({
            type => 'pluslist',
            args => [ $_->copy, $expr->copy ],
        }), @{ $rel->args } ],
    });

    for (sort { $b->[1] cmp $a->[1] } @quant) {
        my($type, $name) = @$_;
        $result = Axiom::Expr->new({
            type => $type,
            args => [
                Axiom::Expr->new({ type => 'name', args => [ $name ] }),
                $result,
            ],
        });
    }

    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'add(%s%s)', $self->_linename($line), $expr->rawexpr);
    return 1;
}

1;
