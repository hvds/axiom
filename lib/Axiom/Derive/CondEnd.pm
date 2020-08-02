package Axiom::Derive::CondEnd;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::CondEnd - close a Conditional Proof scope

=head1 USAGE

  condend ( varmap )

Ends a conditional proof, constructing a new theorem of the form
C<< \Aa: \Ab: ... expr1 -> expr2 >>. Each of the free variables introduced
in the corresponding C<condstart> is mapped via the I<varmap> to a new
name and made universal; I<expr1> is the expression introduced in the
corresponding C<condstart>; and I<expr2> is the last theorem proven.

=cut

sub rulename { 'condend' }

sub rulere { <<'RE' }
    <rule: condend> condend \( <[args=varmap]> \)
RE

sub derivere { <<'RE' }
    <rule: condend> condend <args=(?{ [] })>
RE

sub _condstart {
    my($self) = @_;
    my $where = $self->context->curline;
    return $self->context->line("$where.0");
}

sub derive {
    my($self, $args) = @_;
    my $target = $self->expr;
    my $te = $target;
    my @to;
    while ($te->is_quant) {
        push @to, $te->args->[0]->name;
        $te = $te->args->[1];
    }

    my @from = do {
        my $dict2 = _condstart($self)->dict;
        my $dict1 = $self->context->scope_dict;
        my %known = %{ $dict2->dict };
        delete $known{$_} for keys %{ $dict1->dict };
        sort { $known{$a}->id <=> $known{$b}->id } keys %known;
    };

    if (@from == 1 && @to == 1) {
        my $from = Axiom::Expr->new({ type => 'name', args => [ $from[0] ] });
        $from->{''} = $from[0];
        my $to = Axiom::Expr->new({ type => 'name', args => [ $to[0] ] });
        $to->{''} = $to[0];
        return [ { args => [ { args => [ $from, $to ] } ] } ];
    }
    die "not yet";
}

sub validate {
    my($self, $args) = @_;
    my($map) = @$args;

    my $cond = _condstart($self)->expr;
    my %vmap = map {
        my($var, $expr) = @{ $_->{args} };
        $var->resolve($self->dict);
        +($var->binding->id => $expr)
    } @{ $map->{args} // [] };

    my $result = Axiom::Expr->new({
        type => 'implies',
        args => [
            $cond->copy,
            $self->working->copy,
        ],
    })->subst_vars(\%vmap);
    for my $var (reverse sort values %vmap) {
        $result = Axiom::Expr->new({
            type => 'forall',
            args => [ $var, $result ],
        });
    }

    my $dict = $self->context->scope_dict;
    $result->resolve($dict);
    $self->working($result);
    $self->scope(-1);

    push @{ $self->rules }, sprintf 'condend(%s)', $self->_varmap($map);

    return 1;
}

1;
