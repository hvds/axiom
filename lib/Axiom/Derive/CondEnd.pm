package Axiom::Derive::CondEnd;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::CondEnd - close a Conditional Proof scope

=head1 USAGE

  derive: condend
  rule: [ varmap ]

Ends a conditional proof, constructing a new theorem of the form
C<< \Aa: \Ab: ... expr1 -> expr2 >>. Each of the free variables introduced
in the corresponding C<condstart> is mapped via the I<varmap> to a new
name and made universal; I<expr1> is the expression introduced in the
corresponding C<condstart>; and I<expr2> is the last theorem proven.

=cut

sub rulename { 'condend' }

sub derive_args {
    q{
        <args=(?{ [] })>
    };
}

sub late_resolve {
    my($self, $include) = @_;
    return +($include && $self->context->in_scope) ? 1 : 0;
}

sub _condstart {
    my($self) = @_;
    my $where = $self->context->curline;
    return $self->context->line("$where.0");
}

sub derive {
    my($self, $args) = @_;
    my $target = $self->expr;
    my $te = $target;
    $te = $te->args->[1] while $te->is_quant;
    $te->type eq 'implies' or return $self->set_error(sprintf(
            'Expected implies, not %s', $te->type
    ));

    my $start = $self->_condstart;
    my $base = $start->expr;
    my $dict = $start->dict;
    my $vars = do {
        # FIXME: there must be a better way than parsing it back out of
        # the string
        my $s = $start->rule;
        my($vs) = $s =~ /^condstart\(\{ (.*?) \}\)$/
                or die "Could not match condstart rule '$s'";
        [ map Axiom::Expr->new({
            type => 'name',
            args => [ $_ ],
        }), split /, /, $1 ];
    };
    $_->resolve($dict) for @$vars;
    my $map = $self->find_mapping($base, $te->args->[0], $vars);
    my $list = [];
    for my $fromvar (keys %$map) {
        my $to = $map->{$fromvar};
        $to->type eq 'name' or return $self->set_error(sprintf(
            'Var %s maps to %s, not a variable', $fromvar, $to->str,
        ));
        my $from = Axiom::Expr->new({
            type => 'name',
            args => [ $fromvar ],
        });
        push @$list, { args => [ $from, $to ] };
    }
    return $self->validate([ { args => $list } ]);
}

sub include {
    my($self, $args) = @_;
    $self->scope(-1);
    return $self->null;
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
    $self->validate_diff($result) or return;
    $self->scope(-1);
    $self->rule(sprintf 'condend(%s)', $self->_varmap($map));

    return 1;
}

1;
