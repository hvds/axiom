package Axiom::Derive;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

sub new {
    my($class, $context) = @_;
    my $self = bless {
        dict => $context->dict->copy,
        working => $context->last_expr,
        expa => $context->expr('exp.A2b'),
    };
    return $self;
}

sub derive {
    my($self, $args) = @_;
    my $target = $self->{expr};
    $target->resolve($self->{dict});

    my $var = $self->{expa}->args->[0];
    my $loc = [ 2, 2, 2 ];
    my $map = { args => [ { args => [ $var->copy, ::_ei(1) ] } ] };

    my $starting = $self->{working}->copy;
    $starting->resolve($self->{dict});
    my $dict = $starting->dict_at([]);

    my $from = $self->{expa};
    my $from_expr = $from->args->[1];
    my $from_loc = [ 2 ];
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

    my $repl = $equate->args->[1];
    my $result = $starting->substitute($loc, $repl);
    die "cannot derive: diff\n"
            if $result->diff($target);
    return 1;
}

1;
