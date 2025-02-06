package Axiom::Derive::Specify;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Specify - fix a specific value for a universal quantifier

=head1 USAGE

  derive: specify ( line? )
  rule: [ line, var, expr ]

Given a prior theorem of the form C< \Aa: \Ab: P(a, b) >, can construct
new theorems such as C< P(x, y) >, C< \Aa: \Ac: \Ad: P(a, c+d-e) > or
C< \Aa: \Ab: P(b, a) >.

=head1 RESTRICTIONS

Values specified for each variable must be a number over their entire
range.

New quantified variables may not shadow free variables in the original
theorem. New free variables may not shadow unspecified quantified
variables in the original theorem.

Quantified variables at the top level are expected to appear in alphabetical
order both before and after, derivation may fail if this is not the case.

=cut

sub rulename { 'specify' }

sub derive_args {
    (1, q{ <[args=line]>? });
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);

    my $fo = Axiom::ExprVars->new($starting);
    my $to = Axiom::ExprVars->new($target);
    my $fe = $fo->expr;
    my $te = $to->expr;
    my $fv = $fo->allvar;
    my $map = $self->find_mapping($fe, $te, $fv);

    # if we didn't find it, maybe one side has been simplified to the point
    # we no longer recognise it
    if (!$map && !$fe->is_atom && $fe->type eq $te->type) {
        my $fa = $fe->args;
        my $ta = $te->args;
        if (@$fa == @$ta) {
            for (0 .. $#$fa) {
                $map = $self->find_mapping($fa->[$_], $ta->[$_], $fv);
                last if $map;
            }
        }
    }
    return $self->set_error("don't know how to derive this specify")
            unless $map;

    my %vmap = (args => [
        map +{ args => [ $_->copy, $map->{$_->name} ] }, @$fv,
    ]);
    return $self->validate([ $line, \%vmap ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $map) = @$args;
    my $starting = $self->line($line);
    $starting->resolve($self->dict);
    my $target = $self->expr;
    $target->resolve($self->dict);

    my $fo = Axiom::ExprVars->new($starting);
    my $to = Axiom::ExprVars->new($target);

    # find the binding id of each variable to be replaced
    my $dict = $fo->dict_at;
    my %vmap = map {
        my($var, $expr) = @{ $_->{args} };
        $var->resolve($dict);
        my $id = $var->binding->id;
        +($id => $expr);
    } @{ $map->{args} // [] };

    # Replace the quantifier wrappings with those of the target
    my $expr = $fo->rewrap($to);
    $expr->apply_map($self->dict->clone, \%vmap);
    $self->validate_diff($expr) or return;
    $self->rule(sprintf 'specify(%s%s)',
            $self->_linename($line), $self->_varmap($map));

    return 1;
}

# TODO: work out whether this is a real class that should have its own home,
# or a helper class specific to ::Specify that should have a local name here.
package Axiom::ExprVars {
    sub new {
        my($class, $expr) = @_;
        return bless {
            orig => $expr,
        }, $class;
    }
    sub orig { shift->{orig} }
    sub _findtop {
        my($self) = @_;
        my $e = $self->orig;
        my(@loc, @anyvar, @allvar);
        while ($e->is_quant) {
            my $t = $e->type;
            (my($v), $e) = @{ $e->args };
            push @loc, 2;
            push @anyvar, [ $t, $v ];
            push @allvar, $v if $t eq 'forall';
        }
        @$self{qw{ expr loc anyvar allvar }} = ($e, \@loc, \@anyvar, \@allvar);
        return;
    }
    for my $attr (qw{ expr loc anyvar allvar }) {
        my $sub = sub {
            my($self) = @_;
            $self->_findtop unless $self->{$attr};
            return $self->{$attr};
        };
        no strict 'refs';
        *$attr = $sub;
    }
    sub dict_at {
        my($self) = @_;
        return $self->orig->dict_at($self->loc);
    }
    sub diffvar {
        my($self, $other) = @_;
        my %known = map +($_->name => $_), @$other;
        return [ grep !$known{ $_->name }, @{ $self->allvar } ];
    }
    sub wrapall {
        my($self, $expr) = @_;
        for (reverse @{ $self->anyvar }) {
            my($type, $var) = @$_;
            $expr = Axiom::Expr->new({
                type => $type,
                args => [ $var->copy, $expr ],
            });
        }
        return $expr;
    }
    sub rewrap {
        my($self, $other) = @_;
        return $other->wrapall($self->expr->copy);
    }
};

1;
