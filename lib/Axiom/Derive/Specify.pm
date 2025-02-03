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

    # Walk the expr to do the replacements, resolving as we go.
    # Variables getting introduced should be resolved but not replaced;
    # others should be replaced if their old resolution matches a vmap id,
    # else get resolved normally. Replacement exprs should be resolved but
    # not recursively replaced, and we must verify that each replacement
    # for a given id resolves the same way as the first.

    {
        my %rmap;
        my $dict = $self->dict->clone;
        my($resolve, $walk);
        $resolve = sub {
            my($e, $fixed, $known) = @_;
            if ($e->has_newvar) {
                my $in = $e->intro_newvar;
                my $an = $e->affect_newvar;
                my $args = $e->args;
                my $fargs = $fixed->args;
                for (0 .. $#$args) {
                    next if $_ == $in || $_ == $an;
                    $resolve->($args->[$_], $fargs->[$_], $known);
                }
                my $var = $args->[$in];
                my $binding = $var->_resolve_new($dict);
                if ($known) {
                    $fixed->args->[$in]->binding->id == $binding->id
                            or die sprintf "binding mismatch at %s %s",
                                    $e->type, $var->name;
                } else {
                    $fixed->args->[$in]->bind($binding);
                }
                my $local = $dict->local_name($var->name, $binding);
                $resolve->($args->[$an], $fargs->[$an], $known);
            } elsif ($e->type eq 'name') {
                $e->_resolve($dict);
                my $binding = $e->binding;
                return if $binding->is_func;
                if ($known) {
                    $fixed->binding->id == $binding->id
                            or die sprintf "binding mismatch on %s", $e->name;
                } else {
                    $fixed->bind($binding);
                }
            } elsif (!$e->is_const) {
                my $args = $e->args;
                my $fargs = $fixed->args;
                $resolve->($args->[$_], $fargs->[$_], $known) for 0 .. $#$args;
            }
        };
        $walk = sub {
            my($eref, $given) = @_;
            my $e = $$eref;
            if ($e->has_newvar) {
                my $in = $e->intro_newvar;
                my $an = $e->affect_newvar;
                my $args = $e->args;
                for (0 .. $#$args) {
                    next if $_ == $in || $_ == $an;
                    $walk->(\$args->[$_], $given);
                }
                my $var = $args->[$in];
                my $binding = $var->_resolve_new($dict);
                my $local = $dict->local_name($var->name, $binding);
                $walk->(\$args->[$an], $given);
            } elsif ($e->type eq 'name') {
                # it is not being introduced, so it must get resolved or
                # replaced
                my $binding = $e->binding;
                return if $binding->is_func;
                my $id = $binding->id;
                if ($vmap{$id}) {
                    $e = $vmap{$id}->copy;
                    my $fixed = $rmap{$id} // $e->copy;
                    my $known = $rmap{$id} ? 1 : 0;
                    $resolve->($e, $fixed, $known);
                    return $self->set_error(sprintf(
                        "multiplicand %s is not a number", $fixed->str
                    )) unless $known || $fixed->is_number($given);
                    $$eref = $e;
                } else {
                    $e->_resolve($dict);
                }
            } elsif ($e->type eq 'given') {
                my($local_given, $expr) = @{ $e->args };
                $walk->($local_given, $given);
                $walk->($expr, $local_given);
            } elsif (!$e->is_const) {
                my $args = $e->args;
                $walk->(\$args->[$_], $given) for 0 .. $#$args;
            }
            return 1;
        };
        $walk->(\$expr) // return;
    }

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
