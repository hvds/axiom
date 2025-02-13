package Axiom::Box;
use strict;
use warnings;

sub new {
    my($class, $derive, $expr) = @_;
    return bless {
        derive => $derive,
        expr => $expr,
        loc => [],
        parent => undef,
    }, $class;
}

sub derive { shift->{derive} }
sub expr { shift->{expr} }
sub loc { shift->{loc} }
sub parent { shift->{parent} }

sub unwrap {
    my($self) = @_;
    my $e = $self->expr;
    my @vars;
    while ($e->type eq 'forall') {
        (my($var), $e) = @{ $e->args };
        push @vars, $var;
    }
    return bless {
        derive => $self->derive,
        parent => $self,
        expr => $e,
        vars => \@vars,
        loc => [ @{ $self->loc }, ((2) x @vars) ],
    }, ref($self);
}

sub assert_type {
    my($self, $type) = @_;
    my $t = $self->expr->type;
    return 1 if $type eq $t;
    return $self->derive->set_error(sprintf(
        '%s needs %s, not %s', $self->derive->rulename, $type, $t
    ));
}

sub arg {
    my($self, $i) = @_;
    my $e = $self->expr;
    my $a = $e->args;
    die sprintf('%s asks for arg %s of %s in %s',
        $self->derive->rulename, $i, $e->type, $e->rawexpr
    ) if $i >= @$a;
    return bless {
        derive => $self->derive,
        parent => $self,
        expr => $a->[$i],
        arg => $i,
        loc => [ @{ $self->loc }, $i + 1 ],
    };
}

sub find_mapping {
    my($self, $other) = @_;
    my $derive = $self->derive;
    my $vars = $self->allvars;
    my($left, $right) = ($self->expr, $other->expr);
    my $map = $derive->find_mapping($left, $right, $vars);
    return $derive->set_error(sprintf(
        '%s cannot find mapping over [%s] from %s to %s',
        $derive->rulename, join(', ', map $_->name, @$vars),
        $left->str, $right->str
    )) unless $map;
    return $map;
}

sub walk_up {
    my($this, $cb) = @_;
    while ($this) {
        $cb->($this);
        $this = $this->parent;
    }
    return;
}

sub allvars {
    my($self) = @_;
    my @vars;
    $self->walk_up(sub { unshift @vars, @{ shift->{vars} // [] } });
    return \@vars;
}

sub rewrap_map {
    my($self, $other, $map) = @_;
    my $expr = $other->expr;
    my $dict = $other->dict_at;
    my %vmap = map {
        my($name, $expr) = ($_, $map->{$_});
        my $var = Axiom::Expr->new({
            type => 'name', args => [ $name ],
        });
        $var->resolve($dict);
        my $id = $var->binding->id;
        +($id => $expr);
    } keys %$map;

    my $repl = $other->rewrap($self);
    $repl = $repl->apply_map($self->clone_dict, \%vmap);
    # TODO: verify no free variables are shadowed
    return ref($self)->new($self->derive, $repl);
}

sub clone_dict {
    my($self) = @_;
    return $self->derive->dict->clone;
}

sub dict_at {
    my($self) = @_;
    my $orig;
    $self->walk_up(sub { $orig = shift->expr });
    return $orig->dict_at($self->loc);
}

sub diffvar {
    my($self, $other) = @_;
    my %known = map +($_->name => $_), @$other;
    return [ grep !$known{ $_->name }, @{ $self->allvar } ];

}

sub match {
    my($self, $other) = @_;
    my($left, $right) = ($self->expr, $other->expr);
    return 1 unless $left->diff($right, 1);
    my $derive = $self->derive;
    return $derive->set_error(sprintf(
        '%s failed to match %s to %s',
        $derive->rulename, $left->str, $right->str
    ));
}

sub wrapall {
    my($self, $expr) = @_;
    for my $var (reverse @{ $self->allvars }) {
        $expr = Axiom::Expr->new({
            type => 'forall',
            args => [ $var->copy, $expr ],
        });
    }
    return $expr;
}

sub rewrap {
    my($self, $other) = @_;
    return $other->wrapall($self->expr->copy);
}

1;
