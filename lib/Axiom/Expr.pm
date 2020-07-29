package Axiom::Expr;

use strict;
use warnings;

use Carp qw{ confess };

my %listtype = map +($_ => 1), qw{ pluslist mullist };

my %classtype = (
    integer => 'Axiom::Expr::Const',
    name => 'Axiom::Expr::Name',
    forall => 'Axiom::Expr::Quant',
);

sub new {
    my($class, $hash) = @_;
    my($type, $args) = @$hash{qw{ type args }};
    if ($listtype{$type}) {
        return $args->[0] if @$args == 1;
        $args = [ map {
            $_->type eq $type ? @{ $_->args } : $_
        } @$args ];
    }
    my $targclass = $classtype{$type} // 'Axiom::Expr';
    $class = $targclass unless $class->isa($targclass);
    return bless {
        type => $type,
        args => $args,
    }, $class;
}

sub args { shift->{args} }
sub type { shift->{type} }
sub is_atom { 0 }
sub is_const { 0 }
sub is_quant { 0 }
sub is_list { $listtype{ shift->type } }
sub has_newvar { 0 }

sub is_neg {
    my($self) = @_;
    my $type = $self->type;
    return $type eq 'negate' || (
        $type eq 'mullist' && $self->args->[0]->is_neg
    );
}
sub negate {
    my($self) = @_;
    my $type = $self->type;
    if ($type eq 'negate') {
        return $self->args->[0]->copy;
    } elsif ($type eq 'mullist') {
        my $other = $self->copy;
        $other->args->[0] = $other->args->[0]->negate;
        return $other;
    }
    return Axiom::Expr->new({
        type => 'negate',
        args => [ $self->copy ],
    });
}

sub _clean {
    my($self) = @_;
    return undef if $self->is_atom;
    my $type = $self->type;
    my $args = $self->args;
    for (@$args) {
        my $new = $_->_clean // next;
        $_ = $new;
    }
    if ($type eq 'mullist') {
        my($const) = grep $args->[$_]->is_const, 0 .. $#$args;
        return undef unless defined $const;
        my $rat = $args->[ $const ]->args->[0];
        if ($rat == 1) {
            # a.1.b -> a.b
            splice @$args, $const, 1;
            return $self;
        }
        return undef;
    }
    return undef;
}

sub clean {
    my($self) = @_;
    $self = $self->copy;
    return $self->_clean // $self;
}

sub copy {
    my($self) = @_;
    return $self->copy_with(sub { undef });
}

sub copy_with {
    my($self, $with) = @_;
    return $with->($self) // ref($self)->new({
        type => $self->type,
        args => [ map $_->copy_with($with), @{ $self->args } ],
    });
}

sub dict_at {
    my($self, $loc) = @_;
    my $dict = $self->{dict}->clone;
    return $self->_dict_at($dict, [ @$loc ]);
}

sub _dict_at {
    my($self, $dict, $loc) = @_;
    return $dict unless @$loc;
    my $this = shift(@$loc) - 1;
    return $self->args->[$this]->_dict_at($dict, $loc);
}

sub substitute {
    my($self, $location, $replace) = @_;
    return $replace unless @$location;
    my($off, @subloc) = @$location;
    my $args = $self->args;
    my @copy = map {
        $_ == $off - 1
            ? (@subloc
                ? $args->[$_]->substitute(\@subloc, $replace)
                : (($replace->is_list && $self->type eq $replace->type)
                    ? @{ $replace->args }
                    : $replace
                )
            )
            : $args->[$_]->copy
    } 0 .. $#$args;
    return ref($self)->new({ type => $self->type, args => \@copy });
}

sub subst_vars {
    my($self, $map) = @_;
    return $self->copy_with(sub {
        my($other) = @_;
        return undef unless $other->type eq 'name';
        my $oi = $other->binding->id;
        return undef unless $map->{$oi};
        return $map->{$oi}->copy;
    });
}

sub walk_tree {
    my($self, $cb) = @_;
    $cb->($self);
    unless ($self->is_atom) {
        $_->walk_tree($cb) for @{ $self->args };
    }
    return;
}

sub _diff {
    my($self, $other, $map) = @_;
    $map //= {};
    $self->type eq $other->type or return [];
    my($sa, $oa) = ($self->args, $other->args);
    @$sa == @$oa or return [];
    my $diff;
    for my $i (0 .. $#$sa) {
        my $_diff = $sa->[$i]->_diff($oa->[$i], $map) // next;
        return [] if $diff;
        $diff = [ $i + 1, @{ $_diff } ];
    }
    return $diff;
}

sub diff {
    my($self, $other, $pure) = @_;
    my $map = {};
    my $where = $self->_diff($other, $map);
    return undef unless $where;
    return $where if $pure;
    return undef unless $self->clean->_diff($other->clean, $map);
    return $where;
}

sub _resolve {
    my($self, $dict) = @_;
    $_->_resolve($dict) for @{ $self->args };
    return;
}

sub resolve {
    my($self, $dict) = @_;
    $dict = $dict->clone;   # not copy, must preserve ids
    $self->{dict} = $dict;  # store at top level of expr only
    $self->_resolve($dict);
    return;
}

package Axiom::Expr::Const {
    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        my $type = 'integer';
        my $args = [ $hash->{args}[0] ];
        return bless { type => $type, args => $args }, $class;
    }
    sub is_const { 1 }
    sub is_atom { 1 }
    sub is_neg { shift->args->[0] < 0 }
    sub negate {
        my($self) = @_;
        my $other = $self->copy;
        $other->args->[0] = -$other->args->[0];
        return $other;
    }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // ref($self)->new({
            type => $self->type,
            args => [ @{ $self->args } ],
        });
    }
    sub _diff {
        my($self, $other, $map) = @_;
        my $type = $self->type;
        return [] unless $type eq $other->type;
        my($sa, $oa) = ($self->args, $other->args);
        ($sa->[0] == $oa->[0]) or return [];
        return undef;
    }
    sub _resolve { }
};

package Axiom::Expr::Name {
    use Carp qw{ confess };

    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        return bless { type => 'name', args => $hash->{args} }, $class;
    }
    sub is_atom { 1 }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // do {
            my $other = ref($self)->new({
                type => $self->type,
                args => [ @{ $self->args } ],
            });
            $other->bind($self->binding);
            $other;
        };
    }
    sub _diff {
        my($self, $other, $map) = @_;
        return [] unless $self->type eq $other->type
                && $self->bindtype eq $other->bindtype;
        my($si, $oi) = map $_->binding->id, ($self, $other);
        if (defined $map->{$si}) {
            return [] unless $oi == $map->{$si};
        } else {
            return [] unless $self->name eq $other->name || $si == $oi;
            return [] if defined $map->{"r$oi"};
            $map->{$si} = $oi;
            $map->{"r$oi"} = $si;
        }
        return undef;
    }
    sub name { shift->args->[0] }
    sub bind {
        my($self, $binding) = @_;
        $self->{binding} = $binding;
        return;
    }
    sub binding { shift->{binding} }
    sub bindtype {
        my($self) = @_;
        return $self->binding->type;
    }
    sub _resolve {
        my($self, $dict) = @_;
        my $binding = $self->binding;
        return if $binding && $binding->is_func;
        $binding = $dict->lookup($self->name);
        $self->bind($binding);
        return;
    }
    sub _resolve_new {
        my($self, $dict) = @_;
        my $binding = $dict->introduce($self->name);
        $self->bind($binding);
        return $binding;
    }
};

package Axiom::Expr::Quant {
    our @ISA = qw{Axiom::Expr};
    sub is_quant { 1 }
    sub has_newvar { 1 }
    sub intro_newvar { 0 }
    sub affect_newvar { 1 }
    sub _resolve {
        my($self, $dict) = @_;
        my($var, $expr) = @{ $self->args };
        my $bind = $var->_resolve_new($dict);
        my $local = $dict->local_name($var->name, $bind);
        $expr->_resolve($dict);
        return;
    }
    sub _dict_at {
        my($self, $dict, $loc) = @_;
        return $dict unless @$loc;
        my $this = shift(@$loc) - 1;
        my $result = $self->args->[$this]->_dict_at($dict, $loc);
        if ($this == 1) {
            my $var = $self->args->[0];
            $result->dict->{$var->name} = $var->binding;
        }
        return $result;
    }
};

1;
