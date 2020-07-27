package Axiom::Dict;

use strict;
use warnings;

use Axiom::Bind;

=head1 NAME

Axiom::Dict - bindings for function and variable names

=head1 DESCRIPTION

Objects of this class mediate access to names: functions and variables.

Functions are handled as opaque operators. To overcome the ambiguity of
C< x(y+1) > vs. C< f(y+1) >, function names must be declared in advance
via the C< *func > directive. Declaration adds them to the current
dictionary as the only available meaning for their declared name, and
they link to an L<Axiom::Bind::Func> object.

Variables are of two primary types: they may be external to an expression
(ie a free variable) or internal to it (a bound variable). These are
currently linked to L<Axiom::Bind::Var> and L<Axiom::Bind::Local> objects
respectively, and are not opaque: various derivations involve specification
or constraints relating to variables of appropriate types.

All such variables, and the domain and codomain of functions, should be
restricted to a particular well-defined set that can also be used as
part of the reasoning. This is not yet implemented.

External variables retain their meaning ("some specific (but unspecified)
value x") across multiple expressions, from the point of declaration to
the end of that scope. They may be declared explicitly with the C< *var >
directive, or implicitly (eg in a C<condstart> derivation). To achieve
this, we should introduce a new L<Axiom::Dict> instance for a new scope;
that may either start empty (eg for a new file scope, as introduced with
a C<*import> directive), or duplicating the current definitions of the
outer scope for a conditional proof scope (C<condstart> to C<condend>)
with C<< $dict->clone >> or C<< $dict->copy >>. FIXME: work out what
the difference is between these, and remove one of them.

Internal variables retain their meaning only within the subexpression
to which they relate. For example C<sum(v, from, to, expr)> introduces
the variable C<v> into the dictionary only when parsing the subexpression
C<expr>. Their names are mutable, so it should be valid to substitute
an expression such as a sum over C<i> into a part of the expression for
another sum also declared over C<i> - if we need to serialize the result,
the embedded variable should be rendered as something distinct (eg C<j>)
to avoid ambiguity or error.

For derivations we frequently need to parse isolated fragments of
expressions, then relate them to a fragment of one or more well-formed
expressions. To achieve this, we parse all expressions without attempting
to look up the identity of names (other than function names), then put
them through a separate resolution process L<Axiom::Expr/resolve> to
relate each mention of a variable to its unique identity.

=cut

my $typeclass;
BEGIN { $typeclass = Axiom::Bind->typeclass }

sub new {
    my($class) = @_;
    return bless {
        dict => {},
        bind => [],
    }, $class;
}

sub clone {
    my($other) = @_;
    my $self = ref($other)->new;
    my($sd, $sb) = ($self->dict, $self->bind);
    my($od, $ob) = ($other->dict, $other->bind);
    my %tr;
    @$sb = map {
        my $b = $_->clone;
        $tr{$_} = $b;
        $b;
    } @$ob;
    for my $name (keys %$od) {
        $sd->{$name} = $tr{$od->{$name}} // $od->{$name};
    }
    return $self;
}

sub dict { shift->{dict} }
sub bind { shift->{bind} }

sub lookup {
    my($self, $name) = @_;
    return $self->dict->{$name};
}

sub local_name {
    my($self, $name, $bind) = @_;
    return Axiom::Dict::LocalName->new($self->dict, $name, $bind);
}

sub insert {
    my($self, $name, $type) = @_;
    my $id = @{ $self->bind };
    my $class = $typeclass->{$type}
            // die "Unknown bind type '$type' for name $name\n";
    die "Duplicate name '$name'\n"
            if $self->dict->{$name};
    my $bound = $class->new($name, $id);
    push @{ $self->bind }, $bound;
    $self->dict->{$name} = $bound;
    return;
}

sub insert_local {
    my($self, $name) = @_;
    my $dict = $self->dict;
    ++$name while $dict->{$name};
    $self->insert($name, 'local');
    return $dict->{$name};
}

sub introduce {
    my($self, $name) = @_;
    my $id = @{ $self->bind };
    my $class = $typeclass->{'local'};
    my $bound = $class->new($name, $id);
    push @{ $self->bind }, $bound;
    return $bound;
}

sub subsidiary {
    my($self) = @_;
    my $new = ref($self)->new;
    $new->{bind} = $self->bind;
    return $new;
}

sub copy {
    my($self) = @_;
    my $dict = $self->dict;
    my $bind = $self->bind;
    my $copy = ref($self)->new;
    for my $name (sort { $dict->{$a}->id <=> $dict->{$b}->id } keys %$dict) {
        $copy->insert($name, $dict->{$name}->type);
    }
    return $copy;
}

sub str {
    my($self) = @_;
    my %attr;
    my $dict = $self->dict;
    for (@{ $self->bind }) {
        my $name = $_->name;
        push @{ $attr{$_->type} },
                ($dict->{$name} // 0) == $_ ? $name : "($name)";
    }
    return join '',
        map sprintf("%s: %s\n", $_, join ', ', sort @{ $attr{$_} }),
            sort keys %attr;
}

package Axiom::Dict::LocalName {
    sub new {
        my($class, $dict, $name, $bind) = @_;
        my $old = $dict->{$name};
        my $restore = defined($old)
            ? sub { $dict->{$name} = $old }
            : sub { delete $dict->{$name} };
        my $self = bless \$restore, $class;
        $dict->{$name} = $bind;
        return $self;
    }
    DESTROY {
        my($self) = @_;
        $$self->();
    }
};

1;
