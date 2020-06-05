package Axiom::Dict;

use strict;
use warnings;

use Axiom::Bind;

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
    for my $name (keys %$dict) {
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
