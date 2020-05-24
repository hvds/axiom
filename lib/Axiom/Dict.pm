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

sub dict { shift->{dict} }
sub bind { shift->{bind} }

sub lookup {
    my($self, $name) = @_;
    return $self->dict->{$name};
}

sub insert {
    my($self, $name, $type) = @_;
    my $index = @{ $self->bind };
    my $class = $typeclass->{$type}
            // die "Unknown bind type '$type' for name $name\n";
    die "Duplicate name '$name'\n"
            if $self->dict->{$name};
    my $bound = $class->new($name, $index);
    push @{ $self->bind }, $bound;
    $self->dict->{$name} = $bound;
    return;
}

sub introduce {
    my($self, $name) = @_;
    my $index = @{ $self->bind };
    my $class = $typeclass->{'local'};
    my $bound = $class->new($name, $index);
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

1;
