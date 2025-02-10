package Axiom::Box;
use strict;
use warnings;

sub new {
    my($class, $expr) = @_;
    return bless {
        orig => $expr,
    }, $class;
}

sub orig { shift->{orig} }

for my $attr (qw{ expr loc anyvar allvar }) {
    my $sub = sub {
        my($self) = @_;
        $self->_findtop unless $self->{$attr};
        return $self->{$attr};
    };
    no strict 'refs';
    *$attr = $sub;
}

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

1;
