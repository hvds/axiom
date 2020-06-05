package Axiom::Bind;

use v5.10;
use strict;
use warnings;

sub new {
    my($class, $name, $id) = @_;
    return bless {
        name => $name,
        id => $id,
    }, $class;
}
sub clone {
    my($self) = @_;
    return ref($self)->new($self->name, $self->id);
}

sub name { shift->{name} }
sub id { shift->{'id'} }
sub is_func { 0 }
sub typeclass {
    return state $typeclass = {
        map +($_->type => $_), qw{
            Axiom::Bind::Var Axiom::Bind::Func Axiom::Bind::Local
        }
    };
}

package Axiom::Bind::Var {
    our @ISA = qw{Axiom::Bind};
    sub type { 'var' }
};
package Axiom::Bind::Func {
    our @ISA = qw{Axiom::Bind};
    sub type { 'func' }
    sub is_func { 1 }
};
package Axiom::Bind::Local {
    our @ISA = qw{Axiom::Bind};
    sub type { 'local' }
};

1;
