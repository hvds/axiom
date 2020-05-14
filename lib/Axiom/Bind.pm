package Axiom::Bind;

use v5.10;
use strict;
use warnings;

sub new {
    my($class, $name, $index) = @_;
    return bless {
        name => $name,
        index => $index,
    }, $class;
}
sub name { shift->{name} }
sub index { shift->{'index'} }
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
};
package Axiom::Bind::Local {
    our @ISA = qw{Axiom::Bind};
    sub type { 'local' }
};

1;
