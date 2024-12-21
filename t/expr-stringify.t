#!/opt/axiom-d/bin/perl
use strict;
use warnings;
use Test::More;

use lib 'lib';
use Axiom::Expr;

for (
    [ '\Aa:b', [forall => [name => 'a'], [name => 'b'] ] ],
    [ '\Ea:b', [exists => [name => 'a'], [name => 'b'] ] ],
    [ 'a=b', [equals => [name => 'a'], [name => 'b'] ] ],
    [ 'a->b', [implies => [name => 'a'], [name => 'b'] ] ],
    [ '1', [integer => 1] ],
    [ '1/2', [rational => 1, 2] ],
    [ 'a', [name => 'a'] ],
    [ 'E(a)', [function => [name => 'E'], [name => 'a'] ] ],
    [ '-a', [negate => [name => 'a'] ] ],
    [ 'a+b', [pluslist => [name => 'a'], [name => 'b'] ] ],
    [ 'a-b', [pluslist => [name => 'a'], [negate => [name => 'b'] ] ] ],
    [ '-a+b', [pluslist => [negate => [name => 'a'] ], [name => 'b'] ] ],
    [ '1/a', [recip => [name => 'a'] ] ],
    [ 'a.b', [mullist => [name => 'a'], [name => 'b'] ] ],
    [ 'Ta/b', [mullist => [name => 'a'], [recip => [name => 'b'] ] ] ],
    [ 'a.(1/b)', [mullist => [name => 'a'], [recip => [name => 'b'] ] ] ],
# ?TODO
#   [ '1/a.b', [mullist => [recip => [name => 'a'] ], [name => 'b'] ] ],
    [ '(1/a).b', [mullist => [recip => [name => 'a'] ], [name => 'b'] ] ],
    [ 'a^2', [pow => [name => 'a'], [integer => 2] ] ],
# TODO
#   [ 'a^{10}', [pow => [name => 'a'], [integer => 10] ] ],
    [ 'a^10', [pow => [name => 'a'], [integer => 10] ] ],
    [ 'a!', [factorial => [name => 'a'] ] ],
# TODO
#   [ '\sum_{a=0}^b{a}', [sum
    [ '\sum_{a=0}^{b}{a}', [sum
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
#   [ '\prod_{a=0}^b{a}', [sum
    [ '\prod_{a=0}^{b}{a}', [prod
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
#   [ '\int_{a=0}^b{a}', [sum
    [ '\int_{a=0}^{b}{a}', [integral
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
#   [ '\inteval_{a=0}^b{a}', [sum
    [ '\inteval_{a=0}^{b}{a}', [inteval
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
    [ 'a+b.c', [pluslist => [name => 'a'],
            [mullist => [name => 'b'], [name => 'c'] ] ] ],
    [ 'a.(b+c)', [mullist => [name => 'a'],
            [pluslist => [name => 'b'], [name => 'c'] ] ] ],
    
) {
    my($expect, $brack) = @$_;
    my $e = _make_brack($brack);
    my $todo = ($expect =~ s/^T//) ? 1 : 0;
    TODO: {
        local $TODO = 'TODO' if $todo;
        is(($e->str =~ s{ +}{}gr), $expect,
                sprintf 'expr %s%s', $expect, $todo ? ' (TODO)' : '');
    }
}

{
    # don't cache bracketing
    my $e1 = _make_brack([pluslist => [name => 'a'], [name => 'b'] ]);
    is('a+b', ($e1->str =~ s{ +}{}gr), 'e1 a+b');
    my $e2 = Axiom::Expr->new({
        type => 'mullist',
        args => [ $e1, _make_brack([name => 'c']) ],
    });
    is('(a+b).c', ($e2->str =~ s{ +}{}gr), 'e2 (a+b).c');
    my $e3 = Axiom::Expr->new({
        type => 'equals',
        args => [ $e1, _make_brack([name => 'c']) ],
    });
    is('a+b=c', ($e3->str =~ s{ +}{}gr), 'e3 a+b=c');
}

done_testing();

sub _make_brack {
    my($b) = @_;
    my($type, @args) = @$b;
    return Axiom::Expr->new({
        type => $type,
        args => [ map {
            ref($_) ? _make_brack($_) : $_
        } @args ],
    });
}

1;
