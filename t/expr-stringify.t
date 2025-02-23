#!/opt/axiom-d/bin/perl
use strict;
use warnings;
use Test::More;

use lib 'lib';
use Axiom::Expr;

for (
    [ '\Aa:b', [forall => [name => 'a'], [name => 'b'] ] ],
    [ '\Ea:b', [exists => [name => 'a'], [name => 'b'] ] ],
    [ 'a=b', [req => [name => 'a'], [name => 'b'] ] ],
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
    [ [ 'a.(1/b)', 'a/b' ],
            [mullist => [name => 'a'], [recip => [name => 'b'] ] ] ],
    [ [ '1/a.b', '(1/a).b' ],
             [mullist => [recip => [name => 'a'] ], [name => 'b'] ] ],
    [ 'a^2', [pow => [name => 'a'], [integer => 2] ] ],
    [ [ 'a^10', 'a^{10}' ],
            [pow => [name => 'a'], [integer => 10] ] ],
    [ 'a!', [factorial => [name => 'a'] ] ],
    [ [ '\sum_{a=0}^{b}{a}', '\sum_{a=0}^b{a}' ], [sum
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
    [ [ '\prod_{a=0}^{b}{a}', '\prod_{a=0}^b{a}' ], [prod
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
    [ [ '\int_{a=0}^{b}{a}', '\int_{a=0}^b{a}' ], [integral
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
    [ [ '\inteval_{a=0}^{b}{a}', '\inteval_{a=0}^b{a}' ], [inteval
            => [name => 'a'], [integer => 0], [name => 'b'], [name => 'a'] ] ],
    [ 'a+b.c', [pluslist => [name => 'a'],
            [mullist => [name => 'b'], [name => 'c'] ] ] ],
    [ 'a.(b+c)', [mullist => [name => 'a'],
            [pluslist => [name => 'b'], [name => 'c'] ] ] ],
    
) {
    my($expect, $brack) = @$_;
    my $e = Axiom::Expr->_debrack($brack);
    my %match = map +($_ => 1), ref($expect) ? @$expect : $expect;
    my $legend = sprintf 'expr %s', ref($expect) ? $expect->[-1] : $expect;
    ok($match{ $e->str =~ s{ +}{}gr }, $legend);
}

{
    # don't cache bracketing
    my $e1 = Axiom::Expr->_debrack([pluslist => [name => 'a'], [name => 'b'] ]);
    is('a+b', ($e1->str =~ s{ +}{}gr), 'e1 a+b');
    my $e2 = Axiom::Expr->new({
        type => 'mullist',
        args => [ $e1, Axiom::Expr->_debrack([name => 'c']) ],
    });
    is('(a+b).c', ($e2->str =~ s{ +}{}gr), 'e2 (a+b).c');
    my $e3 = Axiom::Expr->new({
        type => 'req',
        args => [ $e1, Axiom::Expr->_debrack([name => 'c']) ],
    });
    is('a+b=c', ($e3->str =~ s{ +}{}gr), 'e3 a+b=c');
}

done_testing();
