#!/opt/axiom-d/bin/perl
use strict;
use warnings;
use Test::More;

use lib 'lib';

# test good cases
test($_, 1, 1) for ([
    q{negate simple 2-part},
    q{*var a}, q{axiom: -(a+a^2) = 0}, q{unarydistrib: -a-a^2 = 0}
], [
    q{negate simple 3-part},
    q{*var a}, q{axiom: -(a+a^2+a^3) = 0}, q{unarydistrib: -a-a^2-a^3 = 0}
], [
    q{negate reorder 3},
    q{*var a}, q{axiom: -(a+a^2+a^3) = 0}, q{unarydistrib: -a^3-a^2-a = 0}
], [
    q{negate group 1+2 with reorder},
    q{*var a}, q{axiom: -(a+a^2+a^3) = 0}, q{unarydistrib: -(a^3+a^2)-a = 0}
], [
    q{negate group 2+2},
    q{*var a}, q{axiom: -(a+a^2+a^3+a^4) = 0},
    q{unarydistrib: -(a+a^3)-(a^4+a^2) = 0}
], [
    q{negate deeper simple},
    q{*var a}, q{axiom: a^{-(a+a^2)} = 0}, q{unarydistrib: a^{-a-a^2} = 0}
], [
    q{negate deeper complex},
    q{*var a}, q{axiom: a^{-(a+a^2+a^3+a^4)} = 0},
    q{unarydistrib: a^{-(a+a^3)-(a^4+a^2)} = 0}
], [
    q{negate in list simple},
    q{*var a}, q{axiom: a-(a^2+a^3) = 0}, q{unarydistrib: a-a^2-a^3 = 0}
], [
    q{negate in list complex},
    q{*var a}, q{axiom: a-(a+a^2+a^3+a^4) = 0},
    q{unarydistrib: a-(a+a^3)-(a^4+a^2) = 0}
], [
    q{negate with grouping},
    q{*var a}, q{axiom: a+2a^3-(a^2+a^3+a^4) = 0},
    q{unarydistrib: a-a^2+a^3-a^4 = 0}
], [
    q{negate with cancellation},
    q{*var a}, q{axiom: a+a^3-(a^2+a^3+a^4) = 0},
    q{unarydistrib: a-a^2-a^4 = 0}
], [
    q{negate in mullist},
    q{*var a}, q{axiom: -(a+1)(a+2) = 0},
    q{unarydistrib: (a+1)(-a-2) = 0}
], [
    q{forall simple},
    q{axiom: \Ax: (x = 1) -> (2x = 2)},
    q{unarydistrib: (\Ax: x = 1) -> (\Ax: 2x = 2)},
], [
    q{forall all of 3},
    q{axiom: \Aa: \Ab: \Ac: (a+b = c) -> (a = c-b)},
    q{unarydistrib: (\Aa: \Ab: \Ac: a+b = c) -> (\Aa: \Ab: \Ac: a = c-b)}
], [
    q{forall 2 of 3},
    q{axiom: \Aa: \Ab: \Ac: (a+b = c) -> (a = c-b)},
    q{unarydistrib: \Ab: (\Aa: \Ac: a+b = c) -> (\Aa: \Ac: a = c-b)},
], [
    q{forall 1 of 3},
    q{axiom: \Aa: \Ab: \Ac: (a+b = c) -> (a = c-b)},
    q{unarydistrib: \Aa: \Ac: (\Ab: a+b = c) -> (\Ab: a = c-b)},
], [
    q{embedded simple},
    q{axiom: \Ax: (x = 0) -> (\Ay: (y = 0) -> (x+y = 0))},
    q{unarydistrib: \Ax: (x = 0) -> ((\Ay: y = 0) -> (\Ay: (x+y = 0)))},
], [
    q{given simple},
    q{*var y}, q{axiom: 2y = y + \given_{\Ax: (x = 1) -> (2x = 2)}{y}},
    q{unarydistrib: 2y = y + \given_{(\Ax: x = 1) -> (\Ax: 2x = 2)}{y}},
], [
    q{sum simple 2-part},
    q{axiom: \sum_{x=0}^1{x+1} = 0},
    q{unarydistrib: \sum_{x=0}^1{x} + \sum_{x=0}^1{1} = 0}
], [
    q{integral simple 2-part},
    q{axiom: \int_{x=0}^1{x+1} = 0},
    q{unarydistrib: \int_{x=0}^1{x} + \int_{x=0}^1{1} = 0}
], [
    q{inteval simple 2-part},
    q{axiom: \inteval_{x=0}^1{x+1} = 0},
    q{unarydistrib: \inteval_{x=0}^1{x} + \inteval_{x=0}^1{1} = 0}
], [
    # expect sum/integral/inteval all to use the same code
    q{sum simple 3-part},
    q{axiom: \sum_{x=0}^1{x^2+x+1} = 0},
    q{unarydistrib: \sum_{x=0}^1{x^2} + \sum_{x=0}^1{x} + \sum_{x=0}^1{1} = 0}
], [
    q{sum reorder 3},
    q{axiom: \sum_{x=0}^1{x^2+x+1} = 0},
    q{unarydistrib: \sum_{x=0}^1{1} + \sum_{x=0}^1{x} + \sum_{x=0}^1{x^2} = 0}
], [
    q{sum group 1+2 with reorder},
    q{axiom: \sum_{x=0}^1{x^2+x+1} = 0},
    q{unarydistrib: \sum_{x=0}^1{1+x} + \sum_{x=0}^1{x^2} = 0}
], [
    q{sum group 2+2},
    q{axiom: \sum_{x=0}^1{x^3-x^2+x-1} = 0},
    q{unarydistrib: \sum_{x=0}^1{x^3+x} + \sum_{x=0}^1{-x^2-1} = 0}
], [
# see comment in Axiom::Expr->split_prod
#   q{sum group with negate TODO apply negate},
#   q{axiom: \sum_{x=0}^1{x^3-x^2+x-1} = 0},
#   q{unarydistrib: \sum_{x=0}^1{x^3+x} - \sum_{x=0}^1{x^2+1} = 0}
#], [
    q{sum deeper simple},
    q{axiom: 2^{\sum_{x=0}^1{x+1}} = 0},
    q{unarydistrib: 2^{\sum_{x=0}^1{x} + \sum_{x=0}^1{1}} = 0}
], [
    q{sum deeper complex},
    q{axiom: 2^{\sum_{x=0}^1{x^3+x^2+x+1}} = 0},
    q{unarydistrib: 2^{\sum_{x=0}^1{x^3+x} + \sum_{x=0}^1{x^2+1}} = 0}
], [
    q{sum in list simple},
    q{axiom: 2 + \sum_{x=0}^1{x+1} = 0},
    q{unarydistrib: 2 + \sum_{x=0}^1{x} + \sum_{x=0}^1{1} = 0}
], [
    q{sum in list complex},
    q{axiom: 2 + \sum_{x=0}^1{x^3+x^2+x+1} = 0},
    q{unarydistrib: 2 + \sum_{x=0}^1{x^3+x} + \sum_{x=0}^1{x^2+1} = 0}
], [
    q{sum with grouping},
    q{axiom: \sum_{x=0}^1{x} + \sum_{x=0}^1{x+1} = 0},
    q{unarydistrib: 2\sum_{x=0}^1{x} + \sum_{x=0}^1{1} = 0}
], [
    q{sum with cancellation},
    q{axiom: \sum_{x=0}^1{x+1} - \sum_{x=0}^1{x} = 0},
    q{unarydistrib: \sum_{x=0}^1{1} = 0}
], [
    q{pow simple 2-part},
    q{axiom: \Aa: (a+1)^2 = (a+1)^2},
    q{unarydistrib: \Aa: (a+1)^2 = a^2+2a+1}
], [
    q{pow simple 2-part reverse},
    q{axiom: \Aa: (1+a)^2 = (1+a)^2},
    q{unarydistrib: \Aa: (1+a)^2 = 1+2a+a^2}
], [
    q{pow simple 3-part},
    q{axiom: \Aa: \Ab: \Ac: (a+b+c)^2 = (a+b+c)^2},
    q{unarydistrib: \Aa: \Ab: \Ac: (a+b+c)^2 = a^2+b^2+c^2+2ab+2ac+2bc}
], [
    q{pow simple 3-part with coalesce},
    q{axiom: \Aa: (a^2+a+1)^2 = (a^2+a+1)^2},
    q{unarydistrib: \Aa: (a^2+a+1)^2 = a^4+2a^3+3a^2+2a+1},
], [
    q{pow group 1+2},
    q{axiom: \Aa: \Ab: \Ac: (a+b+c)^2 = (a+b+c)^2},
    q{unarydistrib: \Aa: \Ab: \Ac: (a+b+c)^2 = (a+c)^2+b^2+2(a+c)b}
], [
    q{pow group 2+2},
    q{axiom: \Aa: \Ab: \Ac: \Ad: (a+b+c+d)^2 = (a+b+c+d)^2},
    q{unarydistrib: \Aa: \Ab: \Ac: \Ad: (a+b+c+d)^2 = (a+c)^2+(b+d)^2+2(a+c)(b+d)}
], [
    q{pow in list simple},
    q{axiom: \Aa: a^3+(a+1)^2 = a^3+(a+1)^2},
    q{unarydistrib: \Aa: a^3+(a+1)^2 = a^3+a^2+2a+1}
], [
    q{pow in list 2+1 with coalesce},
    q{axiom: \Aa: (a^2+a+1)^2+a^2 = (a^2+a+1)^2+a^2},
    q{unarydistrib: \Aa: (a^2+a+1)^2+a^2 = (a^2+1)^2+2a(a^2+1)+2a^2}
], [
    q{pow in list with cancellation},
    q{axiom: \Aa: (a+1)^2-a^2 = (a+1)^2-a^2},
    q{unarydistrib: \Aa: (a+1)^2-a^2 = 2a+1}
], [
# CHECKME: when are these valid?
    q{splitpow simple 2-part},
    q{axiom: \Aa: \Ab: \Ac: a^{b+c} = a^{b+c}},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b+c} = a^{b}a^c}
], [
    q{splitpow simple 2-part recip},
    q{axiom: \Aa: \Ab: \Ac: a^{b-c} = a^{b-c}},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b-c} = a^b/a^c}
], [
    q{splitpow degen 2-part},
    q{axiom: \Aa: \Ab: a^{b+1} = a^{b+1}},
    q{unarydistrib: \Aa: \Ab: a^{b+1} = a^{b}a}
], [
    q{splitpow simple 3-part},
    q{axiom: \Aa: \Ab: \Ac: \Ad: a^{b+c+d} = a^{b+c+d}},
    q{unarydistrib: \Aa: \Ab: \Ac: \Ad: a^{b+c+d} = a^{b}a^{c}a^d}
], [
    q{splitpow group 1+2},
    q{axiom: \Aa: \Ab: \Ac: \Ad: a^{b+c+d} = a^{b+c+d}},
    q{unarydistrib: \Aa: \Ab: \Ac: \Ad: a^{b+c+d} = a^{b+d}a^c}
], [
    q{splitpow group 2+2},
    q{axiom: \Aa: \Ab: \Ac: a^{b^2+c^2+b+c} = a^{b^2+c^2+b+c}},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b^2+c^2+b+c} = a^{b^2+c}a^{c^2+b}}
], [
    q{splitpow group 2+2 recip},
    q{axiom: \Aa: \Ab: \Ac: a^{b^2+c^2-b-c} = a^{b^2+c^2-b-c}},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b^2+c^2-b-c} = a^{b^2-c}/a^{b-c^2}}
], [
    q{splitpow in list simple},
    q{axiom: \Aa: \Ab: \Ac: \Ad: a^{b+c}a^d = a^{b+c}a^d},
    q{unarydistrib: \Aa: \Ab: \Ac: \Ad: a^{b+c}a^d = a^{b}a^{c}a^d}
], [
    q{splitpow in list degen},
    q{axiom: \Aa: \Ab: \Ac: a^{b+c+1}b = a^{b+c+1}b},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b+c+1}b = a^{b}a^{c}ab}
], [
    q{splitpow with coalesce},
    q{axiom: \Aa: \Ab: \Ac: a^{b+c+1}a = a^{b+c+1}a},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b+c+1}a = a^{b}a^{c}a^2}
], [
    q{splitpow group with coalesce},
    q{axiom: \Aa: \Ab: \Ac: \Ad: a^{b+c+d+1}a = a^{b+c+d+1}a},
    q{unarydistrib: \Aa: \Ab: \Ac: \Ad: a^{b+c+d+1}a = a^{b+d}a^{c}a^2}
], [
    q{splitpow with cancel},
    q{axiom: \Aa: \Ab: \Ac: a^{b+c+1}a^{-1} = a^{b+c+1}a^{-1}},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b+c+1}a^{-1} = a^{b}a^c}
], [
    q{splitpow group with cancel},
    q{axiom: \Aa: \Ab: \Ac: a^{b+c+1}a^{-1} = a^{b+c+1}a^{-1}},
    q{unarydistrib: \Aa: \Ab: \Ac: a^{b+c+1}a^{-1} = a^{b+c}}
], [
    q{splitpow const simple},
    q{axiom: \Aa: \Ab: 2^{a+b} = 2^{a+b}},
    q{unarydistrib: \Aa: \Ab: 2^{a+b} = 2^{a}2^b}
], [
    q{splitpow const expand},
    q{axiom: \Aa: 2^{a+3} = 2^{a+3}},
    q{unarydistrib: \Aa: 2^{a+3} = 8 2^a}
], [
    q{splitpow const recip},
    q{axiom: \Aa: 2^{a-3} = 2^{a-3}},
    q{unarydistrib: \Aa: 2^{a-3} = 2^a/8}
], [
    q{splitpow const coalesce},
    q{axiom: \Aa: 4 2^{a+3} = 4 2^{a+3}},
    q{unarydistrib: \Aa: 4 2^{a+3} = 32 2^a}
], [
    q{splitpow const part cancel},
    q{axiom: \Aa: 32 2^{a-3} = 32 2^{a-3}},
    q{unarydistrib: \Aa: 32 2^{a-3} = 4 2^a}
], [
    q{splitpow const full cancel},
    q{axiom: \Aa: 8 2^{a-3} = 8 2^{a-3}},
    q{unarydistrib: \Aa: 8 2^{a-3} = 2^a}
], [
    q{splitpow const over cancel},
    q{axiom: \Aa: 8 2^{a-5} = 8 2^{a-5}},
    q{unarydistrib: \Aa: 8 2^{a-5} = 2^a/4}
], [
    q{splitpow const cancel with grouping},
    q{axiom: \Aa: \Ab: 8 2^{a-3+b} = 8 2^{a-3+b}},
    q{unarydistrib: \Aa: \Ab: 8 2^{a-3+b} = 2^{a+b}}
]);
done_testing();

sub test {
    my($lines, $good, $quiet) = @_;
    my $legend = shift @$lines;
    use Axiom::Context;
    my $t = Axiom::Context->new;
    my $result = 1;
    my $died = ! eval { $result &&= $t->add($_, $quiet) for @$_; 1 };
    my $out;
    if ($died) {
        $out = $@;
        $result = 0;
    }
    TODO: {
        local($TODO) = ($legend =~ s/\s*TODO\s+(.*)//) ? $1 : undef;
        if ($good ? $result : !$result) {
            pass($legend);
        } else {
            print $out;
            fail($legend);
        }
    }
}
