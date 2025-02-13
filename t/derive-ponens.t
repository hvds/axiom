#!/opt/axiom-d/bin/perl
use strict;
use warnings;
use Test::More;

use lib 'lib';

# test good cases
test($_, 1, 1) for ([
    q{*var x},
    q{axiom A: (x = 1) -> (2x = 2)},
    q{axiom: x = 1}, q{ponens(A): 2x = 2}
], [
    q{axiom A1: 0 < 1}, q{axiom A2: (0 < 1) -> (0 <= 1)},
    q{ponens(A1: A2): 0 <= 1}
], [
    q{*var a, b},
    q{axiom A: (a <= b) -> (\min(a, b) = a)},
    q{axiom: a <= b}, q{ponens(A): \min(a, b) = a}
], [
    q{axiom A: \Aa: \Ab: \Ac: ((a <= b) & (b <= c)) -> (a <= c)},
    q{*var x},
    q{axiom: (x <= 0) & (0 <= 1)}, q{ponens(A): x <= 1}
], [
    q{axiom A: (\Ax: (x >= 0) | (x <= 0)) -> (\Ax: \max(0, \min(1, x)) = \min(1, \max(0, x)))},
    q{axiom: \Ax: (x >= 0) | (x <= 0)},
    q{ponens(A): \Ax: \max(0, \min(1, x)) = \min(1, \max(0, x))}
], [
    q{axiom A: \Ac: \Ad: ((c >= d) | (c <= d)) -> (\int_{e=0}^{\max(0,\min(1,c-d))}{ \min(c,d+e) } = \int_{e=0}^{\max(0,\min(1,c-d))}{ d+e })},
    q{axiom: \Ac: \Ad: (c >= d) | (c <= d)},
    q{ponens(A): \Ac: \Ad: \int_{e=0}^{\max(0,\min(1,c-d))}{ \min(c,d+e) } = \int_{e=0}^{\max(0,\min(1,c-d))}{ d+e }}
]);
done_testing();

sub test {
    my($lines, $good, $quiet) = @_;
    use Axiom::Context;
    my $t = Axiom::Context->new;
    my $result = 1;
    my $died = ! eval { $result &&= $t->add($_, $quiet) for @$_; 1 };
    my $out;
    if ($died) {
        $out = $@;
        $result = 0;
    }
    ok(($good ? $result : !$result), $out);
}
