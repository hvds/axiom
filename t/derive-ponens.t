#!/opt/axiom-d/bin/perl
use strict;
use warnings;
use Test::More;

use lib 'lib';

# test good cases
test($_, 1, 1) for ([
    q{ponens simple constant},
    q{axiom A1: 0 < 1}, q{axiom A2: (0 < 1) -> (0 <= 1)},
    q{ponens(A1: A2): 0 <= 1}
], [
    q{ponens simple global},
    q{*var x},
    q{axiom A: (x = 1) -> (2x = 2)},
    q{axiom: x = 1}, q{ponens(A): 2x = 2}
], [
    q{ponens simple min},
    q{*var a, b},
    q{axiom A: (a <= b) -> (\min(a, b) = a)},
    q{axiom: a <= b}, q{ponens(A): \min(a, b) = a}
], [
    q{ponens specify all outer quantifiers},
    q{axiom A: \Aa: \Ab: (a < b) -> (a <= b)},
    q{*var x}, q{axiom: x < 0}, q{ponens(A): x <= 0}
], [
    q{ponens specify no outer quantifiers},
    q{axiom A: \Aa: \Ab: (a < b) -> (a <= b)},
    q{axiom: \Aa: \Ab: a < b},
    q{ponens(A): \Aa: \Ab: a <= b},
], [
    q{ponens specify some outer quantifiers},
    q{axiom A: \Aa: \Ab: \Ac: \Ad: ((a >= c) & (b >= d)) -> (a+b >= c+d)},
    q{axiom: \Aa: \Ad: (a >= 0) & (1 >= d)},
    q{ponens(A): \Aa: \Ad: a+1 >= d}
], [
    q{ponens inner quantifier},
    q{axiom A: (\Ax: (x >= 0) | (x <= 0)) -> (\Ax: \max(0, \min(1, x)) = \min(1, \max(0, x)))},
    q{axiom: \Ax: (x >= 0) | (x <= 0)},
    q{ponens(A): \Ax: \max(0, \min(1, x)) = \min(1, \max(0, x))}
], [
    q{ponens embedded},
    q{axiom A: \Ac: \Ad: ((c >= d) | (c <= d)) -> (\int_{e=0}^{\max(0,\min(1,c-d))}{ \min(c,d+e) } = \int_{e=0}^{\max(0,\min(1,c-d))}{ d+e })},
    q{axiom: \Ac: \Ad: (c >= d) | (c <= d)},
    q{ponens(A): \Ac: \Ad: \int_{e=0}^{\max(0,\min(1,c-d))}{ \min(c,d+e) } = \int_{e=0}^{\max(0,\min(1,c-d))}{ d+e }}
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
