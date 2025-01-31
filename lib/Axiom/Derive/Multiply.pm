package Axiom::Derive::Multiply;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Multiply - multiply both sides of a relation by some expr

=head1 USAGE

  derive: multiply ( line? )
  rule: [ line, loc, expr ]

Given a prior relation of the form C< P = Q >, replaces it with the new
relation C< P . expr = Q . expr >.

=head1 RESTRICTIONS

Given a multiplier C<m>, we implement C<< P rel_1 Q -> mP rel_2 mQ >>.
Since C<m> can legitimately be zero, the implication is not reversible.

So the affected relation must be I<unencumbered>: we must be able to walk
up its ancestry to the top level of the theorem or to the first argument
of a C<\given>; on the way we can pass through for example quantifiers,
C<andlist> or the second argument of C<implies>, but not for example the
first argument of C<implies>, or logical negation.

C<m> must be a number, so it must provably avoid forbidden subexpressions
such as division by zero.

The relation must support the change: if it is an inequality, we must
know the sign of C<m>; if it is nonequality, C<m> must not be zero.

If the multiplier is not a constant, evidence that these restrictions
are satisfied must be available from a C<\given> enclosing the affected
relation.

New bound variables may be introduced with quantifiers. If the resulting
expression is independent of a quantified variable, that quantifier
[may / must] be elided.

=cut

sub rulename { 'multiply' }

sub derive_args {
    q{
        (?: \( <[args=optline]> (?: \s* <.ValueToken> \s* <[args=Expr]> )? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} // '';
        })
    };
}

sub find_multiplicand {
    my($self, $left, $right, $dict) = @_;
    # FIXME: division is unsafe, we need to cancel items directly
    my $expr = Axiom::Expr->new({
        type => 'mullist',
        args => [
            $right->copy,
            Axiom::Expr->new({
                type => 'recip',
                args => [ $left->copy ],
            }),
        ],
    });
    $expr->resolve($dict);
    $expr = $expr->clean;
    $expr->walk_tree(sub {
        my($e) = @_;
        return unless $e->type eq 'pow';
        my($base, $pow) = @{ $e->args };
        return unless $pow->is_const && $pow->rat == 0;
        # FIXME: hack, make x^0 into 1^0 so that clean() will clean it
        $e->args->[0] = Axiom::Expr->new_const(1);
        return;
    });
    return $expr->clean;
}

sub derive {
    my($self, $args) = @_;
    my($line, $value) = @$args;
    my $source = $self->line($line);
    my $target = $self->expr;

    # find the relation to apply to
    # FIXME: qualifiers may differ, we want to look past those
    my $loc = $source->diff($target)
            or return $self->set_error("can't find difference");
    $loc = $source->find_ancestor($loc, sub { shift->is_relation })
            or return $self->set_error("can't find relation targetted");
    my($from, $to) = map $_->locate($loc), ($source, $target);
    $to->is_relation
            or return $self->set_error("target mismatch");

    # find the multiplicand
    my($fl, $fr) = @{ $from->args };
    # FIXME: we may have introduced new variables
    my $dict = $source->dict_at($loc);
    my $expr = $value // (($fl->is_const && $fl->rat == 0)
        ? $self->find_multiplicand($fr, $to->args->[1], $dict)
        : $self->find_multiplicand($fl, $to->args->[0], $dict)
    ) or return $self->set_error("can't find multiplicand");

    return $self->validate([ $line, $loc, $expr ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $expr) = @$args;
    my $starting = $self->line($line);

    return $self->set_error("relation is not unencumbered")
            unless $starting->is_unencumbered($loc);
    my $given = $self->find_given($starting, $loc);
    return $self->set_error(
        sprintf("multiplicand %s is not a number", $expr->str)
    ) unless $expr->is_number($given);

    my $rel = $starting->locate($loc);
    $rel->is_relation or return $self->set_error(sprintf(
        "don't know how to multiply a %s", $starting->type,
    ));

    my $targ_type;
    if ($rel->type eq 'req') {
        $targ_type = 'req';
    } else {
        my $sign = $expr->test_sign($given);
        return $self->set_error(sprintf(
            "can't multiply inequality by non-const '%s'", $expr->str
        )) unless defined $sign;
        return $self->set_error(sprintf(
            "can't multiply inequality by zero"
        )) unless $sign;
        $targ_type = ($sign < 0) ? $rel->inverse_type : $rel->type;
    }

    my $repl = Axiom::Expr->new({
        type => $targ_type,
        args => [ map Axiom::Expr->new({
            type => 'mullist',
            args => [ $_->copy, $expr->copy ],
        }), @{ $rel->args } ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'multiply(%s%s, %s)',
            $self->_linename($line), join('.', @$loc), $expr->rawexpr);

    return 1;
}

1;
__END__
Test cases:
1 = 1 -> -1 = -1
a > 1 -> -2a < -2
-2a <= 2 -> a >= 1
a + 1 = b + 1 -> 2(a + 1) = 2(b + 1)
a + 1 = b + 1 -> (a + 1)^2 = (a + 1)(b + 1)
a + b = c + d -> -a - b = -c - d
(a + b)(c + d) = e(c + d) -> a + b = e    // fail
(a + b)\given_{c + d > 0}{c + d} = e(c + d) -> a + b = e    // fail
\given_{c + d > 0}{(a + b)(c + d) = e(c + d)} -> a + b = e  // ok
\given_{0 < a}{a + 1} > 1 -> \given_{0 > -2a}{a + 1} > 1
\Aa: 2a = a + a -> \Aa: \Ab: ab = (a + a)b/2
\Aa: 2a > a + a -> \Aa: \Ab: ab > (a + a)b/2    // fail
