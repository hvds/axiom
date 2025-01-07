package Axiom::Derive::Cases;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };

=head1 NAME

Axiom::Derive::Cases - apply case analysis

=head1 USAGE

  derive: cases ( line?, line2 )
  rule: [ line, line2 ]

Given prior theorems I<line> of the form C<< \Ax: P(x) -> R(x) >> and
C<< \Ax: Q(x) -> R(x) >>, proves C<< \Ax: (P(x) | Q(x)) -> R(x) >>.

The classic "case analysis" inference rule described in WikiPedia actually
requires a third given C<< \Ax: P(x) | Q(x) >> and derives C<< \Ax: R(x) >>,
but our life is simpler if we leave that to a separate 'ponens' step.

=cut

sub rulename { 'cases' }

sub derive_args {
    q{
        \( <[args=optline]> \s* <[args=line]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
    };
}

sub derive {
    my($self, $args) = @_;
    return $self->validate($args);
}

sub validate {
    my($self, $args) = @_;
    my($line2, $line) = @$args;
    my $left = $self->line($line);
    my $right = $self->line($line2);
    my $target = $self->expr;
    $target->resolve($self->dict);

    my($li, @lv) = ($left);
    while ($li->type eq 'forall') {
        (my($var), $li) = @{ $li->args };
        push @lv, $var;
    }
    return $self->set_error(sprintf(
        "Can't use cases with a %s", $li->type
    )) unless $li->type eq 'implies';
    my($lg, $lr) = @{ $li->args };
    my($ri, @rv) = ($right);
    while ($ri->type eq 'forall') {
        (my($var), $ri) = @{ $ri->args };
        push @rv, $var;
    }
    return $self->set_error(sprintf(
        "Can't use cases with a %s", $ri->type
    )) unless $ri->type eq 'implies';
    my($rg, $rr) = @{ $ri->args };

    return $self->set_error(sprintf(
        "Mismatched conclusions '%s' versus '%s'",
        $lr->bracketed, $rr->bracketed,
    )) if $lr->diff($rr, 1);

    my $wrap = sub {
        my($var, $e) = @_;
        return Axiom::Expr->new({
            type => 'forall',
            args => [ $var, $e ],
        });
    };
    $lg = $wrap->(pop(@lv), $lg) while @lv > @rv;
    $rg = $wrap->(pop(@rv), $rg) while @lv < @rv;
    ($lg, $rg) = ($wrap->(pop(@lv), $lg), $wrap->(pop(@rv), $rg))
            while @lv && $lv[-1]->name ne $rv[-1]->name;

    my $result = Axiom::Expr->new({
        type => 'implies',
        args => [
            Axiom::Expr->new({
                type => 'orlist',
                args => [ $lg, $rg ],
            }),
            $lr,
        ],
    });
    $result = $wrap->($_, $result) for reverse @lv;
    $result = $result->copy;
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'cases(%s%s)',
            $self->_linename($line), $line2);

    return 1;
}

1;
