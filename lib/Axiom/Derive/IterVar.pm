package Axiom::Derive::IterVar;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::IterVar - rebase an iterator

=head1 USAGE

  derive: itervar ( line? )
  rule: [ line, location, var, expr ]

Rebases the iterator variable I<var> for the iterator at I<location>,
rewriting it to I<expr>. Allows for C< var := E + var > or C< var := E - var >
where C<E> is independent of I<var>.

Eg given C< x = \sum_{i=1}^n{ y^{n - i} } >, C< itervar(2, i := n - i) >
will construct C< x = \sum_{i=0}^{n-1}{ y^i } >.

=cut

sub rulename { 'itervar' }

sub derivere { <<'RE' }
    <rule: itervar>
        itervar (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
RE

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);
    my $loc = $starting->diff($target);

    # If the map is _not_ { i := $from + $to - i }, the diff point must be
    # the sum itself, since from and to will change, and in that case there
    # are always two possibilities which we can only distinguish by the expr.
    # If it _is_, the diff point will be a descendant (but that descendant
    # may itself be a sum).

    my @vargs;
    my $try = sub {
        @vargs = @_;
        local $self->{rules} = [];
        local $self->{working} = $self->{working};
        return validate($self, \@vargs) && ! $self->working->diff($target);
    };
    my $first = 1;
    while (1) {
        my $se = $starting->locate($loc);
        my $te = $target->locate($loc);
        if ($se->is_iter && $se->type eq $te->type) {
            my($var, $ofrom, $oto, $oexpr) = @{ $se->args };
            my(undef, $nfrom, $nto, $nexpr) = @{ $te->args };
            $var = $var->copy;
            if ($first) {
                my $diff = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [
                        $var->copy,
                        $ofrom->copy,
                        $nfrom->negate,
                    ],
                })->clean;
                return \@vargs if $try->($line, $loc, $var, $diff);
                $diff = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [
                        $nfrom->copy,
                        $oto->negate,
                        $var->negate,
                    ],
                })->clean;
                return \@vargs if $try->($line, $loc, $var, $diff);
            } else {
                my $diff = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [
                        $oto->copy,
                        $ofrom->copy,
                        $var->negate,
                    ],
                })->clean;
                return \@vargs if $try->($line, $loc, $var, $diff);
            }
        }
        last unless @$loc;
        pop @$loc;
        $first = 0;
    }
    die "don't know how to derive this itervar";
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $cvar, $cexpr) = @$args;
    my $starting = $self->line($line);

    my $iter = $starting->locate($loc);
    $iter->is_iter or die sprintf(
        "Don't know how to change iter var on a non-iterator %s\n",
        $iter->type,
    );
    my($var, $from, $to, $expr) = @{ $iter->args };

    {
        my $cdict = $starting->dict_at($loc);
        my $cbind = $cvar->_resolve_new($cdict);
        my $local = $cdict->local_name($cvar->name, $cbind);
        $cexpr->resolve($cdict);
    }

    my $repl;
    # If E is an expression independent of the iter variable i, we can
    # change variable to E+i or to E-i (with a reverse of from/to), but
    # not anything else.
    my $pos = Axiom::Expr->new({
        type => 'pluslist',
        args => [ $cexpr->copy, $cvar->negate ],
    });
    if ($pos->is_independent($cvar)) {
        # i := i + E; inverse is i := i - E
        my $inv = Axiom::Expr->new({
            type => 'pluslist',
            args => [ $cvar->copy, Axiom::Expr->new({
                type => 'negate', args => [ $pos ]
            }) ],
        })->clean;
        $repl = Axiom::Expr->new({
            type => $iter->type,
            args => [
                $var->copy,
                $inv->subst_var($cvar, $from),
                $inv->subst_var($cvar, $to),
                $expr->subst_var($var, $cexpr->subst_var($cvar, $var)),
            ],
        });
    } elsif (Axiom::Expr->new({
        type => 'pluslist',
        args => [ $cexpr->copy, $cvar->copy ],
    })->is_independent($cvar)) {
        # i := E - i; inverse is same, i := E - i
        $repl = Axiom::Expr->new({
            type => $iter->type,
            args => [
                $var->copy,
                $cexpr->subst_var($cvar, $to),
                $cexpr->subst_var($cvar, $from),
                $expr->subst_var($var, $cexpr->subst_var($cvar, $var)),
            ],
        });
    } else {
        die sprintf(
            "Don't know how to change iter var with expression %s := %s\n",
            $cvar->name, $cexpr->rawexpr,
        );
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf(
        'itervar(%s%s, %s := %s)',
        $self->_linename($line), join('.', @$loc),
        $cvar->name, $cexpr->rawexpr,
    );

    return 1;
}

1;
