package Axiom::Derive::Factor;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Factor - rearrange a subexpression by factoring

=head1 USAGE

  derive: factor ( line? )
  rule: [ line, location, expr ]

Factors the given I<expr> out of the subexpression at I<location>.

Eg given C< x = 2/y + 3/y(y+1) + 1 >, C< factor(2, 1/y) > will construct
C< x = (1 / y)(2 + 3/(y + 1) + y) >.

TODO: we currently support only factoring from type C<pluslist> or C<sum>.
TODO: we currently only derive a single term to factor.

=cut

sub rulename { 'factor' }

sub derive_args {
    q{
        (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
    };
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);

    my %seen_at_loc;
    my $try = sub {
        my($loc, $expr) = @_;
        return 0 if $seen_at_loc{$expr->str}++;
        return 1 if $self->validate([ $line, $loc, $expr->copy ]);
        $self->clear_error;
        return 0;
    };
    my $try_all = sub {
        my($loc, $all) = @_;
        for my $this (@$all) {
            return 1 if $try->($loc, $this);
            if ($this->type eq 'negate') {
                return 1 if $try->($loc, Axiom::Expr->new_const(-1));
                return 1 if $try->($loc, $this->args->[0]);
            }
            if ($this->type eq 'pow') {
                return 1 if $try->($loc, $this->args->[0]);
            }
        }
        return 0;
    };

    my @choice = do {
        my $l = $starting->diff($target, 1)
                or return $self->set_error('no diff, factor not needed');
        ([ $l, $starting->locate($l) ]);
    };
    while (@choice) {
        my($loc, $e) = @{ shift @choice };
        my $a = $e->args;
        %seen_at_loc = ();
        if ($e->type eq 'mullist') {
            for my $me (@$a) {
                next if $me->is_const;
                return 1 if $try->($loc, $me);
                return 1 if $me->type eq 'pow' && $try->($loc, $me->args->[0]);
            }
            push @choice, map [ [ @$loc, $_ + 1 ], $a->[$_] ], 0 .. $#$a;
            next;
        }
        if ($e->type eq 'pluslist') {
            for my $ae (@$a) {
                if ($ae->type eq 'mullist') {
                    return 1 if $try_all->($loc, $ae->args);
                } elsif ($ae->type eq 'negate') {
                    return 1 if $try->($loc, Axiom::Expr->new_const(-1));
                } elsif ($ae->type eq 'pow') {
                    return 1 if $try->($loc, $ae);
                    return 1 if $try->($loc, $ae->args->[0]);
                } else {
                    return 1 if $try->($loc, $ae);
                }
            }
            next;
        }
        if ($e->type eq 'sum') {
            my($v, $se) = @$a[0, 3];
          retry_sum:
            if ($se->is_independent($v)) {
                return 1 if $try->($loc, $se);
            }
            if ($se->type eq 'mullist') {
                my @ind = grep $_->is_independent($v), @{ $se->args };
                return 1 if $try_all->($loc, \@ind);
            } elsif ($se->type eq 'negate') {
                return 1 if $try->($loc, Axiom::Expr->new_const(-1));
                $se = $se->args->[0];
                goto retry_sum;
            } elsif ($se->type eq 'pluslist') {
                $se = $se->args->[0];
                goto retry_sum;
            }
            next;
        }
    }
    return $self->set_error("don't know how to derive this");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $expr) = @$args;
    my $starting = $self->line($line);

    my $targ = $starting->locate($loc);
    my $subdict = $starting->dict_at($loc);
    $expr->resolve($subdict);

    my $repl;
    if ($targ->type eq 'pluslist') {
        my(@div, @nondiv);
        for my $a (@{ $targ->args }) {
            my $ad = _trydiv($a, $expr);
            if ($ad) {
                push @div, $ad;
            } else {
                push @nondiv, $a;
            }
        }
        $repl = Axiom::Expr->new({
            type => 'mullist',
            args => [ $expr, Axiom::Expr->new({
                type => 'pluslist',
                args => \@div,
            }) ],
        });
        if (@nondiv) {
            $repl = Axiom::Expr->new({
                type => 'pluslist',
                args => [ $repl, map $_->copy, @nondiv ],
            });
        }
    } elsif ($targ->type eq 'mullist') {
        my(@div, @nondiv, @pow);
        for my $a (@{ $targ->args }) {
            if (!$a->diff($expr)) {
                push @pow, Axiom::Expr->new_const(1);
            } elsif ($a->type eq 'pow' && !$a->args->[0]->diff($expr)) {
                push @pow, $a->args->[1]->copy;
            } else {
                my $ad = _trydiv($a, $expr);
                if ($ad) {
                    push @div, $ad;
                    push @pow, Axiom::Expr->new_const(1);
                } else {
                    push @nondiv, $a;
                }
            }
        }
        $repl = Axiom::Expr->new({
            type => 'pow',
            args => [
                $expr->copy,
                Axiom::Expr->new({
                    type => 'pluslist',
                    args => \@pow,
                }),
            ],
        });
        if (@div || @nondiv) {
            $repl = Axiom::Expr->new({
                type => 'mullist',
                args => [
                    @div,
                    (map $_->copy, @nondiv),
                    $repl,
                ],
            });
        }
    } elsif ($targ->type eq 'sum') {
        $repl = Axiom::Expr->new({
            type => 'mullist',
            args => [ $expr, Axiom::Expr->new({
                type => 'sum',
                args => [
                    map($_->copy, @{ $targ->args }[0 .. 2]),
                    _div($targ->args->[3], $expr),
                ],
            }) ],
        });
    } else {
        return $self->set_error(sprintf(
            "don't know how to factor a %s\n", $targ->type,
        ));
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'factor(%s%s, %s)',
            $self->_linename($line), join('.', @$loc), $expr->rawexpr);

    return 1;
}

sub _trydiv {
    my($e1, $e2) = @_;
    return _div($e1, $e2) if $e2->is_const || $e2->type eq 'recip';
    return Axiom::Expr->new_const(1) if !$e1->diff($e2);
    my @e = ($e1);
    while (@e) {
        my $e = shift @e;
        return _div($e1, $e2) if !$e->diff($e2);
        push(@e, $e->args->[0]), next if $e->type eq 'negate';
        push(@e, $e->args->[0]), next if $e->type eq 'pow';
        push(@e, @{ $e->args }), next if $e->type eq 'mullist';
    }
    return undef;
}

sub _div {
    my($e1, $e2) = @_;
    my($t1, $t2) = map $_->type, ($e1, $e2);
    return Axiom::Expr->new_const(1) if !$e1->diff($e2);
    my $a1 = $e1->args;
    my $r2 = ($t2 eq 'recip')
        ? $e2->args->[0]
        : Axiom::Expr->new({
            type => 'recip',
            args => [ $e2 ],
        });
    if ($t1 eq 'mullist') {
        my($index) = grep !$a1->[$_]->diff($e2), 0 .. $#$a1;
        if (defined $index) {
            return Axiom::Expr->new({
                type => 'mullist',
                args => [ map {
                    $_ == $index ? () : $a1->[$_]->copy
                } 0 .. $#$a1 ],
            });
        }
        return Axiom::Expr->new({
            type => 'mullist',
            args => [ map($_->copy, @$a1), $r2 ],
        });
    }
    if ($t1 eq 'negate' && $a1->[0]->type eq 'mullist') {
        return Axiom::Expr->new({
            type => 'negate',
            args => [ _div($a1->[0], $e2) ],
        });
    }
    return Axiom::Expr->new({
        type => 'mullist',
        args => [ $e1, $r2 ],
    });
}

1;
