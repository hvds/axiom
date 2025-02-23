package Axiom::Derive::UnaryDistrib;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;
use List::Util qw{};

=head1 NAME

Axiom::Derive::UnaryDistrib - distribute an operator over its argument

=head1 USAGE

  derive: unarydistrib ( line? )
  rule: [ line, location, type, assign ]

Distribute the unary operator at the given I<location>. 

Currently supported patterns are:

=over 4

=item C<negate> acting over C<pluslist>

  -(a + b) => (-a) + (-b)

=item C<negate> acting over C<mullist>

  -(ab) => (-a)(b)

=item any plus-ish iterator with C<pluslist> as its expr

This covers C<sum>, C<integral> and C<inteval>:

  \sum_{i=a}^b{ci + d} => \sum_{i=a}^b{ci} + \sum_{i=a}^b{d}

=item C<pow> with C<pluslist> base and positive integer power

  (a + b)^2 => a^2 + 2b + b^2

=item C<pow> with C<pluslist> power

  a^{b + c} => (a^b)(a^c)

=item C<forall> acting over C<implies>

  \Aa: p -> q => (\Aa: p) -> (\Aa: q)

=back

Distributed patterns may be grouped arbitratily, eg we can expand
C< (a+b+c+d)^2 > to C< (a+d)^2+(b+c)^2+2(a+d)(b+c) >. The chosen
grouping is referred to as 'assign' in the rule.

=cut

sub rulename { 'unarydistrib' }

sub derive_args {
    (1, q{ <[args=line]>? });
}

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $fb = $self->box($line);
    my $tb = $self->tbox;
    my $loc = $fb->diff($tb, 1, 1);
    my $fe = $fb->locate($loc);
    my $te = $tb->locate($loc);
    my $ft = $fe->type;
    my $rem = [ $te->expr->split_prod ];
    my $split = 0;

    # used for a quick check before _try_expr()
    my %candidate = map +($_ => 1), qw{
        forall negate pow sum integral inteval
    };

    if ($ft eq 'pluslist') {
        my($left, $right) = $fe->plusdiff($te);
        if (@$left == 1) {
            my $li = $left->[0];
            $fe = $fe->arg($li);
            $ft = $fe->type;
            $rem = $right;
            $split = 1;
        } else {
            my $args = $fe->expr->args;
            my @right2 = map $_->negate->split_prod, @$args[@$left];
            for my $i (0 .. $#$left) {
                my $argi = $left->[$i];
                my $fe2 = $fe->arg($argi);
                next unless $candidate{$fe2->type};
                my $rem2 = [
                    @$right,
                    @right2[0 .. $i - 1],
                    @right2[$i + 1 .. $#right2],
                ];
                return 1 if eval { $self->_try_expr($line, $fe2, $rem2, 1) };
                $self->clear_error;
            }
            return $self->set_error(sprintf(
                '%s no match from multiple changes: (%s)', $self->rulename,
                join ', ', map $_->str, @$args[@$left]
            ));
        }
    } elsif ($ft eq 'mullist') {
        my $la = $fe->expr->args;
        my $zone = Math::BigRat->new(1);
        my $rc = $zone;
        my $right = [
            map {
                $_->is_const ? do {
                    $rc *= $_->rat;
                    ()
                } : $_;
            } ($te->type eq 'mullist') ? @{ $te->expr->args } : $te->expr
        ];
        my $left = [ reverse grep {
            my $le = $la->[$_];
            my $keep = 1;
            if ($le->is_const) {
                $rc /= $le->rat;
                $keep = 0;
            } else {
                my $ri = List::Util::first(sub {
                    ! $le->diff($right->[$_], 1)
                }, 0 .. $#$right);
                if (defined $ri) {
                    splice @$right, $ri, 1;
                    $keep = 0;
                }
            }
            $keep;
        } reverse 0 .. $#$la ];
        unshift @$right, _newc($rc) if $rc != 1;
        die "panic: muldiff found nothing left after split\n" unless @$left;

        $rem = [ map [ $zone, $_ ], @$right ];
        if (@$left == 1) {
            my $li = $left->[0];
            $fe = $fe->arg($li);
            $ft = $fe->type;
            $split = 2;
        } else {
            my $args = $fe->expr->args;
            my @right2 = map [ $zone, $_->recip ], @$la[@$left];
            for my $i (0 .. $#$left) {
                my $argi = $left->[$i];
                my $fe2 = $fe->arg($argi);
                next unless $candidate{$fe2->type};
                my $rem2 = [
                    @$rem,
                    @right2[0 .. $i - 1],
                    @right2[$i + 1 .. $#right2],
                ];
                return 1 if eval { $self->_try_expr($line, $fe2, $rem2, 2) };
                $self->clear_error;
            }
            return $self->set_error(sprintf(
                '%s no match from multiple changes: (%s)', $self->rulename,
                join ', ', map $_->str, @$args[@$left]
            ));
        }
    }

    return $self->_try_expr($line, $fe, $rem, $split) if $candidate{$fe->type};
    return $self->set_error("don't know how to derive this unarydistrib");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $type, $assign) = @$args;
    my $fb = $self->box($line);
    my $fe = $fb->locate($loc);
    $fe->assert_type(($type eq 'splitpow') ? 'pow': $type);

    my($arg, $repl);
    if ($type eq 'forall') {
        my $fu = $fe->unwrap;
        $fu->assert_type('implies');
        my($move, $keep) = _pick_args($fu->allvars, $assign);
        $repl = _wrap($keep, Axiom::Expr->new({
            type => 'implies',
            args => [ map _wrap($move, $_->copy), @{ $fu->expr->args } ],
        }));
    } elsif ($type eq 'negate') {
        my $fe2 = $fe->arg(0);
        $fe2->assert_type('pluslist');
        my $replargs = $self->_assign($fe2->expr->args, $assign, 'pluslist')
                or return;
        $repl = Axiom::Expr->new({
            type => 'pluslist',
            args => [ map $_->negate, @$replargs ],
        });
    } elsif ($fe->expr->is_iter && $fe->expr->combiner eq 'pluslist') {
        my($var, $start, $end, $expr) = @{ $fe->expr->args };
        $fe->arg(3)->assert_type('pluslist');
        my $replargs = $self->_assign($expr->args, $assign, 'pluslist')
                or return;
        $repl = Axiom::Expr->new({
            type => 'pluslist',
            args => [ map Axiom::Expr->new({
                type => $type,
                args => [ $var->copy, $start->copy, $end->copy, $_ ],
            }), @$replargs ],
        });
    } elsif ($type eq 'pow') {
        # specifically power expansion
        my($expr, $power) = @{ $fe->expr->args };
        return $self->set_error(sprintf(
            'Power expansion requires positive integer power, not %s',
            $power->str
        )) unless $power->type eq 'integer' && $power->rat > 0;
        my $args = $self->_assign($expr->args, $assign, 'pluslist')
                or return;
        my $piece = _expand_r($args, $power->rat);
        $repl = (@$piece > 1) ? Axiom::Expr->new({
            type => 'pluslist',
            args => $piece,
        }) : (@$piece) ? $piece->[0] : _newc();
    } elsif ($type eq 'splitpow') {
        my($val, $pow) = @{ $fe->expr->args };
        return $self->set_error(sprintf(
            'Splitting a power requires a pluslist power, not %s',
            $pow->type
        )) unless $pow->type eq 'pluslist';
        my $args = $self->_assign($pow->args, $assign, 'pluslist')
                or return;
        $repl = (@$args > 1) ? Axiom::Expr->new({
            type => 'mullist',
            args => [ map Axiom::Expr->new({
                type => 'pow',
                args => [ $val->copy, $_ ],
            }), @$args ],
        }) : $args->[0];
    }

    unless ($repl) {
        return $self->set_error(sprintf(
            "don't know how to distribute a %s%s\n",
            $fe->type, $arg ? ' over a ' . $arg->type : '',
        ));
    }

    $repl->resolve($fe->dict_at);
    my $result = $fb->expr->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'unarydistrib(%s%s)',
            $self->_linename($line), join('.', @$loc));

    return 1;
}

# Try to find a derivation from the boxed $fe to the arrayref of split_prod
# results $rem (which has had type $split applied), and return the result
# of validating it.
sub _try_expr {
    my($self, $line, $fe, $rem, $split) = @_;
    my $ft = $fe->type;
    my $fex = $fe->expr;

    if ($ft eq 'forall' && !$split) {
        my $loc = $fe->loc;
        my $fb = $self->box($line);
        my $tb = $self->tbox;
        {
            # if diff walked past any foralls just above the loc, unwind that
            my $changed = 0;
            my $ancestry = $fe->ancestry;
            for (reverse 0 .. $#$ancestry - 1) {
                last unless $ancestry->[$_]->type eq 'forall';
                pop @$loc;
                $changed = 1;
            }
            $fe = $fb->locate($loc) if $changed;
        }
        my $te = $tb->locate($loc);
        my $fw = $fe->unwrap;
        $fw->assert_type('implies') or return;
        my $tw = $te->unwrap;
        my $fvars = $fw->allvars;
        # no remapping: we expect variables to keep their name the same
        # across this transformation
        my %vars = map +($fvars->[$_]->name => $_), 0 .. $#$fvars;
        delete $vars{$_->name} for @{ $tw->allvars };
        return $self->set_error(sprintf(
            'unarydistrib forall over implies: no variables moved'
        )) unless keys %vars;
        return $self->validate([$line, $loc, $ft,
                [ sort { $a <=> $b } values %vars ]]);
    }

    if ($ft eq 'negate' && $fex->args->[0]->type eq 'pluslist') {
        $fex = $fex->args->[0];
        my $left = [ map $_->split_prod->[1], @{ $fex->args } ];
        my $right = _make_right($rem, $split, sub { return $_[0]->negate });
        my $assign = _find_assignment($self, $ft, $left, $right)
                or return;
        return $self->validate([ $line, $fe->loc, $ft, $assign ]);
    }

    if ($fex->is_iter && $fex->combiner eq 'pluslist'
        && $fex->args->[3]->type eq 'pluslist'
    ) {
        my($lvar, $lstart, $lend, $lexpr) = @{ $fe->expr->args };
        $fe->arg(3)->assert_type('pluslist');
        my $left = [ map $_->split_prod->[1], @{ $lexpr->args } ];
        my $right = _make_right($rem, $split, sub {
            my($e) = @_;
            return undef unless $e->type eq $ft;
            my($rvar, $rstart, $rend, $rexpr) = @{ $e->args };
            return undef if $lvar->name ne $rvar->name
                    || $lstart->diff($rstart, 1)
                    || $lend->diff($rend, 1);
            return $rexpr;
        });
        my $assign = _find_assignment($self, $ft, $left, $right)
                or return;
        return $self->validate([ $line, $fe->loc, $ft, $assign ]);
    }

    if ($ft eq 'pow' && $fex->args->[0]->type eq 'pluslist' && (
        $split == 1 || ($split == 0 && $rem->[0][1]->type eq 'pluslist')
    )) {
        my($base, $power) = @{ $fe->expr->args };
        unless ($split) {
            @$rem = map {
                my($c, $e) = @$_;
                $e->type eq 'pluslist'
                    ? map {
                        my($c2, $e2) = @{ $_->split_prod };
                        [ $c * $c2, $e2 ]
                    } @{ $e->args }
                    : $_;
            } @$rem;
        }
        # aim is to fully expand the power
        return $self->set_error(sprintf(
            'for power expansion need power to be integer, not %s',
            $power->type
        )) unless $power->type eq 'integer';
        my $left = [ map $_->split_prod->[1], @{ $base->args } ];
        my $assign = _find_pow_assignment($self, $left, $power->rat, $rem)
                or return;
        return $self->validate([ $line, $fe->loc, $ft, $assign ]);
    }

    if ($ft eq 'pow' && $fex->args->[1]->type eq 'pluslist' && $split != 1) {
        $ft = 'splitpow';   # commit to this
        my($base, $power) = @{ $fex->args };
        my $rc = Math::BigRat->new(1);

        # TODO: if base is const, find power for RHS const
        @$rem = map {
            my($c, $e) = @$_;
            $rc *= $c;
            map {
                my($power2, $base2) = @{ $_->split_pow };
                if ($base->is_const && $base2->is_const) {
                    if ($base2->rat == 1 && $power2->is_const) {
                        my $log = _log_rat($base->rat, $power2->rat);
                        ($power2, $base2) = (_newc($log), $base->copy)
                                if defined $log;
                    } else {
                        my $log = _log_rat($base->rat, $base2->rat);
                        ($power2, $base2) = (Axiom::Expr->new({
                            type => 'mullist',
                            args => [ $power2->copy, _newc($log) ],
                        })->clean, $base->copy) if defined $log;
                    }
                }
                return $self->set_error(sprintf(
                    'in splitpow, base %s does not match target element %s',
                    $base->str, $base2->str
                )) if $base->diff($base2, 1);
                $power2->split_prod;
            } $e->type eq 'mullist' ? @{ $e->args } : $e; 
        } @$rem;
        if ($rc != 1) {
            return $self->set_error(sprintf(
                'in splitpow, base %s does not match const %s',
                $base->str, $rc
            )) unless $base->is_const;
            my($cbase, $cpow) = _log_rat($base->rat, $rc)
                    // return;
            unshift @$rem, [ $cpow, _newc() ];
        }

        my $left = [ map $_->split_prod->[1], @{ $power->args } ];
        my $right = _make_right($rem, $split, sub { $_[0] });
        my $assign = _find_assignment($self, $ft , $left, $right)
                or return;
        return $self->validate([ $line, $fe->loc, $ft, $assign ]);
    }

    return $self->set_error("don't know how to derive this unarydistrib");
}

# Given a remnant affected by type $split, further split any pluslists
# and pass each expr to the $child callback for replacement. Returns
# an arrayref of split_prod pairs.
sub _make_right {
    my($rem, $split, $child) = @_;
    my $right = [];
    my $ri = 0;
    for (@$rem) {
        my($c, $re) = @$_;
        my $list = (!$split && $re->type eq 'pluslist')
                ? $re->args : [ $re ];
        for (@$list) {
            my $re2 = $child->($_) or next;
            my $rj = $ri++;
            (my($c2), $re2) = @{ $re2->split_prod };
            push @$right, ($re2->type eq 'pluslist')
                ? (map {
                    my($c3, $re3) = @{ $_->split_prod };
                    [ $c * $c2 * $c3, $re3, $rj ];
                } @{ $re2->args })
                : [ $c * $c2, $re2, $rj ];
        }
    }
    return $right;
}

# Given an arrayref of exprs $left, and an arrayref of triples of the
# form (rat, expr, index) $right, finds a way to assign $left exprs
# to matching $right entries, or returns an error.
# On success, the result is an arrayref in which each entry lists
# elements of $left that corresponded to this element of $right.
# For now, the 'rat' constant multiplier is ignored: if that results
# in an incorrect derivation, validation will pick it up.
sub _find_assignment {
    my($self, $type, $left, $right) = @_;
    my @assign;
  LEFT:
    for my $li (0 .. $#$left) {
        my $le = $left->[$li];
        for (@$right) {
            my($rc, $re, $ri) = @$_;
            if (! $le->diff($re, 1)) {
                push @{ $assign[$ri] }, $li;
                next LEFT;
            }
        }
        # TODO: add new $right entry, which might cancel out, if we can
        # find a testcase for it
        return $self->set_error(sprintf(
            'In %s over %s could not find disposition for %s',
            $self->rulename, $type, $le->str
        ));
    }
    return \@assign;
}

# Partition L={l_i} into subsets {s_i = \sum{S_i < L}} such that the terms
# of (s_1+s_2+...s_m)^k match R = {r_i}.
# There are Bell(n) = A110(n) possible assignments; the RHS can have
# up to C(n+1,k) terms; RHS terms can be ambiguous, eg from ((a+b)^2+a+b+1)^2.
#
# We inspect RHS elements one by one, determining in each case what
# combinations of LHS elements could yield them and thus forming
# constraints on the list of possible assignments. We return success
# if we get down to one possible list, an error if we get down to zero,
# and an arbitrary result if we end with more than one.
sub _find_pow_assignment {
    my($self, $left, $pow, $right) = @_;
    my $struct = {
        self => $self,
        left => $left,
        pow => $pow,
        right => $right,
        unfixed => { map +($_ => $left->[$_]), 0 .. $#$left },
        assign => [],   # each element an array of indices
        fixed => [],    # each element an expression
        # $sets->[$i] is an arrayref of possible additional assignments,
        # any one of which is sufficient to match $right->[$i]. If $sets->[$i]
        # is empty, no match is possible; if it contains a single empty
        # arrayref then no additional constraint is needed.
        sets => [],
    };
    for (@{ $struct->{right} }) {
        my($c, $re) = @$_;
        # TODO: multiply out any reciprocals in LHS
        my $possible = _find_fixed($struct, $re, 0, $struct->{pow})
                // return $self->set_error(sprintf(
                    'in pow over pluslist, no source found for (%s) %s',
                    $c, $re->str
                ));
        next if @$possible == 0;    # possible with no new constraint
        if (@$possible == 1) {
            # fix each subset as a mandatory grouping
            for my $inset (@{ $possible->[0] }) {
                return unless _fix_propagate($struct, $inset);
                # if everything is fixed, we're done
                return $struct->{assign} unless keys %{ $struct->{unfixed} };
            }
        } else {
            push @{ $struct->{sets} }, $possible;
        }
    }
    # TODO: pick a possibility to return once we have a testcase
    return $self->set_error(sprintf(
        'failed to fix an assignment'
    ));
}

# Fix an assignment, and recursively propagate the results into the structure.
sub _fix_propagate {
    my($struct, $inset) = @_;

    # update %unfixed
    die "logic error"
            if grep !$struct->{unfixed}{$_}, @$inset;
    my @args = delete @{ $struct->{unfixed} }{@$inset};

    # update @assign
    push @{ $struct->{assign} }, $inset;

    # update @fixed
    push @{ $struct->{fixed} }, (@args > 1) ? Axiom::Expr->new({
        type => 'pluslist',
        args => [
            map $_->copy,
                map $_->type eq 'pluslist' ? @{ $_->args } : $_,
                    @args
        ],
    }) : $args[0];
    # .. and propagate
    return _propagate_fix($struct, $inset);
}

# Given a newly-fixed assignement, recursively propagate the results
# into the structure.
sub _propagate_fix {
    my($struct, $inset) = @_;
    return unless @$inset;
    # %unfixed, @assign and @fixed have already been updated
    my %fixing = map +($_ => 1), @$inset;
    my @pend;
  RI:
    for my $ri (0 .. $#{ $struct->{sets} }) {
        # the set of all possible groups of assignments for $right->[$ri]
        my $set = $struct->{sets}[$ri];
        for my $gi (0 .. $#$set) {
            # one possible group of assignments
            my $group = $set->[$gi];
            for my $ai (0 .. $#$group) {
                # one assignment of the set
                my $assign = $group->[$ai];
                # skip if none of the newly fixed elements are mentioned
                next unless grep $fixing{$_}, @$assign;
                # if it's the same assignment, it is no longer a constraint
                if (join(':', sort @$assign) eq join(':', sort @$inset)) {
                    splice @$group, $ai, 1;
                    # if that leaves the group empty, it is no constraint,
                    # so none of the other groups matter
                    if (@$group == 0) {
                        $set = [];
                        next RI;
                    }
                }
                # else this group of assignments is incompatible with the fix
                splice @$set, $gi, 1;
                # if that was the last group, we failed
                return $struct->{self}->set_error(sprintf(
                    'fixing (%s) leaves no valid assignment for RHS %s',
                    join(q', ', @$inset), $ri
                )) if @$set == 0;
                # if that leaves only one group, it is mandatory
                # but complete work for this fix before propagating
                push @pend, $set->[0] if @$set == 1;
            }
        }
    }
    for my $group (@pend) {
        for my $assign (@$group) {
            return unless _fix_propagate($struct, $assign);
        }
    }
    return 1;
}

# For already-fixed assignments that have not yet been tried, try each way
# of constructing $re from $pow combinations of fixed assignments and
# not-yet fixed assignments.
# On failure, returns undef; else returns an arrayref of possible sets of
# assignments.
sub _find_fixed {
    my($struct, $re, $min, $pow) = @_;
    my @assign;
    if ($pow == 0) {
        return [];
    } elsif ($pow == 1) {
        for my $fi ($min .. $#{ $struct->{fixed} }) {
            my $le = $struct->{fixed}[$fi];
            return [] unless $le->diff($re, 1);
        }
    } else {
        for my $fi ($min .. $#{ $struct->{fixed} }) {
            my $le = $struct->{fixed}[$fi];
            my $re2 = _try_divide($re, $le) or next;
            my $assign = _find_fixed($struct, $re2, $fi, $pow - 1)
                    or next;
            # if it was possible with no constraint, we're done
            return [] unless @$assign;
            push @assign, @$assign;
        }
    }
    my $assign = _find_single_unfixed($struct, $re, 0, $pow);
    push @assign, @$assign if $assign;
    return @assign ? \@assign : undef;
}

# For unfixed exprs that have not yet been tried, try each way of constructing
# $re from $pow combinations of single exprs and combinations of exprs.
# On failure, returns undef; else returns an arrayref of possible sets of
# assignments.
sub _find_single_unfixed {
    my($struct, $re, $min, $pow) = @_;
    my @assign;
    if ($pow == 0) {
        return [];
    } elsif ($pow == 1) {
        for my $li (sort { $a <=> $b }
            grep $_ >= $min,
                keys %{ $struct->{unfixed} }
        ) {
            my $le = $struct->{unfixed}{$li} // next;
            push @assign, [ [ $li ] ] unless $le->diff($re, 1);
        }
    } else {
        for my $li (sort { $a <=> $b }
            grep $_ >= $min,
                keys %{ $struct->{unfixed} }
        ) {
            my $le = $struct->{unfixed}{$li};
            my($re2, $pow2) = ($re, $pow);
            while ($pow2 > 1) {
                $re2 = _try_divide($re2, $le) or last;
                --$pow2;
                delete local $struct->{unfixed}{$li};
                my $assign = _find_single_unfixed($struct, $re2, $li + 1, $pow2)
                        or next;
                push @assign, map [ [ $li ], @$_ ], @$assign;
            }
            my $fullpow = Axiom::Expr->new({
                type => 'pow',
                args => [ $le->copy, _newc($pow) ],
            })->clean;
            push @assign, [ [ $li ] ] unless $fullpow->diff($re, 1);
        }
    }
    my $assign = _find_multi_unfixed($struct, $re, $pow);
    push @assign, @$assign if $assign;
    return @assign ? \@assign : undef;
}

# For unfixed exprs that have not yet been tried, try each way of constructing
# $re from $pow combinations each of at least two exprs.
# On failure, returns undef; else returns an arrayref of possible sets of
# assignments.
sub _find_multi_unfixed {
    my($struct, $re, $pow) = @_;
    # every contributing LHS expression should appear in a pluslist,
    # which may be raised to a power, which will be combined in a mullist;
    # the sum of the powers must equal $pow.
    my $sum = 0;
    my @ra = map {
        my($e, $p) = ($_, 1);
        if ($e->type eq 'pow') {
            ($e, my($pe)) = @{ $e->args };
            $pe->is_const or return undef;
            $pe->type eq 'integer' or return undef;
            $p = $pe->rat;
            $p > 0 or return undef;
        }
        $sum += $p;
        return undef unless $e->type eq 'pluslist';
        [ map $_->split_prod->[1], @{ $e->args } ];
    } ($re->type eq 'mullist') ? @{ $re->args } : $re;
    return undef unless $pow == $sum;
    # LHS elements cannot be pluslists, so only one set of assignments possible
    my @assign;
    my %u = %{ $struct->{unfixed} };
    for (@ra) {
        my @this_set;
        for my $rae (@$_) {
            my $ui = List::Util::first(sub {
                ! $u{$_}->diff($rae, 1)
            }, keys %u) // return undef;
            push @this_set, $ui;
            delete $u{$ui};
        }
        push @assign, \@this_set;
    }
    return [ \@assign ];
}

# Ignoring any constant multiplier, return an expression representing
# $re / $le if it can be constructed by cancellation or subtraction
# of existing powers, else undef.
sub _try_divide {
    my($re, $le) = @_;
    return $re if $le->is_const;
    my @la = map $_->type eq 'pow' ? [@{ $_->args }] : [ $_, _newc() ],
            ($le->type eq 'mullist') ? @{ $le->args } : $le;
    my @ra = map $_->type eq 'pow' ? [@{ $_->args }] : [ $_, _newc() ],
            ($re->type eq 'mullist') ? @{ $re->args } : $re;
    for (@la) {
        my($la, $lp) = @$_;
        my $ri = List::Util::first(sub {
            ! $la->diff($ra[$_][0], 1);
        }, 0 .. $#ra) // return undef;
        my($ra, $rp) = @{ $ra[$ri] };
        $rp = Axiom::Expr->new({
            type => 'pluslist',
            args => [ $rp->copy, $lp->negate ],
        })->clean;
        if ($rp->is_const) {
            my $rpc = $rp->rat;
            return undef if $rpc < 0;
            splice(@ra, $ri, 1), next if $rpc == 0;
        }
        $ra[$ri][1] = $rp;
    }
    @ra = map {
        my($e, $p) = @$_;
        ($p->is_const && $p->rat == 1) ? $e : Axiom::Expr->new({
            type => 'pow',
            args => [ $e->copy, $p->copy ],
        });
    } @ra;
    return +(@ra == 0) ? _newc()
        : (@ra == 1) ? $ra[0]
        : Axiom::Expr->new({
            type => 'mullist',
            args => \@ra,
        });
}

#
# validation helper functions
#

# Return an arrayref of exprs, combining elements of $args using a $list
# list type. We verify that each element of $args is used exactly once,
# and return a false value on error.
sub _assign {
    my($self, $args, $assign, $list) = @_;
    my $argc = @$args;
    my $v = '';
    vec($v, $_, 1) = 1 for 0 .. $argc - 1;
    my @result = map {
        for (@$_) {
            return $self->set_error(sprintf(
                'Invalid arg $_ of $argc in assignment of (%s)',
                join ', ', map $_->str, @$args
            )) if $_ < 0 || $_ >= $argc;
            return $self->set_error(sprintf(
                '%s accounted twice for %s argument %s',
                $self->rulename, $_, $args->[$_]->str,
            )) if vec($v, $_, 1) == 0;
            vec($v, $_, 1) = 0;
        }
        my @set = @$args[@$_];
        @set > 1 ? Axiom::Expr->new({
            type => $list,
            args => \@set,
        }) : $set[0];
    } @$assign;
    vec($v, $_, 1) == 0 or return $self->set_error(sprintf(
        '%s did not account for %s argument %s',
        $self->rulename, $_, $args->[$_]->str,
    )) for 0 .. $argc - 1;
    return \@result;
}

# Wrap the given expr in layers of 'forall' over each of the specified vars.
sub _wrap {
    my($vars, $expr) = @_;
    $expr = Axiom::Expr->new({
        type => 'forall',
        args => [ $_->copy, $expr ],
    }) for reverse @$vars;
    return $expr;
}

# Split an array into two: the specified indices and the rest.
sub _pick_args {
    my($array, $args) = @_;
    my %pick = map +($_ => 1), @$args;
    my(@picked, @unpicked);
    for (0 .. $#$array) {
        push @{ delete($pick{$_}) ? \@picked : \@unpicked }, $array->[$_];
    }
    return +(\@picked, \@unpicked);
}

# return [ (@$in)^$count ]
sub _expand_r {
    my($in, $count) = @_;
    return [ _newc() ] if $count == 0;
    return [] unless @$in;
    my $result = [];
    my($this, @rest) = @$in;
    return [
        map {
            my $i = $_;
            my $comb = _newc(_comb($count, $i));
            my $pow = ($i == 0) ? _newc()
                : ($i == 1) ? $this
                : Axiom::Expr->new({
                    type => 'pow',
                    args => [ $this, _newc($i) ],
                });
            map Axiom::Expr->new({
                type => 'mullist',
                args => [ $comb->copy, $pow->copy, $_ ],
            }), @{ _expand_r(\@rest, $count - $i) };
        } 0 .. $count
    ];
}

sub _newc { Axiom::Expr->new_const(shift // 1) }
{
    my @comb; BEGIN { @comb = [[ Math::BigRat->new(1) ]] }
    sub _comb {
        my($n, $r) = @_;
        return 0 if $r < 0 || $r > $n;
        return 1 if $r == 0 || $r == $n;
        return $comb[$n][$r] //= _comb($n - 1, $r - 1) + _comb($n - 1, $r);
    }
}

# Given rational b, q, return log_b(q) if rational, else undef. We consider
# only principal roots, so for example we return 1/2 for (4, 2) but undef
# for (4, -2).
sub _log_rat {
    my($b, $q) = @_;
    return undef if $b == 0 || $q == 0 || $b == 1 || ($b > 0 && $q < 0);
    return 0 if $q == 1;
    return 1 if $b == $q;
    my($bn, $bd) = $b->parts;
    my($qn, $qd) = $q->parts;
    if ($bd > 1 || $qd > 1) {
        $bn *= $bd;
        $qn *= $qd;
    }
    my($bs, $qs) = (1, 1);
    ($bn, $bs) = (-$bn, -1) if $bn < 0;
    ($qn, $qs) = (-$qn, -1) if $qn < 0;
    my $r = _log_nat(($bn > $qn) ? ($qn, $bn) : ($bn, $qn))
            // return undef;
    $r = 1/$r if $bn > $qn;
    return $r unless $bs < 0;
    return +($r->numerator & 1)
        ? ($qs < 0 ? $r : undef)
        : ($qs > 0 ? $r : undef);
}

# Given positive integer b, z with b < z, return log_b(z) if rational, else
# undef.
sub _log_nat {
    my($b, $z) = @_;
    my $s = Math::BigRat->new(0);
    ++$s, $z /= $b until $z % $b;
    return undef if $z > $b;
    return $s if $z == 1;
    my $t = _log_nat($z, $b) // return undef;
    return $s + 1/$t;
}

1;
