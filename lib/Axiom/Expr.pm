package Axiom::Expr;

use v5.10;
use strict;
use warnings;

use Math::BigRat;
use List::Util ();
use Carp qw{ confess };

our $SUCCEED = qr{(?=)};
our $FAIL = qr{(?!)};
our $DICT;

my %listtype = map +($_ => 1), qw{ pluslist mullist andlist orlist };

my %classtype = (
    (map +($_ => 'Axiom::Expr::Const'), qw{ integer rational }),
    (map +($_ => 'Axiom::Expr::Name'), qw{ name }),
    (map +($_ => 'Axiom::Expr::Iter'), qw{ sum prod integral inteval }),
    (map +($_ => 'Axiom::Expr::Relation'), qw{ req rle rlt rge rgt }),
    (map +($_ => 'Axiom::Expr::Quant'), qw{ forall exists }),
);

sub new {
    my($class, $hash) = @_;
    my($type, $args) = @$hash{qw{ type args }};
    return $args->[0] if $type eq 'nothing';
    if ($listtype{$type}) {
        return $args->[0] if @$args == 1;
        $args = [ map {
ref($_) or confess(Dumper($hash));
            $_->type eq $type ? @{ $_->args } : $_
        } @$args ];
    }
    my $targclass = $classtype{$type} // 'Axiom::Expr';
    $class = $targclass unless $class->isa($targclass);
    return bless {
        type => $type,
        args => $args,
    }, $class;
}

sub new_const {
    my($class, $const) = @_;
    return Axiom::Expr::Const->new_rat(Math::BigRat->new($const));
}

sub local_dict {
    my($class, $localdict) = @_;
    return Axiom::Expr::LocalDict->new($localdict);
}

sub args { shift->{args} }
sub type { shift->{type} }
sub rawexpr {
    my($self) = @_;
    return $self->{''} // $self->str;
}

sub valuetype {
    my($self) = @_;
    my $t = $self->type;
    state %vt = (
        (map +($_ => 'rat'), qw{
            integer rational sum prod integral inteval
            pluslist negate mullist recip pow factorial min max
        }),
        (map +($_ => 'bool'), qw{
            req rle rlt rge rgt forall exists
            implies andlist orlist
        }),
        # for now
        (name => 'rat'),
    );
    return $vt{$t} if defined $vt{$t};
    return $self->args->[1]->valuetype if $t eq 'given';
    die "unknown type '$t' in valuetype";
}

sub is_atom { 0 }
sub is_const { 0 }
sub is_iter { 0 }
sub is_relation { 0 }
sub is_quant { 0 }
sub is_rat { shift->valuetype eq 'rat' }
sub is_bool { shift->valuetype eq 'bool' }
sub is_list { $listtype{ shift->type } }
sub has_newvar { 0 }
sub check_const { undef }

sub is_unencumbered {
    my($self, $loc) = @_;
    my $ancestry = $self->ancestry($loc);
    for my $i (reverse 0 .. $#$loc) {
        my $e = $ancestry->[$i];
        return 0 unless $e->is_bool;
        return 0 if $e->is_relation;
        next if $e->is_quant;
        my $t = $e->type;
        next if $t eq 'andlist' || $t eq 'orlist';
        my $arg = $loc->[$i];
        if ($t eq 'implies') {
            next if $arg == 2;
            return 0;
        } elsif ($t eq 'given') {
            return 1 if $arg == 1;  # shortcircuit true
            return 0;
        }
        die "unknown type '$t' in is_unencumbered";
    }
    return 1;
}

sub is_number {
    my($self, $given) = @_;
    return 0 unless $self->valuetype eq 'rat';
    return 1 if $self->is_atom;
    return 0 if List::Util::any(sub {
        !$_->is_number($given);
    }, @{ $self->args });
    # FIXME: unwarranted assumption on integral
    return 1 if $self->is_iter;
    my $t = $self->type;
    my $cb = {
        (map +($_ => sub { 1 }), qw{ pluslist negate mullist min max }),
        recip => sub {
            my $arg = $self->args->[0];
            return 1 if $arg->test_nonzero($given);
            return 0;
        },
        pow => sub {
            my($base, $pow) = @{ $self->args };
            # FIXME: disallow negative base with non-integer pow
            return 1 if $base->test_nonzero($given);
            return 1 if $pow->test('rgt', 0, $given);
            return 0;
        },
        factorial => sub {
            my $arg = $self->args->[0];
            # TODO: we'll need domain constraints on variables to do better,
            # so keep it tight for now
            return 1 if $arg->type eq 'integer' && $arg->rat >= 0;
            return 0;
        },
    }->{$t} // die "Unknown type '$t' in is_number";
    return $cb->();
}

sub given {
    my($self) = @_;
    if ($self->type eq 'given') {
        my $arg = $self->args->[0];
        return +($arg->type eq 'andlist') ? @{ $arg->args } : ($arg);
    }
    return ();
}

sub is_neg {
    my($self) = @_;
    my $type = $self->type;
    return $type eq 'negate' || (
        $type eq 'mullist' && $self->args->[0]->is_neg
    );
}
sub negate {
    my($self) = @_;
    my $type = $self->type;
    if ($type eq 'negate') {
        return $self->args->[0]->copy;
    }
    if ($type eq 'mullist') {
        my $other = $self->copy;
        $other->args->[0] = $other->args->[0]->negate;
        if ($other->args->[0]->type eq 'integer'
                && $other->args->[0]->rat == 1) {
            shift @{ $other->args };
            $other = $other->args->[0] if @{ $other->args } == 1;
        }
        return $other;
    }
    return Axiom::Expr->new({
        type => 'negate',
        args => [ $self->copy ],
    });
}
sub is_recip {
    my($self) = @_;
    my $type = $self->type;
    return $type eq 'recip' || (
        $type eq 'rational' && (
            $self->args->[0] eq '1' || $self->args->[0] eq '-1'
        )
    );
}
sub recip {
    my($self) = @_;
    my $type = $self->type;
    if ($type eq 'recip') {
        return $self->args->[0]->copy;
    }
    if ($self->is_const) {
        return Axiom::Expr->new_const(1 / $self->rat);
    }
    if ($type eq 'pow') {
        my $other = $self->copy;
        $other->args->[0] = $other->args->[0]->recip;
        return $other;
    }
    return Axiom::Expr->new({
        type => 'recip',
        args => [ $self->copy ],
    });
}

sub test_nonzero {
    my($self, $given) = @_;
    my $zero = $self->test('req', 0, $given);
    return defined($zero) ? 1 - $zero : undef;
}

sub test_sign {
    my($self, $given) = @_;
    my $zero = $self->test('req', 0, $given);
    return undef unless defined $zero;
    return 0 if $zero;
    my $pos = $self->test('rgt', 0, $given);
    return undef unless defined $pos;
    return 1 if $pos;
    return -1;
}

sub _test_exact {
    my($rel, $v1, $v2) = @_;
    my $cb = {
        req => sub { $v1 == $v2 },
        rlt => sub { $v1 < $v2 },
        rle => sub { $v1 <= $v2 },
        rgt => sub { $v1 > $v2 },
        rge => sub { $v1 >= $v2 },
    }->{$rel} // die "Unknown relation '$rel'";
    return $cb->() ? 1 : 0;
}

# Return 1 if X r2 v2 implies X r1 v1, 0 if it implies the opposite, undef
# if neither is forced.
sub _test_const {
    my($r1, $v1, $r2, $v2) = @_;
    my $cb = {
        req => {
            req => sub { $v2 == $v1 ? 1 : 0 },
            rlt => sub { $v2 <= $v1 ? 0 : undef },
            rle => sub { $v2 < $v1 ? 0 : undef },
            rgt => sub { $v2 >= $v1 ? 0 : undef },
            rge => sub { $v2 > $v1 ? 0 : undef },
        },
        rlt => {
            req => sub { $v2 < $v1 ? 1 : 0 },
            rlt => sub { $v2 <= $v1 ? 1 : undef },
            rle => sub { $v2 < $v1 ? 1 : undef },
            rgt => sub { $v2 >= $v1 ? 0 : undef },
            rge => sub { $v2 >= $v1 ? 0 : undef },
        },
        rle => {
            req => sub { $v2 <= $v1 ? 1 : 0 },
            rlt => sub { $v2 <= $v1 ? 1 : undef },
            rle => sub { $v2 <= $v1 ? 1 : undef },
            rgt => sub { $v2 >= $v1 ? 0 : undef },
            rge => sub { $v2 > $v1 ? 0 : undef },
        },
        rgt => {
            req => sub { $v2 > $v1 ? 1 : 0 },
            rlt => sub { $v2 <= $v1 ? 0 : undef },
            rle => sub { $v2 <= $v1 ? 0 : undef },
            rgt => sub { $v2 >= $v1 ? 1 : undef },
            rge => sub { $v2 > $v1 ? 1 : undef },
        },
        rge => {
            req => sub { $v2 >= $v1 ? 1 : 0 },
            rlt => sub { $v2 <= $v1 ? 0 : undef },
            rle => sub { $v2 < $v1 ? 0 : undef },
            rgt => sub { $v2 >= $v1 ? 1 : undef },
            rge => sub { $v2 >= $v1 ? 1 : undef },
        },

    }->{$r1}{$r2} // die "Unknown relation combo '$r1' with '$r2'";
    return $cb->();
}

# Return 1 if known to be true, 0 if known to be false, undef if not known.
sub test {
    my($self, $rel1, $val1, $given) = @_;
    return _test_exact($rel1, $self->rat, $val1)
            if $self->is_const;
    # if not const we must rely on given constraints
    return 0 unless defined $given;
    my @given = ($given->type eq 'andlist') ? @{ $given->args } : ($given);
    for my $g (@given) {
        # CHECKME: do we need to handle quantifiers?
        next unless $g->is_relation;
        my($rel2, $left, $right) = ($g->type, @{ $g->args });
        my $targ;
        if (!$self->diff($left, 1)) {
            $targ = $right;
        } elsif (!$self->diff($right, 1)) {
            $targ = $left;
            $rel2 = $g->inverse_type;
        } else {
            next;
        }
        next unless $targ->is_const;
        my $known = _test_const($rel1, $val1, $rel2, $targ->rat);
        return $known if defined $known;
    }
    return undef;
}

{
    # TODO: [mullist a [recip b]] => 'a/b' rather than 'a.(1/b)'
    # .. and try to unify it with a cleaner [pluslist a [negate b]]
    # TODO: iterators should apply 'req' precedence to first two args,
    # and base precedence to third arg - but using {} to bracket. Last arg
    # should however have mandatory {}.
    my %stringify = (
        forall => [ 0, 0, "\\A%s: %s" ],
        exists => [ 0, 0, "\\E%s: %s" ],
        req => [ 6, 0, "%s = %s" ],
        rlt => [ 6, 0, "%s < %s" ],
        rle => [ 6, 0, "%s <= %s" ],
        rgt => [ 6, 0, "%s > %s" ],
        rge => [ 6, 0, "%s >= %s" ],
        implies => [ 6, 0, "%s -> %s" ],
        andlist => [ 6, -1, " & " ],
        orlist => [ 6, -1, " | " ],
        integer => [ sub { ($_[0][0] < 0) ? 5 : 0 }, 0, "%s" ],
        rational => [ sub { ($_[0][0] < 0) ? 5 : 4 }, 0, "%s/%s" ],
        name => [ 0, 0, "%s" ],
        function => [ 0, 1, "%s(%s)", ", " ],
        negate => [ 5, 0, "-%s" ],
        pluslist => [ 5, -1, " + " ],
        recip => [ 4, 0, "1 / %s" ],
        mullist => [ 3, -1, " . " ],
        pow => [ 2, 0, "%s ^ %s" ],
        factorial => [ 1, 0, "%s!" ],
        sum => [ 0, 0, "\\sum_{%s=%s}^{%s}{%s}" ],
        prod => [ 0, 0, "\\prod_{%s=%s}^{%s}{%s}" ],
        integral => [ 0, 0, "\\int_{%s=%s}^{%s}{%s}" ],
        inteval => [ 0, 0, "\\inteval_{%s=%s}^{%s}{%s}" ],
        min => [ 0, 0, "\\min(%s, %s)" ],
        max => [ 0, 0, "\\max(%s, %s)" ],
        given => [ 0, 0, "\\given_{%s}{%s}" ],
    );
    sub str {
        my($self, $prec) = @_;
        my $ify = $stringify{$self->type}
                or die "No stringify available for @{[ $self->type ]}";
        my($sprec, $sstyle, $sfmt, $sfmt2) = @$ify;
        $sprec = $sprec->($self->args) if ref $sprec;
        my $s = $self->{str} //= do {
            my @args = $self->is_atom
                ? @{ $self->args }
                : map($_->str($sprec), @{ $self->args });
            my $t = ($sstyle == 0) ? sprintf($sfmt, @args)
                : ($sstyle < 0) ? join($sfmt, @args)
                : do {
                    splice @args, $sstyle, 0 + @args,
                            join $sfmt2, @args[$sstyle .. $#args];
                    sprintf($sfmt, @args);
                };
            $t =~ s{\+\s*-}{-}g if $self->type eq 'pluslist';
            $t;
        };
        $s = "($s)" if defined($prec) && $prec < $sprec;
        return $s;
    }
}

sub _clean {
    my($self, $given) = @_;
    return undef if $self->is_atom;
    my $type = $self->type;
    my $args = $self->args;
    for (@$args) {
        my $new = $_->_clean($given) // next;
        $_ = $new;
        redo;
    }
    my $sub = {
        req => undef,
        rlt => undef,
        rle => undef,
        rgt => undef,
        rge => undef,
        function => undef,
        expr => sub { return $self->args->[0] },
        braceexpr => sub { return $self->args->[0] },
        parenexpr => sub { return $self->args->[0] },
        given => sub {
            my($p, $q) = @$args;
            return $q->clean($p);
        },
        forall => sub {
            my($var, $child) = @$args;
            if ($child->type eq 'forall'
                && $var->name gt $child->args->[0]->name
            ) {
                # \b \a x -> \a \b x
                return Axiom::Expr->new({
                    type => 'forall',
                    args => [
                        $child->args->[0]->copy,
                        Axiom::Expr->new({
                            type => 'forall',
                            args => [
                                $var->copy,
                                $child->args->[1]->copy,
                            ],
                        }),
                    ],
                });
            }
            return undef;
        },
        andlist => sub {
            # &(null) -> true
            return Axiom::Expr->new({
                type => 'integer',  # FIXME: may need a bool type
                args => [ '1' ],
            }) if @$args == 0;

            # &(x) -> x
            return $args->[0] if @$args == 1;

            return undef;
        },
        orlist => sub {
            # |(null) -> false
            return Axiom::Expr->new({
                type => 'integer',  # FIXME: may need a bool type
                args => [ '0' ],
            }) if @$args == 0;

            # |(x) -> x
            return $args->[0] if @$args == 1;

            return undef;
        },
        pluslist => sub {
            # +(null) -> 0
            return Axiom::Expr->new({
                type => 'integer',
                args => [ '0' ],
            }) if @$args == 0;

            # +(x) -> x
            return $args->[0] if @$args == 1;

            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                if ($arg->type eq 'pluslist') {
                    # +(a, +(b, c), d) -> +(a, b, c, d)
                    splice @$args, $i, 1, @{ $arg->args };
                    return $self;
                }
                if ($arg->is_const) {
                    if ($arg->args->[0] eq '0') {
                        # +(a, 0, b) -> +(a, b)
                        splice @$args, $i, 1;
                        return $self;
                    }
                }
            }

            # collate const multiples of the same things
            my @split = map {
                my $e = $_;
                my $em = Math::BigRat->new(1);
                if ($e->type eq 'negate') {
                    $em = -$em;
                    $e = $e->args->[0];
                }
                if ($e->type eq 'mullist') {
                    my $ea = $e->args;
                    if ($ea->[0]->is_const) {
                        $em *= $ea->[0]->rat;
                        $e = (@$ea > 2)
                            ? Axiom::Expr->new({
                                type => 'mullist',
                                args => [ map $_->copy, @$ea[1 .. $#$ea] ],
                            })
                            : $ea->[1];
                    }
                }
                if ($e->is_const) {
                    $em *= $e->rat;
                    $e = undef;
                }
                [ $e, $em ];
            } @$args;

            for my $ai (0 .. $#$args - 1) {
                my($a, $am) = @{ $split[$ai] };
                my @found;
                for my $bi ($ai + 1 .. $#$args) {
                    my($b, $bm) = @{ $split[$bi] };
                    next if defined($a) != defined($b);
                    next if defined($a) && $a->diff($b, 1, 1);
                    push @found, $bi;
                    $am += $bm;
                }
                if (@found) {
                    splice @$args, $_, 1 for reverse @found;
                    my $mult = Axiom::Expr->new_const($am);
                    my $repl = defined($a) ? do {
                        my $mulargs = $a->type eq 'mullist' ? $a->args : [ $a ];
                        Axiom::Expr->new({
                            type => 'mullist',
                            args => [ $mult, map $_->copy, @$mulargs ],
                        });
                    } : $mult;
                    $args->[$ai] = $repl->clean($given);
                    return $self;
                }
            }

            my(@con, @plus, @minus) = ();
            for (0 .. $#$args) {
                push @{
                    $args->[$_]->is_const ? \@con
                    : $args->[$_]->is_neg ? \@minus : \@plus
                }, $_;
            }

            if (@plus && @minus) {
                for my $m (@minus) {
                    my $nm = $args->[$m]->negate;
                    for my $p (@plus) {
                        next if $nm->diff($args->[$p], 1);
                        # +(a, b, c, -b) -> +(a, c)
                        for (sort { $b <=> $a } $m, $p) {
                            splice @$args, $_, 1;
                        }
                        return $self;
                    }
                }
            }

            # This should probably change
            # +(-a, b, -const) -> +(b, -const, -a)
            # +(-a, b, const) -> +(const, b, -a)
            my @order = (@con && $args->[$con[0]]->args->[0] =~ /^-/)
                ? (@plus, @con, @minus)
                : (@con, @plus, @minus);
            if (grep $order[$_] > $order[$_ + 1], 0 .. @order - 2) {
                @$args = @$args[@order];
                return $self;
            }
            return undef;
        },
        negate => sub {
            my $arg = $args->[0];
            # -(-(a)) -> a
            return $arg->args->[0] if $arg->type eq 'negate';

            # -(const) -> eval(-const)
            return $arg->negate if $arg->is_const;

            # -(a - b) -> b - a
            return Axiom::Expr->new({
                type => 'pluslist',
                args => [ map $_->negate, @{ $arg->args } ],
            }) if $arg->type eq 'pluslist';

            # -(a.b) -> (-a).b
            if ($arg->type eq 'mullist') {
                $arg->args->[0] = $arg->args->[0]->negate;
                return $arg;
            }

            # -x -> (-1 . x)
            return Axiom::Expr->new({
                type => 'mullist',
                args => [
                    Axiom::Expr->new({ type => 'integer', args => [ '-1' ] }),
                    $arg,
                ],
            });
        },
        mullist => sub {
            # x(null) -> 1
            return Axiom::Expr->new({
                type => 'integer',
                args => [ '1' ],
            }) if @$args == 0;

            # x(a) -> a
            return $args->[0] if @$args == 1;

            my(@const, @neg) = ();
            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                if ($arg->type eq 'mullist') {
                    # x(a, x(b, c), d) -> x(a, b, c, d)
                    splice @$args, $i, 1, @{ $arg->args };
                    return $self;
                }
                if ($arg->is_const) {
                    if ($arg->args->[0] eq '0') {
                        # x(a, 0, b) -> 0
                        return $arg;
                    }
                    if ($arg->type eq 'integer' && $arg->args->[0] eq '1') {
                        # x(a, 1, b) -> x(a, b)
                        splice @$args, $i, 1;
                        return $self;
                    }
                    push @const, $i;
                } elsif ($arg->is_neg) {
                    push @neg, $i;
                }
            }

            # 3.(-a).(-b).(-c) -> (-3)abc
            # (-a).b -> (-1).ab
            $args->[$_] = $args->[$_]->negate for @neg;

            if (@const > 1) {
                my $prod = Math::BigRat->new(1);
                $prod *= $_->rat for @$args[@const];
                $prod = -$prod if @neg & 1;
                my $repl = ($prod == 1)
                    ? undef
                    : Axiom::Expr->new_const($prod);
                # x(a, c1, b, c2) -> x(a, eval(c1 . c2), b)
                splice(@$args, $_, 1) for reverse @const;
                splice(@$args, $const[0], 0, $repl) if $repl;
                return $self;
            }

            if (@neg) {
                if (@neg & 1) {
                    if (@const) {
                        $args->[ $const[0] ] = $args->[ $const[0] ]->negate;
                    } else {
                        unshift @$args, Axiom::Expr->new({
                            type => 'integer',
                            args => [ '-1' ],
                        });
                    }
                }
                return $self;
            }

            for (my $i = 0; $i < @$args; ++$i) {
                my $arg = $args->[$i];
                next unless $arg->type eq 'pluslist';
                splice @$args, $i, 1;
                # x(a, b+c, d) -> +(abd, acd)
                return Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ map Axiom::Expr->new({
                        type => 'mullist',
                        args => [ $_, @$args ],
                    }), @{ $arg->{args} } ],
                });
            }

            # collate powers
            my @split = map {
                my $e = $_;
                my $en = 1;
                my $ep = Math::BigRat->new(1);
                my $epe;
                if ($e->is_neg) {
                    $e = $e->negate;
                    $en = -1;
                }
                if ($e->type eq 'pow') {
                    ($e, my $p) = @{ $e->args };
                    if ($p->is_const) {
                        $ep *= $p->rat;
                    } else {
                        $epe = $p;
                    }
                }
                if ($e->is_recip) {
                    $e = $e->recip;
                    if ($epe) {
                        $epe = $epe->negate;
                    } else {
                        $ep = -$ep;
                    }
                }
                [ $e, $en, $ep, $epe ];
            } @$args;
            for my $ai (0 .. $#$args - 1) {
                my($a, $an, $ap, $ape) = @{ $split[$ai] };
                my @found;
                for my $bi ($ai + 1 .. $#$args) {
                    my($b, $bn, $bp, $bpe) = @{ $split[$bi] };
                    next if $a->diff($b, 1, 1);
                    # avoid combining 2 . 2^a into 2^(1+a)
                    next if $a->is_const && (defined($ape) != defined($bpe));

                    push @found, $bi;
                    $an *= $bn;
                    if ($ape || $bpe) {
                        $ape //= Axiom::Expr->new_const($ap);
                        $bpe //= Axiom::Expr->new_const($bp);
                        $ape = Axiom::Expr->new({
                            type => 'pluslist',
                            args => [ $ape->copy, $bpe->copy ],
                        })->clean($given);
                    } else {
                        $ap += $bp;
                    }
                }
                if (@found) {
                    splice @$args, $_, 1 for reverse @found;
                    $ape //= Axiom::Expr->new_const($ap);
                    my $repl = Axiom::Expr->new({
                        type => 'pow',
                        args => [ $a->copy, $ape->copy ],
                    });
                    $repl = $repl->negate if $an < 0;
                    $args->[$ai] = $repl->clean($given);
                    return $self;
                }
            }

            my(@con, @mul, @pow, @div) = ();
            for (0 .. $#$args) {
                push @{
                    $args->[$_]->is_const ? \@con
                    : $args->[$_]->type eq 'pow' ? \@pow
                    : $args->[$_]->type eq 'recip' ? \@div : \@mul
                }, $_;
            }
            # Not sure what we want here
            # x(a, const p/q, 1/b, c, 1/d) -> x(const p/q, a, c, 1/b, 1/d)
            my @order = (@con, @mul, @pow, @div);
            my $changed = grep { $order[$_] > $order[$_ + 1] } 0 .. @order - 2;
            @$args = @$args[@order] if $changed;

            return $changed ? $self : undef;
        },
        recip => sub {
            my $arg = $args->[0];
            if ($arg->type eq 'recip') {
                my $argarg = $arg->args->[0];
                return $argarg if $argarg->test_nonzero($given);
            }

            # 1/(p/q) -> q/p
            return Axiom::Expr->new_const(1 / $arg->rat) if $arg->is_const;

            # 1/(a.b) -> 1/a . 1/b
            return Axiom::Expr->new({
                type => 'mullist',
                args => [ map Axiom::Expr->new({
                    type => 'recip',
                    args => [ $_ ],
                }), @{ $arg->args } ],
            }) if $arg->type eq 'mullist';

            # 1/(a^b) -> (1/a)^b
            return Axiom::Expr->new({
                type => 'pow',
                args => [
                    Axiom::Expr->new({
                        type => 'recip',
                        args => [ $arg->args->[0]->copy ],
                    }),
                    $arg->args->[1]->copy,
                ],
            }) if $arg->type eq 'pow';

            return undef;
        },
        pow => sub {
            my($val, $pow) = @{ $args };
            if ($pow->type eq 'integer') {
                my $powi = $pow->rat;
                # x^0 -> 1
                return Axiom::Expr->new({
                    type => 'integer',
                    args => [ '1' ],
                }) if $powi == 0 && $val->test_nonzero($given);

                # x^1 -> x
                return $val if $powi eq '1';

                # c1^c2 -> eval(c1^c2)
                if ($val->is_const) {
                    my $vali = $val->rat;
                    return Axiom::Expr->new_const(
                        $vali ** $powi
                    ) if $vali || $powi;
                }
            }
            if ($val->type eq 'integer') {
                my $vali = $val->rat;
                return Axiom::Expr->new({
                    type => 'integer',
                    args => [ '0' ],
                }) if $vali == 0 && $pow->test_nonzero($given);
            }

            # 1^x -> 1
            return $val
                    if $val->type eq 'integer' && $val->args->[0] eq '1';

            # pow(a, -b) -> 1 / pow(a, b)
            return Axiom::Expr->new({
                type => 'recip',
                args => [ Axiom::Expr->new({
                    type => 'pow',
                    args => [ $val->copy, $pow->negate ],
                }) ],
            }) if $pow->is_neg;

            # pow(c1, c2 + x) -> eval(c1^c2) . pow(c1, x)
            if ($val->is_const && $pow->type eq 'pluslist') {
                my $pc = $pow->args->[0];
                if ($pc->type eq 'integer') {
                    my $pv = $pc->rat;
                    my $pargs = $pow->args;
                    my $vv = $val->rat;
                    return Axiom::Expr->new({
                        type => 'mullist',
                        args => [
                            Axiom::Expr->new_const($val->rat ** $pv),
                            Axiom::Expr->new({
                                type => 'pow',
                                args => [
                                    $val->copy,
                                    Axiom::Expr->new({
                                        type => 'pluslist',
                                        args => [ @$pargs[1 .. $#$pargs] ],
                                    }),
                                ],
                            }),
                        ],
                    }) if $vv || $pv;
                }
            }

            if ($val->is_neg && $pow->type eq 'integer') {
                # pow(-a, 2c) -> pow(a, 2c); pow(-a, 2c+1) -> -pow(a, 2c+1)
                my $rest = Axiom::Expr->new({
                    type => 'pow',
                    args => [ $val->negate, $pow->copy ],
                });
                return $rest->negate if $pow->args->[0] & 1;
                return $rest;
            }

            return undef;
        },
    }->{$type};
    return $sub ? $sub->() : undef;
}

sub _clean_copied {
    my($self, $given) = @_;
    while (1) {
        my $new = $self->_clean($given) // return $self;
        $self = $new;
    }
}

sub clean {
    my($self, $given) = @_;
    return $self->copy->_clean_copied($given);
}

sub bracketed {
    my($self) = @_;
    sprintf '[%s %s]', $self->type,
            join ', ', map $_->bracketed, @{ $self->args };
}

sub ancestry {
    my($self, $loc) = @_;
    my $last = $self;
    my $ret;
    return [ (map {
        $ret = $last;
        $last = $last->args->[$_ - 1];
        $ret;
    } @$loc), $last ];
}

sub find_ancestor {
    my($self, $loc, $cb) = @_;
    my $ancestry = $self->ancestry($loc);
    for my $i (reverse 0 .. @$loc) {
        return [ @$loc[0 .. $i - 1] ] if $cb->($ancestry->[$i]);
    }
    return undef;
}

sub locate {
    my($self, $location) = @_;
    return $self unless @$location;
    my $cur = $self;
    my $next;
    for my $i (0 .. $#$location) {
        $next = $cur->args->[$location->[$i] - 1];
        $cur = $next, next if defined $next && ref $next;
        die sprintf(
            "Invalid location: %s has only %s arguments for %s in %s\n",
            join('.', $i ? @$location[0 .. $i - 1] : 0),
            0 + @{ $cur->args },
            join('.', @$location),
            $self->str,
        );
    }
    return $cur;
}

sub copy {
    my($self) = @_;
    return $self->copy_with(sub { undef });
}

sub copy_with {
    my($self, $with) = @_;
    return $with->($self) // ref($self)->new({
        type => $self->type,
        args => [ map $_->copy_with($with), @{ $self->args } ],
    });
}

sub copy_with_locn {
    my($self, $with, $loc) = @_;
    $loc //= [];
    my $args = $self->args;
    return $with->($self, $loc) // ref($self)->new({
        type => $self->type,
        args => [ map $args->[$_]->copy_with_locn($with, [ @$loc, $_ + 1]),
                0 .. $#$args ],
    });
}

sub common_loc {
    my($self, $vi) = @_;
    my @all;
    $self->walk_locn(sub {
        my($expr, $loc) = @_;
        push @all, $loc if $expr->type eq 'name'
                && !$expr->binding->is_func
                && $expr->binding->id == $vi;
    });
    die "Variable index $vi not found in expr @{[ $self->str ]}" unless @all;
    return List::Util::reduce(sub {
        my @new;
        while (@$a && @$b) {
            my $la = shift @$a;
            my $lb = shift @$b;
            last if $la != $lb;
            push @new, $la;
        }
        [@new];
    }, @all);
}

sub dict_at {
    my($self, $loc) = @_;
    my $dict = $self->{dict}->clone;
    return $self->_dict_at($dict, [ @$loc ]);
}

sub _dict_at {
    my($self, $dict, $loc) = @_;
    return $dict unless @$loc;
    my $this = shift(@$loc) - 1;
    return $self->args->[$this]->_dict_at($dict, $loc);
}

sub substitute {
    my($self, $location, $replace) = @_;
# CHECKME: do we need to introduce and re-bind any local variables in $replace?
    return $replace unless @$location;
    my($off, @subloc) = @$location;
    my $args = $self->args;
    my @copy = map {
        $_ == $off - 1
            ? (@subloc
                ? $args->[$_]->substitute(\@subloc, $replace)
                : (($replace->is_list && $self->type eq $replace->type)
                    ? @{ $replace->args }
                    : $replace
                )
            )
            : $args->[$_]->copy
    } 0 .. $#$args;
    return ref($self)->new({ type => $self->type, args => \@copy });
}

sub subst_var {
    my($self, $var, $replace) = @_;
    my $vi;
    if ($var->binding) {
        $vi = $var->binding->id;
    } else {
        confess("var @{[ $var->name ]} is unbound\n");
    }
    return $self->subst_vars({ $vi => $replace });
}

sub subst_vars {
    my($self, $map) = @_;
    return $self->copy_with(sub {
        my($other) = @_;
        return undef unless $other->type eq 'name';
        my $oi = $other->binding->id;
        return undef unless $map->{$oi};
        return $map->{$oi}->copy;
    });
}

sub _apply_map {
    my($self, $a) = @_;
    if ($self->has_newvar) {
        my $intro = $self->intro_newvar;
        my $affect = $self->affect_newvar;
        my $args = $self->args;
        for (0 .. $#$args) {
            next if $_ == $intro || $_ == $affect;
            local $a->{ref} = \$args->[$_];
            $args->[$_]->_apply_map($a);
        }
        my $var = $args->[$intro];
        my $orig = $var->binding;
        my $binding = $var->_resolve_new($a->{dict});
        if ($a->{replacing} == 2) {
            die sprintf(
                'binding mismatch at %s %s', $self->type, $self->name
            ) unless $orig->id == $binding->id;
        }
        my $local = $a->{dict}->local_name($var->name, $binding);
        local $a->{ref} = \$args->[$affect];
        $args->[$affect]->_apply_map($a);
    } elsif ($self->type eq 'name') {
        if ($a->{replacing}) {
            my $binding = $self->binding;
            return if $binding && $binding->is_func;
            $self->_resolve($a->{dict});
            if ($a->{replacing} == 2) {
                my $new = $self->binding;
                die sprintf(
                    'binding mismatch at %s %s', $self->type, $self->name
                ) unless $binding->id == $new->id;
            }
            return;
        }
        # not being introduced, so must be resolved or replaced
        my $binding = $self->binding;
        return if $binding->is_func;
        my $id = $binding->id;
        if ($a->{map}{$id}) {
            my($repl, $known) = $a->{known}{$id}
                ? ($a->{known}{$id}->copy, 2)
                : ($a->{map}{$id}->copy, 1);
            {
                local $a->{replacing} = $known;
                $repl->_apply_map($a);
            }
            if ($known == 1) {
                $a->{known}{$id} = $repl;
                die sprintf('multiplicand %s is not a number', $repl->str)
                        unless $repl->is_number($a->{given});
            }
            ${ $a->{ref} } = $repl;
        } else {
            $self->_resolve($a->{dict});
        }
    } elsif ($self->type eq 'given') {
        my $args = $self->args;
        local $a->{ref} = \$args->[0];
        $args->[0]->_apply_map($a);
        local @$a{qw{ ref given }} = (\$args->[1], $args->[0]);
        $args->[1]->_apply_map($a);
    } elsif (!$self->is_const) {
        my $args = $self->args;
        for (0 .. $#$args) {
            local $a->{ref} = \$args->[$_];
            $args->[$_]->_apply_map($a);
        }
    }
}

# Walk the expr to do the replacements, resolving as we go.
# Variables getting introduced should be resolved but not replaced;
# others should be replaced if their old resolution matches a map id,
# else get resolved normally. Replacement exprs should be resolved but
# not recursively replaced, and we each replacement for a given id must
# resolve the same way as the first. Each replacement must also have
# a numeric value across its range.
sub apply_map {
    my($self, $dict, $map) = @_;
    $self->_apply_map({
        ref => \$self,
        dict => $dict,
        map => $map,
        known => {},
        given => undef,
        replacing => 0,
    });
    return $self;
}

sub walk_tree {
    my($self, $cb) = @_;
    $cb->($self);
    unless ($self->is_atom) {
        $_->walk_tree($cb) for @{ $self->args };
    }
    return;
}

sub walk_locn {
    my($self, $cb, $loc) = @_;
    $loc //= [];
    $cb->($self, $loc);
    unless ($self->is_atom) {
        my $args = $self->args;
        for my $i (0 .. $#$args) {
            $args->[$i]->walk_locn($cb, [ @$loc, $i + 1 ]);
        }
    }
    return;
}

sub iter_tree {
    my(@stack) = $_[0];
    return sub {
        my $self = shift(@stack) // return undef;
        push @stack, @{ $self->args } unless $self->is_atom;
        return $self;
    };
}

sub iter_locn {
    my($self, $start) = @_;
    my(@stack) = $start
        ? [ $self->locate($start), $start ]
        : [ $self, [] ];
    return sub {
        my($self, $loc) = @{ shift(@stack) // return };
        my $args = $self->args;
        push @stack, map [ $args->[$_], [ @$loc, $_ + 1 ] ], 0 .. $#$args
                unless $self->is_atom;
        return ($self, $loc);
    };
}

sub is_independent {
    my($self, $var) = @_;
    my $id = $var->binding->id;
    my $iter = $self->clean->iter_tree;
    while (my $e = $iter->()) {
        return 0 if $e->type eq 'name' && $e->binding->id == $id;
    }
    return 1;
}

sub parse {
    my($class, $dict, $text, $debug) = @_;
    my $local = $class->local_dict($dict);
    if ($text =~ _parsere($debug)) {
        return $/{Statement};
    } else {
        die "No match: <$text>\n";
    }
}

sub _diff {
    my($self, $other, $map, $exact) = @_;
    $map //= {};
    $self->type eq $other->type or return [];
    my($sa, $oa) = ($self->args, $other->args);
    @$sa == @$oa or return [];
    my $diff;
    if ($self->is_list) {
        my @sd = map {
            my $this_diff = $sa->[$_]->_diff($oa->[$_], $map, $exact);
            $this_diff ? [ $_, $this_diff ] : ();
        } 0 .. $#$sa;
        if (@sd > 1) {
            my @od = @sd;
          DiffListPair:
            for (my $si = 0; $si < @sd; ++$si) {
                my $s = $sa->[$sd[$si][0]];
                for (my $oi = 0; $oi < @od; ++$oi) {
                    # FIXME: why does passing $map in here cause failures?
                    next if $s->_diff($oa->[$od[$oi][0]], undef, $exact);
                    splice @sd, $si, 1;
                    splice @od, $oi, 1;
                    last DiffListPair if $si >= @sd;
                    redo DiffListPair;
                }
            }
            return undef unless @sd;
            return [] if $sd[0][0] != $od[0][0];
        }
        return [] if @sd > 1;
        $diff = [ $sd[0][0] + 1, @{ $sd[0][1] } ]
                if @sd;
    } else {
        # turn off exact for the introduction of a new variable, so
        # we can map [sum local i_1 f(i_1)] to [sum local i_2 f(i_2)]
        # without trying to map [local i_1] to [local i_2] otherwise.
        if ($exact && $self->has_newvar) {
            my $intro = $self->intro_newvar;
            # ignore return, this is just to set the mapping
            $sa->[$intro]->_diff($oa->[$intro], $map, 0);
        }

        for my $i (0 .. $#$sa) {
            my $_diff = $sa->[$i]->_diff($oa->[$i], $map, $exact) // next;
            return [] if $diff;
            $diff = [ $i + 1, @{ $_diff } ];
        }
    }
    return $diff;
}

sub diff {
    my($self, $other, $pure, $exact) = @_;
    my $map = {};
    my $where = $self->_diff($other, $map, $exact);
    return undef unless $where;
    return $where if $pure;
    return undef unless $self->clean->_diff($other->clean, $map, $exact);
    return $where;
}

sub find_expr {
    my($self, $expr) = @_;
    return [] if !$self->_diff($expr, {}, 0);
    return undef if $self->is_atom;
    my $args = $self->args;
    for my $i (0 .. $#$args) {
        my $loc = $args->[$i]->find_expr($expr);
        return [ $i + 1, @$loc ] if $loc;
    }
    return undef;
}

sub _resolve {
    my($self, $dict) = @_;
    $_->_resolve($dict) for @{ $self->args };
    return;
}

sub resolve {
    my($self, $dict) = @_;
    $dict = $dict->clone;   # not copy, must preserve ids
    $self->{dict} = $dict;  # store at top level of expr only
    $self->_resolve($dict);
    return;
}

package Axiom::Expr::Const {
    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        my $type = (@{ $hash->{args} } > 1 && $hash->{args}[1] != 1)
                ? 'rational' : 'integer';
        my $args = ($type eq 'rational')
                ? $hash->{args} : [ $hash->{args}[0] ];
        return bless { type => $type, args => $args }, $class;
    }
    sub new_rat {
        my($class, $rat) = @_;
        return $class->new({ args => [ $rat->parts ] });
    }
    sub is_const { 1 }
    sub is_atom { 1 }
    sub is_neg { shift->args->[0] < 0 }
    sub negate {
        my($self) = @_;
        my $other = $self->copy;
        $other->args->[0] = -$other->args->[0];
        return $other;
    }
    sub recip {
        my($self) = @_;
        return Axiom::Expr->new_const(1 / $self->rat);
    }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // ref($self)->new({
            type => $self->type,
            args => [ map Math::BigInt->new("$_"), @{ $self->args } ],
        });
    }
    sub copy_with_locn {
        my($self, $with, $loc) = @_;
        $loc //= [];
        return $with->($self, $loc) // ref($self)->new({
            type => $self->type,
            args => [ map Math::BigInt->new("$_"), @{ $self->args } ],
        });
    }
    sub bracketed { join '/', @{ shift->args } }
    sub rat {
        my($self) = @_;
        my $args = $self->args;
        use Math::BigRat;
        return Math::BigRat->new(
            $args->[0], $self->type eq 'integer' ? '1' : $args->[1],
        );
    }
    sub _diff {
        my($self, $other, $map, $exact) = @_;
        my $type = $self->type;
        return [] unless $type eq $other->type;
        my $argc = { integer => 1, rational => 2 }->{$type}
                // die "I don't know how many args a $type has";
        my($sa, $oa) = ($self->args, $other->args);
        ($sa->[$_] == $oa->[$_]) or return []
                for (0 .. $argc - 1);
        return undef;
    }
    sub _resolve { }
};

package Axiom::Expr::Name {
    use Carp qw{ confess };

    our @ISA = qw{Axiom::Expr};
    sub new {
        my($class, $hash) = @_;
        return bless { type => 'name', args => $hash->{args} }, $class;
    }
    sub is_atom { 1 }
    sub copy_with {
        my($self, $with) = @_;
        return $with->($self) // do {
            my $other = ref($self)->new({
                type => $self->type,
                args => [ @{ $self->args } ],
            });
            $other->bind($self->binding);
            $other;
        };
    }
    sub copy_with_locn {
        my($self, $with, $loc) = @_;
        $loc //= [];
        return $with->($self, $loc) // do {
            my $other = ref($self)->new({
                type => $self->type,
                args => [ @{ $self->args } ],
            });
            $other->bind($self->binding);
            $other;
        };
    }
    sub bracketed {
        my($self) = @_;
        my $b = $self->binding;
        return $b
            ? sprintf('%s %s_%s', $b->type, $self->name, $b->id)
            : sprintf('%s %s', 'unbound', $self->name);
    }
    sub _diff {
        my($self, $other, $map, $exact) = @_;
        return [] unless $self->type eq $other->type
                && $self->bindtype eq $other->bindtype;
        my($si, $oi) = map $_->binding->id, ($self, $other);
        if (defined $map->{$si}) {
            return [] unless $oi == $map->{$si};
        } else {
            return [] unless $si == $oi
                    || (!$exact && $self->name eq $other->name)
                    || ($exact || 0) < 0;
            return [] if defined $map->{"r$oi"};
            $map->{$si} = $oi;
            $map->{"r$oi"} = $si;
        }
        return undef;
    }
    sub name { shift->args->[0] }
    sub bind {
        my($self, $binding) = @_;
        $self->{binding} = $binding;
        return;
    }
    sub binding { shift->{binding} }
    sub bindtype {
        my($self) = @_;
        my $binding = $self->binding;
        confess("var ", $self->name, " is unbound") unless $binding;
        return $binding->type;
    }
    sub _resolve {
        my($self, $dict) = @_;
        my $binding = $self->binding;
        return if $binding && $binding->is_func;

        $binding = $dict->lookup($self->name) or confess sprintf(
            "Cannot resolve var %s, not in dictionary\n",
            $self->name,
        );
        $binding->is_func and die sprintf(
            "Cannot resolve var %s, is reserved as function name\n",
            $self->name,
        );
        $self->bind($binding);
        return;
    }
    sub _resolve_new {
        my($self, $dict) = @_;
        my $binding = $dict->introduce($self->name);
        $self->bind($binding);
        return $binding;
    }
};

package Axiom::Expr::Iter {
    our @ISA = qw{Axiom::Expr};
    my %combiner = (
        sum => 'pluslist',
        prod => 'mullist',
        integral => 'pluslist',
        inteval => 'pluslist',
    );
    sub is_iter { 1 }
    # All of these have arglist of the form (var, start, end, expr)
    sub has_newvar { 1 }
    sub intro_newvar { 0 }
    sub affect_newvar { 3 }
    sub given {
        my($self, $next) = @_;
        return () unless ($next // 0) == 3;
        my $args = $self->args;
        return +(
            Axiom::Expr->new({
                type => 'rge',
                args => [ $args->[0]->copy, $args->[1]->copy ],
            }),
            Axiom::Expr->new({
                type => 'rle',
                args => [ $args->[0]->copy, $args->[2]->copy ],
            }),
        );
    }

    # Provides the op used to split 'iter(var, start, end, expr)' into
    # 'iter(var, start, mid, expr) op type(var, mid, end, expr)'
    sub combiner {
        my($self) = @_;
        return $combiner{$self->type} // die sprintf(
            "Cannot return combiner of unknown iterator type '%s'",
            $self->type,
        );
    }
    sub range {
        my($self) = @_;
        my($from, $to) = @{ $self->args }[1, 2];
        my $diff = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $to->copy,
                $from->negate,
            ],
        })->clean;
        die sprintf(
            "Cannot expand non-constant range: %s .. %s is not constant\n",
            $from->rawexpr, $to->rawexpr,
        ) unless $diff->is_const;
        return [ map Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $from->copy,
                Axiom::Expr->new({
                    type => 'integer',
                    args => [ "$_" ],
                }),
            ],
        }), 0 .. $diff->args->[0] ];
    }
    sub value_at {
        my($self, $expr) = @_;
# FIXME: expr may have variables that need resolving/checking
        my($var, $targ) = @{ $self->args }[0, 3];
        return $targ->subst_var($var, $expr);
    }
    sub _resolve {
        my($self, $dict) = @_;
        my($var, $from, $to, $expr) = @{ $self->args };
        my $bind = $var->_resolve_new($dict);
        $_->_resolve($dict) for ($from, $to);
        my $local = $dict->local_name($var->name, $bind);
        $expr->_resolve($dict);
        return;
    }
    sub _dict_at {
        my($self, $dict, $loc) = @_;
        return $dict unless @$loc;
        my $this = shift(@$loc) - 1;
        my $result = $self->args->[$this]->_dict_at($dict, $loc);
        if ($this == 3) {
            my $var = $self->args->[0];
            $result->dict->{$var->name} = $var->binding;
        }
        return $result;
    }
};

package Axiom::Expr::Relation {
    our @ISA = qw{Axiom::Expr};
    my %inverse = (qw{
        req req rle rge rge rle rlt rgt rgt rlt
    });
    sub is_relation { 1 }
    sub inverse_type {
        my($self) = @_;
        return $inverse{$self->type} // die "Unknown type '@{[ $self->type ]}'";
    }
    sub _diff {
        my($self, $other, $map, $exact) = @_;
        my $diff = $self->SUPER::_diff($other, $map, $exact);
        if ($diff) {
            my $temp = Axiom::Expr->new({
                type => $self->inverse_type,
                args => [ reverse @{ $self->args } ],
            });
            return undef unless $temp->SUPER::_diff($other, $map, $exact);
        }
        return $diff;
    }
    # TRUE or FALSE if relation is constant, else undef
    sub check_const {
        my($self) = @_;
        my $args = $self->args;
        my $e = Axiom::Expr->new({
            type => 'pluslist',
            args => [ $args->[0]->copy, $args->[1]->negate ],
        })->clean;
        return undef unless $e->is_const;
        my $v = $e->rat;
        my $cb = {
            req => sub { $v == 0 ? 1 : 0 },
            rle => sub { $v <= 0 ? 1 : 0 },
            rlt => sub { $v < 0 ? 1 : 0 },
            rge => sub { $v >= 0 ? 1 : 0 },
            rgt => sub { $v > 0 ? 1 : 0 },
        }->{ $self->type } // die "Unknown type @{[ $self->type ]}";
        return $cb->();
    }
}

package Axiom::Expr::Quant {
    our @ISA = qw{Axiom::Expr};
    sub is_quant { 1 }
    sub has_newvar { 1 }
    sub intro_newvar { 0 }
    sub affect_newvar { 1 }
    sub _resolve {
        my($self, $dict) = @_;
        my($var, $expr) = @{ $self->args };
        my $bind = $var->_resolve_new($dict);
        my $local = $dict->local_name($var->name, $bind);
        $expr->_resolve($dict);
        return;
    }
    sub _dict_at {
        my($self, $dict, $loc) = @_;
        return $dict unless @$loc;
        my $this = shift(@$loc) - 1;
        my $result = $self->args->[$this]->_dict_at($dict, $loc);
        if ($this == 1) {
            my $var = $self->args->[0];
            $result->dict->{$var->name} = $var->binding;
        }
        return $result;
    }
};

sub _grammar {
    use Regexp::Grammars;
    state $grammar = qr{
        <grammar: Axiom::Expr>
        <debug: same>
        <objrule: Axiom::Expr=Statement>
            (?:
                <.ForallToken> <[args=Variable]> : <[args=Statement]>
                <type=(?{ 'forall' })>
            |
                <.ExistsToken> <[args=Variable]> : <[args=Statement]>
                <type=(?{ 'exists' })>
            |
                <[args=SStatement]>+ % <.AndSeparator>
                <type =(?{ 'andlist' })>
            |
                <[args=SStatement]>+ % <.OrSeparator>
                <type =(?{ 'orlist' })>
            |
                <[args=SStatement]> <.ImpliesToken> <[args=SStatement]>
                <type=(?{ 'implies' })>
            |
                <[args=SStatement]>
                <type=(?{ 'nothing' })>
            |
                <[args=Expr]> <.EqualsToken> <[args=Expr]>
                <type=(?{ 'req' })>
            |
                <[args=Expr]> <.LEToken> <[args=Expr]>
                <type=(?{ 'rle' })>
            |
                <[args=Expr]> <.LTToken> <[args=Expr]>
                <type=(?{ 'rlt' })>
            |
                <[args=Expr]> <.GEToken> <[args=Expr]>
                <type=(?{ 'rge' })>
            |
                <[args=Expr]> <.GTToken> <[args=Expr]>
                <type=(?{ 'rgt' })>
            |
                <[args=GivenStatement]>
                <type=(?{ 'nothing' })>
            )
        <objrule: Axiom::Expr=SStatement>
            (?:
                <.OpenParen> <[args=Statement]> <.CloseParen>
                <type=(?{ 'nothing' })>
                (?# if we go second-order, a variable can represent
                    a proposition - though in that case we should really
                    be attaching a domain. In any case, adding a raw
                    ... or args=Variable, type=nothing ...
                    here makes parsing way slower.
                )
            )
        <objrule: Axiom::Expr=Expr>
            <[args=PlusList]>
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=PlusList>
            <[args=SignedAtom]>+ % <.PlusSeparator> <!SignToken>
            <type=(?{ 'pluslist' })>
        <objrule: Axiom::Expr=SignedAtom>
            (?: <ws> <[Sign=SignToken]> )* <[args=MulList]>
            <type=(?{
                my $count = grep $_ = '-', @{ $MATCH{Sign} // [] };
                ($count % 2) ? 'negate' : 'nothing';
            })>
        <objrule: Axiom::Expr=MulList>
            (?: 1 (?= <.DivideToken> ) | <[args=Cuddled]> )
            (?:
                <.MultiplyToken>
                (?: 1 (?= <.DivideToken> ) | <[args=Cuddled]> )
            )* <!MultiplyToken>
            <args=(?{ [ map @{ $_->args }, @{ $MATCH{args} } ] })>
            (?: <.DivideToken> <[args=Recip]> )* <!DivideToken>
            <type=(?{ 'mullist' })>
        <objrule: Axiom::Expr=Cuddled>
            (?:
                <[args=PowExpr]>+ <[args=BarePowExpr]>?
            |
                <[args=BarePowExpr]>
            ) (?! \w )
            <type=(?{ 'cuddled' })>
        <objrule: Axiom::Expr=Recip>
            (?: <[args=PowExpr]> | <[args=BarePowExpr]> )
            (?! \w ) <!MultiplyToken>
            <type=(?{ 'recip' })>
        <objrule: Axiom::Expr=BarePowExpr>
            <[args=Factorial]> <.PowerToken> <[args=Factorial]> (?! \w )
            <type=(?{ 'pow' })>
        <objrule: Axiom::Expr=PowExpr>
            <[args=Factorial]> (?: <.PowerToken> <[args=BraceExpr]> )?
            <!PowerToken>
            <type=(?{ @{ $MATCH{args} } > 1 ? 'pow' : 'nothing' })>
        <objrule: Axiom::Expr=Factorial>
#FIXME
            <[args=Atom]> <[FactorialToken]>* <!FactorialToken>
            (?{
                my $count = @{ $MATCH{FactorialToken} // [] };
                if ($count) {
                    push @{ $MATCH{args} }, $count;
                    $MATCH{type} = 'factorial';
                } else {
                    $MATCH{type} = 'nothing';
                }
            })
        <objrule: Axiom::Expr=BraceExpr>
            <.OpenBrace> <[args=Expr]> <.CloseBrace>
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=Atom>
            (?:
                <[args=Integer]>
                | <[args=Function]>
                | <[args=Variable]>
                | <[args=Sum]>
                | <[args=Integral]>
                | <[args=Inteval]>
                | <[args=Min]>
                | <[args=Max]>
                | <[args=GivenExpr]>
                | <[args=ParenExpr]>
            )
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=ParenExpr>
            <.OpenParen> <[args=Expr]> <.CloseParen>
            <type=(?{ 'nothing' })>
        <objrule: Axiom::Expr=Function>
            <FuncName> \( <[args=ArgList]> \)
            (?{
                $MATCH{args} = [ $MATCH{FuncName},
                        map @{ $_->{args} }, @{ $MATCH{args} } ];
            })
            <type=(?{ 'function' })>
        <objrule: Axiom::Expr=Sum>
            <.SumToken> <[args=SumStart]> <[args=SumEnd]> <[args=BraceExpr]>
            (?{
                # split SumStart into variable and start value, extract SumEnd
                splice @{ $MATCH{args} }, 0, 1, @{ $MATCH{args}[0]{args} };
                $MATCH{args}[2] = $MATCH{args}[2]{args}[0];
            })
            <type=(?{ 'sum' })>
        <objrule: Axiom::Expr=Integral>
            <.IntegralToken> <[args=SumStart]> <[args=SumEnd]> <[args=BraceExpr]>
            (?{
                # split SumStart into variable and start value, extract SumEnd
                splice @{ $MATCH{args} }, 0, 1, @{ $MATCH{args}[0]{args} };
                $MATCH{args}[2] = $MATCH{args}[2]{args}[0];
            })
            <type=(?{ 'integral' })>
        <objrule: Axiom::Expr=Inteval>
            <.IntevalToken> <[args=SumStart]> <[args=SumEnd]> <[args=BraceExpr]>
            (?{
                # split SumStart into variable and start value, extract SumEnd
                splice @{ $MATCH{args} }, 0, 1, @{ $MATCH{args}[0]{args} };
                $MATCH{args}[2] = $MATCH{args}[2]{args}[0];
            })
            <type=(?{ 'inteval' })>
        <objrule: Axiom::Expr=Min>
            <.MinToken> \( <[args=ArgList]> \)
            (?{
                $MATCH{args} = [ map @{ $_->{args} }, @{ $MATCH{args} } ];
            })
            <type=(?{ 'min' })>
        <objrule: Axiom::Expr=Max>
            <.MaxToken> \( <[args=ArgList]> \)
            (?{
                $MATCH{args} = [ map @{ $_->{args} }, @{ $MATCH{args} } ];
            })
            <type=(?{ 'max' })>
        <objrule: Axiom::Expr=GivenStatement>
            <.GivenToken> _ \{ <[args=Statement]> \} \{ <[args=Statement]> \}
            <type=(?{ 'given' })>
        <objrule: Axiom::Expr=GivenExpr>
            <.GivenToken> _ \{ <[args=Statement]> \} <[args=BraceExpr]>
            <type=(?{ 'given' })>

        <rule: ArgList>
            <[args=Expr]>+ % <.CommaToken>
        <rule: SumStart>
            _ \{ <[args=AssignExpr]> \}
            (?{ $MATCH = { args => $MATCH{args}[0]{args} } })
        <rule: AssignExpr>
            <[args=Variable]> <.AssignToken> <[args=Expr]>
        <rule: SumEnd>
            <.PowerToken> (?:
                \{ <[args=Expr]> \}
                | <[args=Atom]>
            )
        <rule: RemapExpr>
            <[args=Variable]> <.BindToken> <[args=Expr]>
        <rule: FuncName>
            <[args=Name]> (??{
                my $name = $MATCH{args}[0];
                my $func = $Axiom::Expr::DICT->lookup($name->name);
                if ($func && $func->is_func) {
                    $name->bind($func);
                    $MATCH = $name;
                    $Axiom::Expr::SUCCEED;
                } else {
                    $Axiom::Expr::FAIL;
                }
            })
        <rule: Variable>
            <[args=Name]> (??{
                my $name = $MATCH{args}[0];
                my $var = $Axiom::Expr::DICT->lookup($name->name);
                if ($var && $var->is_func) {
                    $Axiom::Expr::FAIL;
                } else {
                    $MATCH = $name;
                    $Axiom::Expr::SUCCEED;
                }
            })

        <objtoken: Axiom::Expr=Name>
            <[args=(?: [a-zA-Z] (?: _ (?: \d \b ) )? )]>
            <type=(?{ 'name' })>
        <objtoken: Axiom::Expr=Integer>
            <[args=(?: \d+ (?! \d ) )]>
            <type=(?{ 'integer' })>

        <token: OpenParen> \(
        <token: CloseParen> \)
        <token: OpenBrace> \{
        <token: CloseBrace> \}
        <token: ImpliesToken> ->
        <token: EqualsToken> =
        <token: LEToken> \<=
        <token: LTToken> \< (?!=)
        <token: GEToken> \>=
        <token: GTToken> \> (?!=)
        <token: AndSeparator> \&
        <token: OrSeparator> \|
        <token: PlusSeparator> <PlusToken> | <?MinusToken>
        <token: SignToken> <Sign=PlusToken> | <Sign=MinusToken>
            (?{ $MATCH = $MATCH{Sign} })
        <token: PlusToken> \+
        <token: MinusToken> \- (?!>)
        # should this be \\sol ?
        <token: DivideToken> /
        # should this be \\middot ?
        <token: MultiplyToken> \.
        <token: PowerToken> \^
        <token: FactorialToken> !
        <token: CommaToken> ,
        <token: SumToken> \\sum
        <token: IntegralToken> \\int
        <token: IntevalToken> \\inteval
        <token: MinToken> \\min
        <token: MaxToken> \\max
        <token: GivenToken> \\given
        <token: ForallToken> \\A | \\forall
        <token: ExistsToken> \\E | \\exists
        (?# used only in derivations )
        <token: WithToken> \*with
        <token: ValueToken> \*value
        (?# Assign and Equals are ambiguous, I think that is ok )
        <token: AssignToken> =
        <token: BindToken> :=
        <token: ws> \s*+
    }x;
    return;
}
BEGIN { _grammar() }

sub _parsere {
    my($debug) = @_;

    use Regexp::Grammars;
    return $debug
        ? (state $dsre = qr{
            <extends: Axiom::Expr>
            <debug: match>
            ^ <Statement> \z
        }x)
        : (state $sre = qr{
            <extends: Axiom::Expr>
            ^ <Statement> \z
        }x);
}

package Axiom::Expr::LocalDict {
    sub new {
        my($class, $dict) = @_;
        my $old = $Axiom::Expr::DICT;
        my $restore = sub { $Axiom::Expr::DICT = $old };
        my $self = bless \$restore, $class;
        $Axiom::Expr::DICT = $dict;
        return $self;
    }
    DESTROY {
        my($self) = @_;
        $$self->();
    }
};

1;
