package Axiom::Derive;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;
use Scalar::Util qw{ weaken };
use List::Util qw{ first };

sub new {
    my($class, $context, $source) = @_;
    my $self = bless {
        context => $context,
        source => $source,
        dict => $context->dict->copy,
        rules => [],
        working => $context->last_expr,
        working_name => [],
        scope => 0,
    };
    weaken $self->{context};
    return $self;
}

sub is_derived { 1 }

sub context { shift->{context} }
sub source { shift->{source} }
sub rules { shift->{rules} }
sub expr { shift->{expr} }
sub dict { shift->{dict} }
sub rawexpr { shift->{rawexpr} }
sub working {
    my($self, $new) = @_;
    $self->{working} = $new if @_ > 1;
    return $self->{working};
}
sub working_name { shift->{working_name} }
sub lookup {
    my($self, $name) = @_;
    return $self->dict->lookup($name);
}
sub introduce {
    my($self, $name) = @_;
    return $self->dict->introduce($name);
}
sub str {
    my($self) = @_;
    return sprintf '%s: %s', join('; ', @{ $self->rules }), $self->rawexpr;
}
sub line {
    my($self, $index) = @_;
    return $index eq ''
        ? $self->working
        : $self->context->expr($index);
}
sub scope {
    my($self, $new) = @_;
    $self->{scope} = $new if @_ > 1;
    return $self->{scope};
}

sub derive {
    my($class, $line, $context, $debug) = @_;
    my $self = $class->new($context, $line);
    my @rules;
    my $rre = rulere($debug);

    my $local = Axiom::Expr->local_dict($self->dict);
    while ($line =~ s{$rre}{}) {
        my($rule, $value) = %{ $/{rule} };
        push @rules, [ $rule, $value->{args} ];
    }
    $line =~ s/^\s+//;

    my $expr = Axiom::Expr->parse($self->dict, $line, $debug) or return;
    $self->{rawexpr} = $line;
    $self->{expr} = $expr;
    $self->validate(\@rules) or return;
    return $self;
}

# FIXME: these new vars are temporary, somehow we need to make them valid
# while they're needed for comparison, then discard them.
sub new_local {
    my($self, $name) = @_;
    my $subdict = $self->dict->subsidiary;
    my $binding = $subdict->insert_local($name);
    my $new = Axiom::Expr->new({
        type => 'name',
        args => [ $binding->name ],
    });
    $new->bind($binding);
    return $new;
}

sub _rulere {
    use Regexp::Grammars;
    return state $gdre = qr{
        <grammar: Axiom::Derive>
        <extends: Axiom::Expr>
        <nocontext:>
        <debug: same>

        <rule: rule> (?:
            <axiom>
            | <theorem>
            | <identity>
            | <condstart>
            | <condend>
            | <induction>
            | <equate>
            | <distrib>
            | <unarydistrib>
            | <add>
            | <multiply>
            | <factor>
            | <iterexpand>
            | <iterextend>
            | <itervar>
            | <recurse>
        )
        <rule: axiom> axiom (?:
            <[args=rulename]>
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        |
            <args=(?{ [] })>
        )
        <rule: theorem> theorem (?: <[args=rulename]> | <args=(?{ [] })> )
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        <rule: identity> identity \( <[args=varlist]> , <[args=Expr]> \)
            (?{ $MATCH{args}[0] = $MATCH{args}[0]{args} })
        <rule: condstart> condstart \( <[args=varlist]> \)
            (?{ $MATCH{args}[0] = $MATCH{args}[0]{args} })
        <rule: condend> condend \( <[args=varmap]> \)
        <rule: induction> induction \( <[args=Variable]> , <[args=Expr]> \)
        <rule: equate>
            equate \( <[args=optline]> <[args=location]> ,
                    <[args=line]> (?: , <[args=varmap]> )? \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 2) })
        <rule: distrib>
            distrib \(
                <[args=optline]> <[args=location]> , <[args=arg]> , <[args=arg]>
            \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: unarydistrib>
            unarydistrib \( <[args=optline]> <[args=location]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: add>
            add \( <[args=optline]> <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        <rule: multiply>
            multiply \( <[args=optline]> <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        <rule: factor>
            factor \( <[args=optline]> <[args=location]> , <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: iterexpand>
            iterexpand \( <[args=optline]> <[args=location]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: iterextend>
            iterextend \( <[args=optline]> <[args=location]> , <[args=arg]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: itervar>
            # FIXME: we actually need to parse the RemapExpr in the context
            # of the variable mappings that exist at the line and location
            # being specified by the first two arguments - it should be
            # possible to rewrite \sum_i=...{sum_j=...} to set j := i - j.
            itervar \(
                <[args=optline]> <[args=location]> , <[args=RemapExpr]>
            \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 2) })
            (?{ splice @{ $MATCH{args} }, 2, 1, @{ $MATCH{args}[2] } })
        <rule: recurse>
            recurse \( <[args=optline]> <[args=pair]> , <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0 .. 1) })
            (?{ splice @{ $MATCH{args} }, 1, 1, @{ $MATCH{args}[1] } })

        <rule: varmap> (?: \{ (?: <[args=pair]>* % , )? \} )
        <rule: pair> <[args=Variable]> := <[args=Expr]>
        <rule: varlist> \{ <[args=Variable]>* % , <.ws>? \}

        <token: optline>
            <args=line> : <args=(?{ $MATCH{args}{args} })>
            | <args=(?{ '' })>
        <token: line>
            <args=(?: \d+ (?: \. \d+ )* )>
            | <args=rulename> <args=(?{ $MATCH{args}{args} })>
        <token: rulename> <args=(?:[A-Z]\w*(?!\w))>
        <token: location> <[args=arg]>+ % \.
        <token: arg> \d+
    }x;
}
BEGIN { _rulere() }

sub rulere {
    use Regexp::Grammars;
    my($debug) = @_;
    return $debug
        ? (state $drre = qr{
            <extends: Axiom::Derive>
            <nocontext:>
            <debug: match>
            ^ <rule> [:;]
        }x)
        : (state $rre = qr{
            <extends: Axiom::Derive>
            <nocontext:>
            ^ <rule> [:;]
        }x);
}

sub _zero {
    return Axiom::Expr->new({
        type => 'integer',
        args => [ '0' ],
    });
}

sub _one {
    return Axiom::Expr->new({
        type => 'integer',
        args => [ '1' ],
    });
}

sub _div {
    my($e1, $e2) = @_;
    my($t1, $t2) = map $_->type, ($e1, $e2);
    return _one() if !$e1->diff($e2);
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

sub _linename {
    my($line) = @_;
    return '' unless defined $line && length $line;
    return "$line:";
}

sub _map {
    my($map) = @_;
    return '' unless defined $map && keys %$map;
    return sprintf ', { %s }', join ', ', map {
        my($var, $expr) = @{ $_->{args} };
        sprintf '%s := %s', $var->name, $expr->rawexpr;
    } @{ $map->{args} };
}

# Given (x, f(x), n) return f^x(n) if we know how to construct it, else undef.
sub _f_pow {
    my($var, $iter, $count) = @_;
    my $try = Axiom::Expr->new({
        type => 'pluslist',
        args => [ $iter->copy, $var->negate ],
    })->clean;
    if ($try->is_independent($var)) {
        # (x := x + a) -> (x + an)
        return Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $var->copy,
                Axiom::Expr->new({
                    type => 'mullist',
                    args => [ $try, $count ],
                }),
            ],
        })->clean;
    }
    $try = Axiom::Expr->new({
        type => 'mullist',
        args => [ $iter, Axiom::Expr->new({
            type => 'recip',
            args => [ $var ],
        }) ],
    })->clean;
    if ($try->is_independent($var)) {
        # (x := ax) -> (a^n . x)
        return Axiom::Expr->new({
            type => 'mullist',
            args => [
                Axiom::Expr->new({
                    type => 'pow',
                    args => [ $try, $count ],
                }),
                $var,
            ],
        })->clean;
    }
    # Could handle ax + b (if we can discern it), not sure what else.
    return undef;
}

{
    my $OK = 0;
    my $NOK = 1;
    my $VALID = 2;
    my %validation = (
        axiom => sub {
            my($self, $args) = @_;
            $self->working($self->expr);
            if (@$args) {
                push @{ $self->working_name }, $args->[0];
                push @{ $self->rules }, "axiom $args->[0]";
            } else {
                push @{ $self->rules }, 'axiom';
            }
            return 1;
        },
        theorem => sub {
            my($self, $args) = @_;
            if (@$args) {
                push @{ $self->working_name }, $args->[0];
                push @{ $self->rules }, "theorem $args->[0]";
            } else {
                push @{ $self->rules }, 'theorem';
            }
            return 1;
        },
        identity => sub {
            my($self, $args) = @_;
            my($varlist, $expr) = @$args;
            my $result = Axiom::Expr->new({
                type => 'equals',
                args => [ $expr->copy, $expr->copy ],
            });
            for my $var (reverse @$varlist) {
                $result = Axiom::Expr->new({
                    type => 'forall',
                    args => [ $var, $result ],
                });
            }
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'identity(%s)', $expr->rawexpr;
            return 1;
        },
        condstart => sub {
            my($self, $args) = @_;
            my($varlist) = @$args;
            my $dict = $self->dict->clone;
            $dict->insert($_->name, 'var') for @$varlist;
            my $result = $self->expr;
            $result->resolve($dict);
            $self->working($self->expr);
            $self->{dict} = $dict;
            $self->scope(1);
            push @{ $self->rules }, 'condstart';
            return 1;
        },
        condend => sub {
            my($self, $args) = @_;
            my($map) = @$args;
            my $where = $self->context->curline;
            my $cond = $self->context->expr("$where.0");
            my %vmap = map {
                my($var, $expr) = @{ $_->{args} };
                $var->resolve($self->dict);
                +($var->binding->id => $expr)
            } @{ $map->{args} // [] };

            my $result = Axiom::Expr->new({
                type => 'implies',
                args => [
                    $cond->copy,
                    $self->working->copy,
                ],
            })->subst_vars(\%vmap);
            for my $var (reverse sort values %vmap) {
                $result = Axiom::Expr->new({
                    type => 'forall',
                    args => [ $var, $result ],
                });
            }

            my $dict = $self->context->scope_dict;
            $result->resolve($dict);
            $self->working($result);
            $self->scope(-1);
            push @{ $self->rules }, 'condend';
            return 1;
        },
        induction => sub {
            my($self, $args) = @_;
            my($var, $base_expr) = @$args;
            my $starting = $self->working;
            # FIXME: source of base line should be explicit
            my $base = $self->context->lines->{$self->context->curline}[-2]->expr;
            $starting->type eq 'forall' or die sprintf
                    "Induction requires 'forall', not %s\n", $starting->type;
            my($ivar, $iexpr) = @{ $starting->args };
            $ivar->name eq $var->name or die sprintf(
                "Induction variable '%s' does not match '%s' found\n",
                $var->name, $ivar->name,
            );
            $iexpr->type eq 'implies' or die sprintf(
                "Induction requires 'implies', not '%s' in forall\n",
                $iexpr->type,
            );
            my($result, $next) = @{ $iexpr->args };

            # Allow the base_expr to reference any names resolvable at
            # the deepest common subexpr that covers all references
            # to be substituted.
            my $common = $result->common_loc($ivar->binding->id);
            # $result is at [ 2, 1 ] in the primary expr
            my $subdict = $starting->dict_at([ 2, 1, @$common ]);
            $base_expr->resolve($subdict);
            my $expect_base = $result->subst_var($ivar, $base_expr);
            my $diff = $expect_base->diff($base);
            if ($diff) {
                die sprintf "base expressions differ at\n  %s\n  %s\n",
                        map $_->locate($diff)->str, $expect_base, $base;
            }

            # The next_expr may resolve the same set of names as above,
            # but may also reference the variable we're substituting.
            $subdict->dict->{$ivar->name} = $ivar->binding;
            my $next_expr = Axiom::Expr->new({
                type => 'pluslist',
                args => [ $var->copy, _one() ],
            });
            $next_expr->resolve($subdict);
            my $expect_next = $result->subst_var($ivar, $next_expr);
            $diff = $expect_next->diff($next);
            if ($diff) {
                die sprintf "next expressions differ at\n  %s\n  %s\n",
                        map $_->locate($diff)->str, $expect_next, $next;
            }

            # FIXME: attach 'var >= base_expr -> ...' unless that covers
            # the whole domain of the var.
            $result = Axiom::Expr->new({
                type => 'forall',
                args => [ $ivar->copy, $result ],
            });
            $self->working($result->copy);
            push @{ $self->rules }, sprintf 'induction(%s, %s)',
                    $var->name, $base_expr->rawexpr;
            return 1;
        },
        equate => sub {
            my($self, $args) = @_;
            my($line, $loc, $eqline, $map) = @$args;
            my $starting = $self->line($line);
            my $expr = $starting->locate($loc);

            my $from = $self->line($eqline);
            my $from_expr = $from;
            my $from_loc = [];
            while ($from_expr->type eq 'forall') {
                push @$from_loc, 2;
                $from_expr = $from_expr->args->[1];
            }
            $from_expr->type eq 'equals' or die sprintf(
                "Can't equate() with a %s\n", $from_expr->type,
            );
            my $from_dict = $from->dict_at($from_loc);
            my $to_dict = $starting->dict_at($loc);

            my %vmap = map {
                my($var, $expr) = @{ $_->{args} };
                $var->resolve($from_dict);
                $expr->resolve($to_dict);
                +($var->binding->id => $expr)
            } @{ $map->{args} // [] };
            my $equate = $from_expr->subst_vars(\%vmap);

            my $repl;
            my($left, $right) = @{ $equate->args };
            if (! $expr->diff($left)) {
                $repl = $right;
            } elsif (! $expr->diff($right)) {
                $repl = $left;
            } else {
                die sprintf(
                    "Neither side of equate %s matches target %s\n",
                    $equate->str, $expr->str,
                );
            }

            my $result = $starting->substitute($loc, $repl);
            $self->working($result);
            push @{ $self->rules }, sprintf 'equate(%s%s, %s%s)',
                    _linename($line), join('.', @$loc), $eqline, _map($map);
            return 1;
        },
        distrib => sub {
            my($self, $args) = @_;
            my($line, $loc, $from, $over) = @$args;
            my $starting = $self->line($line);
            my $expr = $starting->locate($loc);
            my $efrom = $expr->args->[$from - 1]
                    // die sprintf "arg %s missing in %s\n", $from, $expr->str;
            my $eover = $expr->args->[$over - 1]
                    // die sprintf "arg %s missing in %s\n", $over, $expr->str;
            my $repl;
            if ($expr->type eq 'mullist'
                && ($eover->type eq 'pluslist' || $eover->type eq 'sum')
            ) {
                my $eargs = $eover->args;
                my $combined = ($eover->type eq 'pluslist')
                    ? Axiom::Expr->new({
                        type => 'pluslist',
                        args => [
                            map Axiom::Expr->new({
                                type => 'mullist',
                                args => [ $_, $efrom ],
                            }), map $_->copy, @$eargs
                        ],
                    })
                    : Axiom::Expr->new({
                        type => 'sum',
                        args => [
                            $eargs->[0]->copy,
                            $eargs->[1]->copy,
                            $eargs->[2]->copy,
                            Axiom::Expr->new({
                                type => 'mullist',
                                args => [ $eargs->[3]->copy, $efrom ],
                            }),
                        ],
                    });

                $repl = Axiom::Expr->new({
                    type => 'mullist',
                    args => [ map {
                        $_ == $from - 1
                            ? ()
                        : $_ == $over - 1
                            ? $combined
                            : $expr->args->[$_]->copy
                    } 0 .. $#{ $expr->args } ],
                });
            } else {
                die sprintf "don't know how to distribute a %s over a %s\n",
                        $efrom->type, $eover->type;
            }
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'distrib(%s%s, %s, %s)',
                    _linename($line), join('.', @$loc), $from, $over;
            return 1;
        },
        unarydistrib => sub {
            my($self, $args) = @_;
            my($line, $loc) = @$args;
            my $starting = $self->line($line);
            my $expr = $starting->locate($loc);
            my($arg, $repl);
            if ($expr->type eq 'negate') {
                $arg = $expr->args->[0];
                if ($arg->type eq 'pluslist') {
                    $repl = Axiom::Expr->new({
                        type => 'pluslist',
                        args => [ map Axiom::Expr->new({
                            type => 'negate',
                            args => [ $_->copy ],
                        }), @{ $arg->args } ],
                    });
                } elsif ($arg->type eq 'mullist') {
                    my $margs = $arg->args;
                    my $target = first(
                        sub { $_->is_neg }, @$margs
                    ) // $margs->[0];
                    $repl = Axiom::Expr->new({
                        type => 'mullist',
                        args => [ map {
                            $_ == $target ? $_->negate : $_->copy
                        } @$margs ],
                    });
                }
            } elsif ($expr->type eq 'sum') {
                (my($var, $from, $to), $arg) = @{ $expr->args };
                if ($arg->type eq 'pluslist') {
                    my $name = $var->name;
                    my @var = map $self->new_local($name),
                            0 .. $#{ $arg->args };
                    $repl = Axiom::Expr->new({
                        type => 'pluslist',
                        args => [ map Axiom::Expr->new({
                            type => 'sum',
                            args => [
                                $var[$_],
                                $from->copy,
                                $to->copy,
                                $arg->args->[$_]->subst_var($var, $var[$_]),
                            ],
                        }), 0 .. $#{ $arg->args } ],
                    });
                }
            }
            unless ($repl) {
                die sprintf "don't know how to distribute a %s%s\n",
                    $expr->type, $arg ? ' over a ' . $arg->type : '';
            }
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'unarydistrib(%s%s)',
                    _linename($line), join('.', @$loc);
            return 1;
        },
        add => sub {
            my($self, $args) = @_;
            my($line, $expr) = @$args;
            my $starting = $self->line($line);
            my $loc = [];
            my $eq = $starting;
            while ($eq->is_quant) {
                push @$loc, 2;
                $eq = $eq->args->[1];
            }
            $eq->type eq 'equals' or die sprintf(
                "don't know how to add to a %s\n", $eq->type
            );
            my $repl = Axiom::Expr->new({
                type => $eq->type,
                args => [ map Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ $_->copy, $expr->copy ],
                }), @{ $eq->args } ],
            });
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'add(%s%s)',
                    _linename($line), $expr->rawexpr;
            return 1;
        },
        multiply => sub {
            my($self, $args) = @_;
            my($line, $expr) = @$args;
            my $starting = $self->line($line);
            my $loc = [];
            my $eq = $starting;
            while ($eq->is_quant) {
                push @$loc, 2;
                $eq = $eq->args->[1];
            }
            $eq->type eq 'equals' or die sprintf(
                "don't know how to multiply a %s\n", $starting->type,
            );
            my $repl = Axiom::Expr->new({
                type => $eq->type,
                args => [ map Axiom::Expr->new({
                    type => 'mullist',
                    args => [ $_->copy, $expr->copy ],
                }), @{ $eq->args } ],
            });
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'multiply(%s%s)',
                    _linename($line), $expr->rawexpr;
            return 1;
        },
        factor => sub {
            my($self, $args) = @_;
            my($line, $loc, $expr) = @$args;
            my $starting = $self->line($line);
            my $targ = $starting->locate($loc);
            my $subdict = $starting->dict_at($loc);
            $expr->resolve($subdict);
            my $repl;
            if ($targ->type eq 'pluslist') {
                $repl = Axiom::Expr->new({
                    type => 'mullist',
                    args => [ $expr, Axiom::Expr->new({
                        type => 'pluslist',
                        args => [ map _div($_, $expr), @{ $targ->args } ],
                    }) ],
                });
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
                die sprintf "don't know how to factor a %s\n", $targ->type;
            }
            my $result = $starting->substitute($loc, $repl);
            $self->working($result);
            push @{ $self->rules }, sprintf 'factor(%s%s, %s)',
                    _linename($line), join('.', @$loc), $expr->rawexpr;
            return 1;
        },
        iterexpand => sub {
            my($self, $args) = @_;
            my($line, $loc) = @$args;
            my $starting = $self->line($line);
            my $iter = $starting->locate($loc);
            my $repl;
            die sprintf "Cannot iterate over a %s\n", $iter->type
                    unless $iter->is_iter;
            if ($iter->type eq 'sum') {
                $repl = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ map $iter->value_at($_), @{ $iter->range } ],
                });
            } else {
                die sprintf "don't know how to expand a %s\n", $iter->type;
            }
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'iterexpand(%s%s)',
                    _linename($line), join('.', @$loc);
            return 1;
        },
        iterextend => sub {
            my($self, $args) = @_;
            my($line, $loc, $dir) = @$args;
            my $starting = $self->line($line);
            my $iter = $starting->locate($loc);
            my $repl;
            if ($iter->type eq 'sum') {
                my($var, $from, $to, $expr) = @{ $iter->args };
                my($base, $add);
                if ($dir == 0) {
                    $base = $from;
                    $add = '-1';
                } else {
                    $base = $to;
                    $add = '1';
                }
                my $var_at = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [
                        $base->copy,
                        Axiom::Expr->new({
                            type => 'integer',
                            args => [ $add ],
                        }),
                    ],
                });
                $repl = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [
                        Axiom::Expr->new({
                            type => 'sum',
                            args => [
                                $var->copy,
                                ($base == $from) ? $var_at : $from->copy,
                                ($base == $to) ? $var_at : $to->copy,
                                $expr->copy,
                            ],
                        }),
                        Axiom::Expr->new({
                            type => 'negate',
                            args => [ $iter->value_at($var_at) ],
                        }),
                    ],
                });
            } else {
                die sprintf "Don't know how to extend a %s\n", $iter->type;
            }
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf 'iterextend(%s%s, %s)',
                    _linename($line), join('.', @$loc), $dir;
            return 1;
        },
        itervar => sub {
            my($self, $args) = @_;
            my($line, $loc, $cvar, $cexpr) = @$args;
            my $starting = $self->line($line);
            my $iter = $starting->locate($loc);
            $iter->is_iter or die sprintf(
                "Don't know how to change iter var on a non-iterator %s\n",
                $iter->type,
            );
            my($var, $from, $to, $expr) = @{ $iter->args };

            my $cdict = $starting->dict_at($loc);
            my $cbind = $cvar->_resolve_new($cdict);
            {
                my $local = $cdict->local_name($cvar->name, $cbind);
                $cexpr->_resolve($cdict);
            }

            my $repl;
            # This gets tricky: if E is an expression independent of
            # the iter variable i, we can change variable to E+i
            # or to E-i (with a reverse of from/to), but not anything
            # else.
            if (Axiom::Expr->new({
                type => 'pluslist',
                args => [ $cexpr->copy, $cvar->copy ],
            })->is_independent($var)) {
                # i := E - i
                $repl = Axiom::Expr->new({
                    type => $iter->type,
                    args => [
                        $var->copy,
                        $cexpr->subst_var($cvar, $to),
                        $cexpr->subst_var($cvar, $from),
                        $expr->subst_var($var, $cexpr->subst_var($cvar, $var)),
                    ],
                });
            } elsif (Axiom::Expr->new({
                type => 'pluslist',
                args => [ $cexpr->copy, $cvar->negate ],
            })->is_independent($var)) {
                # i := E + i
                $repl = Axiom::Expr->new({
                    type => $iter->type,
                    args => [
                        $var->copy,
                        $cexpr->subst_var($cvar, $from),
                        $cexpr->subst_var($cvar, $to),
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
                _linename($line), join('.', @$loc),
                $cvar->name, $cexpr->rawexpr,
            );
            return 1;
        },
        recurse => sub {
            my($self, $args) = @_;
            my($line, $var, $iter, $count) = @$args;
            my $starting = $self->line($line);
            my $loc = [];
            my $eq = $starting;
            while ($eq->is_quant) {
                push @$loc, 2;
                $eq = $eq->args->[1];
            }

            my $subdict = $starting->dict_at($loc);
            $_->resolve($subdict) for ($var, $iter, $count);

            # Given f(x) = af(g(x)) + bh(x) + c, we iteratively replace
            # af(g(x)) with the equivalent evaluation of the whole RHS
            # n times to give
            #  f(x) = a^n f(g^n(x)) + sum_0^{n-1}{ a^i (bh(g^i(x)) + c) }

            $eq->type eq 'equals' or die sprintf(
                "Don't know how to apply recurse over a %s\n", $eq->type,
            );
            my($lhs, $rhs) = @{ $eq->args };
            my $base_pow = _f_pow($var, $iter, $count) or die sprintf(
                "Don't know how to recurse iteration %s := %s\n",
                $var->name, $iter->rawexpr,
            );

            $lhs->is_independent($var) and die sprintf(
                "LHS of recurse expression is independent of %s\n", $var->name,
            );
            my $expect = $lhs->subst_var($var, $iter);
            my $rloc = $rhs->find_expr($expect) or die sprintf(
                "Unable to find %s in %s\n",
                $expect->str, $rhs->str,
            );
            my $prod = _one();
            my $cur;
            for (0 .. $#$rloc) {
                $cur = $_ ? $cur->args->[ $rloc->[$_ - 1] ] : $rhs;
                my $type = $cur->type;
                if ($type eq 'pluslist') {
                    next;
                } elsif ($type eq 'negate') {
                    $prod = $prod->negate;
                    next;
                } elsif ($type eq 'mullist') {
                    my $next_rloc = $rloc->[$_];
                    my $args = $cur->args;
                    $prod = Axiom::Expr->new({
                        type => 'mullist',
                        args => [ $prod, @$args[ grep $_ != $next_rloc, 0 .. $#$args ] ],
                    });
                    next;
                } elsif ($type eq 'recip') {
                    $prod = Axiom::Expr->new({
                        type => 'recip',
                        args => [ $prod ],
                    });
                    next;
                } else {
                    die sprintf(
                        "Don't know how to recurse %s with RHS structure %s\n",
                        $expect->str, $cur->str,
                    );
                }
            }
            $prod = $prod->clean;
            my $rest = Axiom::Expr->new({
                type => 'pluslist',
                args => [
                    $rhs,
                    Axiom::Expr->new({
                        type => 'mullist',
                        args => [ $prod->copy, $expect->copy ],
                    })->negate,
                ],
            })->clean;
            my $itervar = $self->new_local('i');
            my $rest_iter = Axiom::Expr->new({
                type => 'sum',
                args => [
                    $itervar,
                    _zero(),
                    Axiom::Expr->new({
                        type => 'pluslist',
                        args => [
                            $count->copy,
                            _one()->negate,
                        ],
                    }),
                    Axiom::Expr->new({
                        type => 'mullist',
                        args => [
                            Axiom::Expr->new({
                                type => 'pow',
                                args => [
                                    $prod->copy,
                                    $itervar,
                                ],
                            }),
                            $rest->subst_var($var, _f_pow($var, $iter, $itervar)),
                        ],
                    }),
                ],
            });
            # (f(x) = af(g(x)) + bh(x) + c)
            # -> f(x) = a^n . f(g^n(x)) + \sum_{i=0}^{n-1}{a^i(bh(g^i(x)) + c)}
            my $repl = Axiom::Expr->new({
                type => 'equals',
                args => [
                    $lhs->copy,
                    Axiom::Expr->new({
                        type => 'pluslist',
                        args => [
                            Axiom::Expr->new({
                                type => 'mullist',
                                args => [
                                    Axiom::Expr->new({
                                        type => 'pow',
                                        args => [
                                            $prod->copy,
                                            $count->copy,
                                        ],
                                    }),
                                    $lhs->subst_var($var, $base_pow),
                                ],
                            }),
                            $rest_iter,
                        ],
                    }),
                ],
            });
            my $result = $starting->substitute($loc, $repl);
            $result->resolve($self->dict);
            $self->working($result);
            push @{ $self->rules }, sprintf(
                'recurse(%s%s := %s, %s)',
                _linename($line), $var->name, $iter->rawexpr, $count->rawexpr,
            );
            return 1;
        },
    );
    sub validate {
        my($self, $rules) = @_;
        for my $rule (@$rules) {
            my($type, $args) = @$rule;
            return unless $validation{$type}->($self, $args);
        }
        my $expr = $self->expr;
        $expr->resolve($self->dict);
        my $diff = $expr->diff($self->working);
        return $self unless $diff;
        die sprintf "Expressions differ at\n  %s\n  %s\nclean:\n  %s\n  %s\n",
                map($_->locate($diff)->str, $expr, $self->working),
                map $_->str, $expr->clean, $self->working->clean;
    }
}

1;
