package Axiom::Derive;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;
use Scalar::Util qw{ weaken };

sub new {
    my($class, $context) = @_;
    my $self = bless {
        context => $context,
        dict => $context->dict->copy,
        rules => [],
        working => $context->last_expr,
        working_name => [],
        scope => 0,
    };
    weaken $self->{context};
    return $self;
}

sub context { shift->{context} }
sub source { shift->{source} }
sub rules { shift->{rules} }
sub expr { shift->{expr} }
sub dict { shift->{dict} }
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
    return sprintf '%s: %s', join('; ', @{ $self->rules }), $self->source;
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
    my $self = $class->new($context);
    my @rules;
    my $rre = rulere($debug);

    local $Axiom::Expr::DICT = $self->dict;
    while ($line =~ s{$rre}{}) {
        my($rule, $value) = %{ $/{rule} };
        push @rules, [ $rule, $value->{args} ];
    }

    my $expr = Axiom::Expr->parse($self->dict, $line, $debug) or return;
    $self->{expr} = $expr;
    $self->{source} = $line;
    $self->validate(\@rules) or return;
    return $self;
}
    
sub _rulere {
    use Regexp::Grammars;
    return state $gdre = qr{
        <grammar: Axiom::Derive>
        <extends: Axiom::Expr>
        <nocontext:>

        <rule: rule> (?:
            <axiom>
            | <theorem>
            | <identity>
            | <condstart>
            | <condend>
            | <distrib>
            | <unarydistrib>
            | <add>
            | <multiply>
            | <factor>
            | <iterexpand>
            | <iterextend>
        )
        <rule: axiom> axiom (?:
            <[args=rulename]>
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        |
            <args=(?{ [] })>
        )
        <rule: theorem> theorem (?: <[args=rulename]> | <args=(?{ [] })> )
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        <rule: condstart> condstart <args=(?{ [] })>
        <rule: condend> condend <args=(?{ [] })>
        <rule: identity> identity \( <[args=Expr]> \)
        <rule: distrib>
            distrib \(
                <[args=lineref]> <[args=location]> , <[args=arg]> , <[args=arg]>
            \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: unarydistrib>
            unarydistrib \(
                <[args=lineref]> <[args=location]>
            \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: add>
            add \( <[args=lineref]> <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        <rule: multiply>
            multiply \( <[args=lineref]> <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0) })
        <rule: factor>
            factor \( <[args=lineref]> <[args=location]> , <[args=Expr]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: iterexpand>
            iterexpand \( <[args=lineref]> <[args=location]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
        <rule: iterextend>
            iterextend \( <[args=lineref]> <[args=location]> , <[args=arg]> \)
            (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })

        <token: lineref>
            <args=(?: \d+ (?: \. \d+ )* )> :
            | <args=rulename> :
                (?{ $MATCH{args} = $MATCH{args}{args} })
            | <args=(?{ '' })>
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
    return Axiom::Expr::Const->new({
        type => 'integer',
        args => [ '0' ],
    });
}

sub _one {
    return Axiom::Expr::Const->new({
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
        condstart => sub {
            my($self, $args) = @_;
            $self->working($self->expr);
            $self->scope(1);
            push @{ $self->rules }, 'condstart';
            return 1;
        },
        condend => sub {
            my($self, $args) = @_;
            my $where = $self->context->curline;
            my $cond = $self->context->expr("$where.0");
            my $result = Axiom::Expr->new({
                type => 'implies',
                args => [
                    $cond->copy,
                    $self->working->copy,
                ],
            });
            $self->working($result);
            $self->scope(-1);
            push @{ $self->rules }, 'condend';
            return 1;
        },
        identity => sub {
            my($self, $args) = @_;
            my $expr = $args->[0];
            $self->working(Axiom::Expr->new({
                type => 'equals',
                args => [ $expr->copy, $expr->copy ],
            }));
            push @{ $self->rules }, sprintf 'identity(%s)', $expr->{''};
            return 1;
        },
        distrib => sub {
            my($self, $args) = @_;
            my($line, $loc, $from, $over) = @$args;
            my $starting = $self->line($line);
            my $expr = $starting->locate($loc);
            my $efrom = $expr->args->[$from - 1];
            my $eover = $expr->args->[$over - 1];
            my $repl;
            if ($expr->type eq 'mullist' && $eover->type eq 'pluslist') {
                $repl = Axiom::Expr->new({
                    type => 'mullist',
                    args => [ map {
                        $_ == $from - 1
                            ? ()
                        : $_ == $over - 1
                            ? $repl = Axiom::Expr->new({
                                type => 'pluslist',
                                args => [
                                    map Axiom::Expr->new({
                                        type => 'mullist',
                                        args => [ $_, $efrom ],
                                    }), map $_->copy, @{ $eover->args }
                                ],
                            })
                            : $expr->args->[$_]->copy
                    } 0 .. $#{ $expr->args } ],
                });
            } else {
                die sprintf "don't know how to distribute a %s over a %s\n",
                        $efrom->type, $eover->type;
            }
            $self->working($starting->substitute($loc, $repl));
            push @{ $self->rules }, sprintf 'distrib(%s%s, %s, %s)',
                    _linename($line), join('.', @$loc), $from, $over;
            return 1;
        },
        unarydistrib => sub {
            my($self, $args) = @_;
            my($line, $loc) = @$args;
            my $starting = $self->line($line);
            my $expr = $starting->locate($loc);
            my $arg = $expr->args->[0];
            my $repl;
            if ($expr->type eq 'negate' && $arg->type eq 'pluslist') {
                $repl = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ map Axiom::Expr->new({
                        type => 'negate',
                        args => [ $_->copy ],
                    }), @{ $arg->args } ],
                });
            } else {
                die sprintf "don't know how to distribute a %s over a %s\n",
                        $expr->type, $arg->type;
            }
            $self->working($starting->substitute($loc, $repl));
            push @{ $self->rules }, sprintf 'unarydistrib(%s%s)',
                    _linename($line), join('.', @$loc);
            return 1;
        },
        add => sub {
            my($self, $args) = @_;
            my($line, $expr) = @$args;
            my $starting = $self->line($line);
            $starting->type eq 'equals'
                    or die "don't know how to add to a %s\n", $starting->type;
            my $result = Axiom::Expr->new({
                type => $starting->type,
                args => [ map Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ $_->copy, $expr->copy ],
                }), @{ $starting->args } ],
            });
            $self->working($result);
            push @{ $self->rules }, sprintf 'add(%s%s)',
                    _linename($line), $expr->{''};
            return 1;
        },
        multiply => sub {
            my($self, $args) = @_;
            my($line, $expr) = @$args;
            my $starting = $self->line($line);
            $starting->type eq 'equals'
                    or die "don't know how to multiply a %s\n", $starting->type;
            my $result = Axiom::Expr->new({
                type => $starting->type,
                args => [ map Axiom::Expr->new({
                    type => 'mullist',
                    args => [ $_->copy, $expr->copy ],
                }), @{ $starting->args } ],
            });
            $self->working($result);
            push @{ $self->rules }, sprintf 'multiply(%s%s)',
                    _linename($line), $expr->{''};
            return 1;
        },
        factor => sub {
            my($self, $args) = @_;
            my($line, $loc, $expr) = @$args;
            my $starting = $self->line($line);
            my $targ = $starting->locate($loc);
            my $repl;
            if ($targ->type eq 'pluslist') {
                $repl = Axiom::Expr->new({
                    type => 'mullist',
                    args => [ $expr, Axiom::Expr->new({
                        type => 'pluslist',
                        args => [ map _div($_, $expr), @{ $targ->args } ],
                    }) ],
                });
            } else {
                die sprintf "don't know how to factor a %s\n", $targ->type;
            }
            $self->working($starting->substitute($loc, $repl));
            push @{ $self->rules }, sprintf 'factor(%s%s, %s)',
                    _linename($line), join('.', @$loc), $expr->{''};
            return 1;
        },
        iterexpand => sub {
            my($self, $args) = @_;
            my($line, $loc) = @$args;
            my $starting = $self->line($line);
            my $iter = $starting->locate($loc);
            my $repl;
            die "Cannot iterate over a %s\n", $iter->type
                    unless $iter->iter;
            if ($iter->type eq 'sum') {
                $repl = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [ map $iter->value_at($_), @{ $iter->range } ],
                });
            } else {
                die sprintf "don't know how to expand a %s\n", $iter->type;
            }
            $self->working($starting->substitute($loc, $repl));
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
                        Axiom::Expr::Const->new({
                            type => 'integer',
                            args => [ $add ],
                        }),
                    ],
                });
                $repl = Axiom::Expr->new({
                    type => 'pluslist',
                    args => [
                        Axiom::Expr::Iter->new({
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
            $self->working($starting->substitute($loc, $repl));
            push @{ $self->rules }, sprintf 'iterextend(%s%s, %s)',
                    _linename($line), join('.', @$loc), $dir;
            return 1;
        },
    );
    sub validate {
        my($self, $rules) = @_;
        my $expr = $self->expr;
        for my $rule (@$rules) {
            my($type, $args) = @$rule;
            return unless $validation{$type}->($self, $args);
        }
        my $diff = $expr->clean->diff($self->working->clean);
        return $self unless $diff;
        die sprintf "Expressions differ at\n  %s\n  %s\n",
                map $_->locate($diff)->str, $expr, $self->working;
    }
}

1;
