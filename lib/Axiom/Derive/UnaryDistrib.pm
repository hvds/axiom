package Axiom::Derive::UnaryDistrib;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;
use List::Util qw{ first };

=head1 NAME

Axiom::Derive::UnaryDistrib - distribute an operator over its argument

=head1 USAGE

  derive: unarydistrib ( line? )
  rule: [ line, location ]

Distribute the unary operator at the given I<location>. 

TODO: we currently support only type C<negate> distributing over a
C<pluslist> or C<mullist>, type C<sum> distributing over a C<pluslist>,
and type C<pow> distributing over a C<pluslist> with positive integer
power.

=cut

sub rulename { 'unarydistrib' }

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

    my @choice;
    $starting->walk_locn(sub {
        my($expr, $loc) = @_;
        if ($expr->type eq 'negate') {
            my $subtype = $expr->args->[0]->type;
            push @choice, $loc if $subtype eq 'pluslist'
                    || $subtype eq 'mullist';
        } elsif ($expr->type eq 'sum') {
            my $subtype = $expr->args->[3]->type;
            push @choice, $loc if $subtype eq 'pluslist';
        } elsif ($expr->type eq 'pow') {
            my($val, $pow) = @{ $expr->args };
            push @choice, $loc if $val->type eq 'pluslist'
                    && $pow->type eq 'integer'
                    && $pow->rat > 0;
        }
        return;
    });

    for my $loc (@choice) {
        return 1 if $self->validate([ $line, $loc ]);
        $self->clear_error;
    }
    return $self->set_error("don't know how to derive this unarydistrib");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc) = @$args;
    my $starting = $self->line($line)->copy;
    $starting->resolve($self->dict);
    my $source_dict = $starting->dict_at([]);

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
            my @var = map {
                my $binding = $source_dict->insert_local($name);
                my $new = Axiom::Expr->new({
                    type => 'name',
                    args => [ $name ],
                });
                $new->bind($binding);
                $new;
            } 0 .. $#{ $arg->args };
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
    } elsif ($expr->type eq 'pow') {
        my($val, $pow) = @{ $expr->args };
        $val->type eq 'pluslist' or return $self->set_error(sprintf(
            "don't know how to distribute a pow over a %s\n",
            $val->type,
        ));
        $pow->type eq 'integer' or return $self->set_error(sprintf(
            "don't know how to distribute a pow with a type %s power\n",
            $pow->type,
        ));
        my $p = $pow->args->[0];
        $p >= 0 or return $self->set_error(sprintf(
            "don't know how to distribute a pow with a negate power\n",
        ));
        my $base = _fact($p);
        my @pargs;
        my @i = (0) x $p;
      POW_LOOP:
        while (1) {
            my $count = $base;
            my @margs;
            my $last;
            my $lastpow;
            my $take = sub {
                if (defined $last) {
                    my $arg = $val->args->[$last];
                    push @margs, ($lastpow == 1)
                        ? $arg->copy
                        : Axiom::Expr->new({
                            type => 'pow',
                            args => [
                                $arg->copy,
                                Axiom::Expr->new({
                                    type => 'integer',
                                    args => [ "$lastpow" ],
                                })
                            ],
                        });
                    $count /= _fact($lastpow);
                    $lastpow = 0;
                }
                $last = $_;
            };
            for (@i) {
                $take->() if $_ != ($last // -1);
                $last = $_;
                ++$lastpow;
            }
            $take->();
            unshift @margs, Axiom::Expr->new({
                type => 'integer',
                args => [ "$count" ],
            }) unless $count == 1;
            push @pargs, Axiom::Expr->new({
                type => 'mullist',
                args => \@margs,
            });

            my $index = $#i;
            while (1) {
                last POW_LOOP if $index < 0;
                --$index, next if ++$i[$index] >= @{ $val->args };
                $i[$_] = $i[$index] for $index +1 .. $#i;
                last;
            }
        }
        $repl = Axiom::Expr->new({
            type => 'pluslist',
            args => \@pargs,
        });
    }
    unless ($repl) {
        return $self->set_error(sprintf(
            "don't know how to distribute a %s%s\n",
            $expr->type, $arg ? ' over a ' . $arg->type : '',
        ));
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'unarydistrib(%s%s)',
            $self->_linename($line), join('.', @$loc));

    return 1;
}

{
    my @fact; BEGIN { @fact = (1, 1) }
    sub _fact {
        my($n) = @_;
        return $fact[$n] //= $n * _fact($n - 1);
    }
}

1;
