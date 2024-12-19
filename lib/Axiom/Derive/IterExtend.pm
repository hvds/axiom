package Axiom::Derive::IterExtend;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::IterExtend - change the range of an iterator

=head1 USAGE

  derive: iterextend ( line? )
  rule: [ line, location, which, dir ]

Modifies the iterator at I<location> by adding or removing one element,
at either the I<from> or the I<to> end.

We modify the I<to> value if I<which> is C<1>, or I<from> if I<which> is
C<-1>. We extend upwards if I<dir> is C<1>, or downwards if I<dir> is C<-1>.
In every case we add or subtract the appropriate balancing expression.

Eg given C< x = \sum_{i=1}^n{y^i} >, C<iterextend(2, -1, -1)> will derive
C< x = \sum_{i=0}^n{y^i} - y^0 >.

TODO: currently supports only type C<sum>.

=cut

sub rulename { 'iterextend' }

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

    my($loca, $lasteq);
    my $find_iter = sub {
        my($self, $loc) = @_;
        # FIXME: other relations are (or will be) available
        $lasteq = $loc if $self->type eq 'equals';
        if ($self->is_iter) {
            my $side = $loc->[0 + @$lasteq];
            push @{ $loca->[$side] }, $loc;
        }
        return;
    };
    my(@sloc, @tloc);
    $loca = \@sloc;
    $starting->walk_locn($find_iter);
    $loca = \@tloc;
    $target->walk_locn($find_iter);

    for my $side (1 .. 2) {
        my($sside, $tside) = ($sloc[$side], $tloc[$side]);
        next unless $sside && $tside;
        T: for (my $ti = 0; $ti < @$tside; ++$ti) {
            last if $ti >= @$tside;
            my $te = $target->locate($tside->[$ti]);
            for my $si (0 .. $#$sside) {
                my $se = $starting->locate($sside->[$si]);
                next if $se->diff($te);
                splice @$sside, $si, 1;
                splice @$tside, $ti, 1;
                redo T;
            }
        }
    }

    for my $side (1 .. 2) {
        my($sside, $tside) = ($sloc[$side], $tloc[$side]);
        next unless $sside && $tside
                && @$sside == 1 && @$tside == 1;
        my $loc = $sside->[0];
        my $se = $starting->locate($loc);
        my $te = $target->locate($tside->[0]);
        next if $se->type ne $te->type;

        my($sv, $sfrom, $sto, $sexpr) = @{ $se->args };
        my($tv, $tfrom, $tto, $texpr) = @{ $te->args };
        next if $sexpr->diff($texpr);

        my $from = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $tfrom->copy,
                Axiom::Expr->new({
                    type => 'negate',
                    args => [ $sfrom->copy ],
                }),
            ],
        })->clean;
        next unless $from->type eq 'integer';

        my $to = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $tto->copy,
                Axiom::Expr->new({
                    type => 'negate',
                    args => [ $sto->copy ],
                }),
            ],
        })->clean;
        next unless $to->type eq 'integer';

        my $fn = $from->args->[0];
        my $tn = $to->args->[0];
        # FIXME: could generate multiple iterextend validations
        next unless abs($fn) + abs($tn) == 1;

        return 1 if $self->validate([ $line, $loc, $fn ? -1 : 1, $fn || $tn ]);
        warn $self->clear_error;
    }
    return $self->set_error("don't know how to derive this");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $which, $dir) = @$args;
    my $starting = $self->line($line);

    my $iter = $starting->locate($loc);
    my $repl;

    if ($iter->type eq 'sum') {
        my($var, $from, $to, $expr) = @{ $iter->args };
        my $base = ($which > 0) ? $to : $from;
        my $var_at = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                $base->copy,
                Axiom::Expr->new_const($dir > 0 ? 1 : -1),
            ],
        });
        my $newfrom = ($which > 0) ? $from->copy : $var_at;
        my $newto = ($which > 0) ? $var_at : $to->copy;
        my($sign, $diff) = ($which > 0)
            ? ($dir > 0) ? (-1, $var_at) : (1, $to)
            : ($dir > 0) ? (1, $from) : (-1, $var_at);
        my $value = $iter->value_at($diff);
        $repl = Axiom::Expr->new({
            type => 'pluslist',
            args => [
                Axiom::Expr->new({
                    type => 'sum',
                    args => [
                        $var->copy,
                        $newfrom,
                        $newto,
                        $expr->copy,
                    ],
                }),
                ($sign > 0
                    ? $value
                    : Axiom::Expr->new({
                        type => 'negate',
                        args => [ $value ],
                    }),
                ),
            ],
        });
    } else {
        return $self->set_error(sprintf(
            "Don't know how to extend a %s\n", $iter->type,
        ));
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'iterextend(%s%s, %s, %s)',
            $self->_linename($line), join('.', @$loc), $which, $dir);

    return 1;
}

1;
