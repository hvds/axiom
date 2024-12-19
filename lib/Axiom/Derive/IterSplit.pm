package Axiom::Derive::IterSplit;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::IterSplit - split an iterator into two parts

=head1 USAGE

  derive: itersplit ( line? )
  rule: [ line, location, expr ]

Replaces \iter_{x=a}^b{e} with \iter_{x=a}^c{e} + \iter_{x=c}^b{e}.
(Combines by multiplication rather than addition for \prod.)

TODO: in principle we should require a <= c <= b, but that would require
support for inequalities and additional reasoning: for now, we rely on
the user to ensure that.
TODO: also allow the reverse process.

=cut

sub rulename { 'itersplit' }

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
    my $loc = $starting->diff($target);

    my $se = $starting->locate($loc);
    my $te = $target->locate($loc);
    my($ta, $type, $listtype);
    if ($se->is_list) {
        $listtype = $se->type;
        return $self->set_error(
            "need $listtype on rhs, not @{[ $te->type ]}"
        ) unless $te->type eq $listtype;
        (my($sa), $ta) = $self->difflist($se, $te);
        return $self->set_error(
            "need one iterator on lhs, not @{[ scalar @$sa ]}"
        ) unless @$sa == 1;
        $sa = $sa->[0];
        $se = $se->args->[$sa];
        push @$loc, $sa + 1;
    } elsif ($se->is_iter) {
        $listtype = $se->combiner;
        $ta = [ 0 .. $#{ $te->args } ];
    } else {
        return $self->set_error(
            "don't know how to apply itersplit to lhs @{[ $se->type ]}"
        );
    }
    $type = $se->type;
    return $self->set_error(
        "lhs not iterator but $type"
    ) unless $se->is_iter;
    return $self->set_error(
        "lhs iterator needs to form a @{[ $se->combiner ]}, not a $listtype"
    ) unless $listtype eq $se->combiner;
    return $self->set_error(
        "rhs needs to form a @{[ $listtype ]}, not a @{[ $te->type ]}"
    ) unless $te->type eq $listtype;
    return $self->set_error(
        "need two $type on rhs, not @{[ scalar @$ta ]}"
    ) unless @$ta == 2;
    my($left, $right) = @{ $te->args }[@$ta];
    return $self->set_error("rhs.0 is not $type")
            unless $left->type eq $type;
    return $self->set_error("rhs.1 is not $type")
            unless $right->type eq $type;

    my($var, $ofrom, $oto, $oexpr) = @{ $se->args };
    $var = $var->copy;
    my($lvar, $lfrom, $lto, $lexpr) = @{ $left->args };
    my($rvar, $rfrom, $rto, $rexpr) = @{ $right->args };
    if ($ofrom->diff($lfrom, 1) && !$ofrom->diff($rfrom, 1)) {
        ($left, $right) = ($right, $left);
        ($lvar, $lfrom, $lto, $lexpr) = @{ $left->args };
        ($rvar, $rfrom, $rto, $rexpr) = @{ $right->args };
    }

    return $self->set_error(
        "rhs.0 starts at @{[ $lfrom->str ]}, not @{[ $ofrom->str ]}"
    ) if $ofrom->diff($lfrom, 1);
    return $self->set_error(
        "rhs.1 ends at @{[ $rto->str ]}, not @{[ $oto->str ]}"
    ) if $oto->diff($rto, 1);

    return $self->set_error(
        "rhs.0 has expr @{[ $lexpr->str ]}, not @{[ $oexpr->str ]}"
    ) if $oexpr->diff($lexpr, 1);
    return $self->set_error(
        "rhs.1 has expr @{[ $rexpr->str ]}, not @{[ $oexpr->str ]}"
    ) if $oexpr->diff($rexpr, 1);
    return $self->set_error(
        "introduced exprs @{[ $lto->str ]} and @{[ $rfrom->str ]} do not match"
    ) if $lto->diff($rfrom, 1);

    return 1 if $self->validate([ $line, $loc, $lto->copy ]);
    warn $self->clear_error;
    return 0;
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc, $splitexpr) = @$args;
    my $starting = $self->line($line);

    my $iter = $starting->locate($loc);
    my $subdict = $starting->dict_at($loc);
    $splitexpr->resolve($subdict);

    my $repl;
    if ($iter->is_iter) {
        my($var, $from, $to, $expr) = @{ $iter->args };
        $repl = Axiom::Expr->new({
            type => $iter->combiner,
            args => [
                Axiom::Expr->new({
                    type => $iter->type,
                    args => [
                        $var->copy,
                        $from->copy,
                        $splitexpr->copy,
                        $expr->copy,
                    ],
                }),
                Axiom::Expr->new({
                    type => $iter->type,
                    args => [
                        $var->copy,
                        $splitexpr->copy,
                        $to->copy,
                        $expr->copy,
                    ],
                }),
            ],
        });
    } else {
        return $self->set_error(sprintf(
            "Don't know how to split a %s\n", $iter->type,
        ));
    }

    if (@$loc) {
        my $ploc = [ @$loc[0 .. $#$loc - 1] ];
        my $parent = $starting->locate($ploc);
        if ($parent->type eq $iter->combiner) {
            my $i = pop(@$loc) - 1;
            my $args = $parent->args;
            $repl = Axiom::Expr->new({
                type => $iter->combiner,
                args => [
                    (map $_->copy, @$args[0 .. $i - 1]),
                    @{ $repl->args },
                    (map $_->copy, @$args[$i + 1 .. $#$args]),
                ],
            });
        }
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'itersplit(%s%s, %s)',
            $self->_linename($line), join('.', @$loc), $splitexpr->str);

    return 1;
}

1;
