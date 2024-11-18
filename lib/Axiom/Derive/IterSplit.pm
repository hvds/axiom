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

TODO: in principle we should require a <= c <= b, but in practice we
are dealing with simple polynomials for which it doesn't matter.
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

    while (1) {
        my $se = $starting->locate($loc);
        my $te = $target->locate($loc);
        return $self->set_error("lhs not iterator but @{[ $se->type ]}")
                unless $se->is_iter;
        my($var, $ofrom, $oto, $oexpr) = @{ $se->args };
        $var = $var->copy;
        my $join = $se->combiner;
        return $self->set_error("rhs is not $join")
                unless $te->type eq $join;
        return $self->set_error("rhs does not join 2 elements")
                unless @{ $te->args } == 2;
        my($left, $right) = @{ $te->args };
        return $self->set_error("rhs.0 is not @{[ $se->type ]}")
                unless $left->type eq $se->type;
        return $self->set_error("rhs.1 is not @{[ $se->type ]}")
                unless $right->type eq $se->type;

        my($lvar, $lfrom, $lto, $lexpr) = @{ $left->args };
        return $self->set_error("rhs.0 starts at @{[ $lfrom->str ]}, not @{[ $ofrom->str ]}")
                if $ofrom->diff($lfrom, 1);

        my($rvar, $rfrom, $rto, $rexpr) = @{ $right->args };
        return $self->set_error("rhs.1 ends at @{[ $rto->str ]}, not @{[ $oto->str ]}")
                if $oto->diff($rto, 1);

        return $self->set_error("rhs.0 has expr @{[ $lexpr->str ]}, not @{[ $oexpr->str ]}")
                if $oexpr->diff($lexpr, 1);
        return $self->set_error("rhs.1 has expr @{[ $rexpr->str ]}, not @{[ $oexpr->str ]}")
                if $oexpr->diff($rexpr, 1);
        return $self->set_error("introduced exprs @{[ $lto->str ]} and @{[ $rfrom->str ]} do not match")
                if $lto->diff($rfrom, 1);

        return 1 if $self->validate([ $line, $loc, $lto->copy ]);
        warn $self->clear_error;
    }
    return $self->set_error("don't know how to derive this");
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

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'itersplit(%s%s, %s)',
            $self->_linename($line), join('.', @$loc), $splitexpr->str);

    return 1;
}

1;
