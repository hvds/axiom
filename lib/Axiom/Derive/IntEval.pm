package Axiom::Derive::IntEval;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::IntEval - evaluate a definite integral

=head1 USAGE

  derive: inteval ( line? )
  rule: [ line, location ]

Replaces \eval_{x=a}^b{e(x)} with e(b) - e(a).

=cut

sub rulename { 'inteval' }

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
    my $sfrom = $starting->locate($loc);
    if ($sfrom->type eq 'inteval') {
        return $self->validate([ $line, $loc ]);
    }

    if ($sfrom->is_list) {
        my $afrom = $sfrom->args;
        my @i = grep $afrom->[$_]->type eq 'inteval', 0 .. $#$afrom;
        if (@i == 1) {
            return $self->validate([ $line, [ @$loc, $i[0] + 1 ] ]);
        }
        my $sto = $target->locate($loc);
        if ($sto->type eq $sfrom->type) {
            for my $cmpto (@{ $sto->args }) {
                next unless $cmpto->type eq 'inteval';
                for (0 .. $#i) {
                    my $cmpfrom = $afrom->[$i[$_]];
                    next if $cmpfrom->diff($cmpto);
                    splice @i, $_, 1;
                    last;
                }
                last if @i == 1;
            }
            if (@i == 1) {
                return $self->validate([ $line, [ @$loc, $i[0] + 1 ] ]);
            }
        }
    }
    return $self->set_error("don't know how to inteval");
}

sub validate {
    my($self, $args) = @_;
    my($line, $loc) = @$args;
    my $starting = $self->line($line);

    my $eval = $starting->locate($loc);
    return $self->set_error(sprintf(
        "Cannot inteval over a %s\n", $eval->type,
    )) unless $eval->type eq 'inteval';

    my($var, $from, $to, $expr) = @{ $eval->args };
    my $repl = Axiom::Expr->new({
        type => 'pluslist',
        args => [
            $eval->value_at($to),
            $eval->value_at($from)->negate,
        ],
    });

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->validate_diff($result) or return;
    $self->rule(sprintf 'inteval(%s%s)',
            $self->_linename($line), join('.', @$loc));

    return 1;
}

1;
