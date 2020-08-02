package Axiom::Derive::Specify;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Specify - fix a specific value for a universal quantifier

=head1 USAGE

  derive: specify ( line? )
  rule: [ line, var, expr ]

Given a prior theorem of the form C< \Aa: P(a) >, constructs the
new theorem C< P(x) >.

=cut

sub rulename { 'specify' }

sub derivere { <<'RE' }
    <rule: specify>
        specify (?: \( <[args=line]>? \) )?
        (?{
            $MATCH{args}[0] = $MATCH{args}[0]{args} if $MATCH{args};
            $MATCH{args} //= [ '' ];
        })
RE

sub derive {
    my($self, $args) = @_;
    my($line) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;
    $target->resolve($self->dict);

    my %var;
    my $seq = $starting;
    while ($seq->is_quant) {
        next unless $seq->type eq 'forall';
        (my($var), $seq) = @{ $seq->args };
        $var{$var->name} = $var;
    }
    my $teq = $target;
    while ($teq->is_quant) {
        next unless $teq->type eq 'forall';
        (my($var), $teq) = @{ $teq->args };
        delete $var{$var->name};
    }

    my @var = @var{ sort keys %var };
    # FIXME: why does specify only allow a single var to be fixed?
    die "Too many vars for specify" if @var > 1;

    my $mapping = $self->find_mapping($seq, $teq, \@var);
    # if we didn't find it, maybe one side has been simplified to the point
    # we no longer recognise it
    if (!$mapping && !$seq->is_atom && $seq->type eq $teq->type) {
        my $sa = $seq->args;
        my $ta = $teq->args;
        if (@$sa == @$ta) {
            for (0 .. $#$sa) {
                $mapping = $self->find_mapping($sa->[$_], $ta->[$_], \@var);
                last if $mapping;
            }
        }
    }
    return [ $line, $var[0], $mapping->{ $var[0]->name } ] if $mapping;
    die "don't know how to derive this specify";
}

sub validate {
    my($self, $args) = @_;
    my($line, $var, $value) = @$args;
    my $starting = $self->line($line);

    my $expr = $starting;
    my $loc = [];
    while (1) {
        $expr->type eq 'forall' or die sprintf(
            'Need forall for specify(), not %s', $expr->type,
        );
        my($fvar, $fexpr) = @{ $expr->args };
        if ($fvar->name ne $var->name) {
            push @$loc, 2;
            $expr = $fexpr;
            next;
        }
        $var = $fvar;
        $expr = $fexpr;
        last;
    }

    # note _not_ including $var
    my $subdict = $starting->dict_at($loc);
    $value->resolve($subdict);

    my $repl = $expr->subst_var($var, $value);
    my $result = $starting->substitute($loc, $repl);
    $self->working($result);

    $self->rule(sprintf 'specify(%s%s, %s)',
            $self->_linename($line), $var->rawexpr, $value->rawexpr);

    return 1;
}

1;
