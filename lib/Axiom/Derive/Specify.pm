package Axiom::Derive::Specify;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Specify - fix a specific value for a universal quantifier

=head1 USAGE

  derive: specify ( line? )
  rule: [ line, var, expr ]

Given a prior theorem of the form C< \Aa: P(a) >, constructs the
new theorem C< P(x) >.

Can also go from C< \Aa: \Ab: P(a, b) > to C< \Ab: P(x, b) >, or from
C< \Aa: P(a) > to C< \Ax: \Ay: P(Q(x, y)) >. But for now can only specify
one variable at a time: apply repeatedly to specify more.

TODO: extend to allow specification of multiple variables.

=cut

sub rulename { 'specify' }

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
    return $self->set_error("Too many vars for specify")
            if @var > 1;

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
# FIXME: trying to map x -> x will leave @var empty
return $self->set_error(sprintf('no var to map')) unless @var;
    return $self->validate([ $line, $var[0], $mapping->{ $var[0]->name } ])
            if $mapping;
    return $self->set_error("don't know how to derive this specify");
}

sub validate {
    my($self, $args) = @_;
    my($line, $var, $value) = @$args;
    my $starting = $self->line($line);
    my $target = $self->expr;

    my(@svar, @var);
    my $se = $starting;
    while ($se->type eq 'forall') {
        (my($svar), $se) = @{ $se->args };
        push @svar, $svar unless $svar->name eq $var->name;
    }
    my $te = $target;
    while ($te->type eq 'forall') {
        (my($tvar), $te) = @{ $te->args };
        push @var, $tvar;
    }
    for my $tvar (reverse @var) {
        last unless @svar;
        pop @svar if $tvar->name eq $svar[-1]->name;
    }
    return $self->set_error(sprintf(
        'Target misses quantifier(s) from source: [%s]',
        join ', ', map $_->name, @svar
    )) if @svar;

    my($expr, $eloc) = ($se->copy, []);
    # Wrap in an extra '\Av: (...)' for resolving, then strip off after subst
    for (reverse(@var), $var) {
        $expr = Axiom::Expr->new({
            type => 'forall',
            args => [ $_->copy, $expr ],
        });
        push @$eloc, 2;
    }
    $expr->resolve($self->dict);
    my $edict = $expr->dict_at($eloc);
    # TODO: strip $var out of $edict, it should not resolve
    # TODO: verify that quantified variables added in target do not appear
    # in source
    $var = $var->copy;
    $var->resolve($edict);
    my $result = _subst_var_lazy($expr, $var, $value) // return;
    $result = $result->args->[1];
    # multiply introduced variables may be misresolved, so go once more
    $result->resolve($self->dict);

    $self->validate_diff($result) or return;
    $self->rule(sprintf 'specify(%s%s, %s)',
            $self->_linename($line), $var->rawexpr, $value->rawexpr);

    return 1;
}

sub _subst_var_lazy {
    my($self, $var, $value) = @_;
    my $si = $var->binding->id;
    my $map;
    my $result = eval { $self->copy_with_locn(sub {
        my($other, $loc) = @_;
        return undef unless $other->type eq 'name';
        return undef unless $si == $other->binding->id;
        return undef if "@$loc" eq "1";
        my $dict = $self->dict_at($loc);
        my $hwm = scalar @{ $dict->bind };  # FIXME, should be method
        my $v = $value->copy;
        $v->resolve($dict);
        if ($map) {
            # verify that the previous mapping is still valid
            for my $source (keys %$map) {
                my($target, @locs) = @{ $map->{$source} };
                for (@locs) {
                    my $e = $v->locate($_);
                    my $binding = $e->binding->id;
                    next if $binding == $target;
                    $self->set_error(sprintf(
                        'var %s mapped to varying bind ids', $source
                    ));
                    die 'set_error';
                }
            }
        } else {
            # discover the mapping
            $value->resolve($dict);
            my %thismap;
            $value->walk_locn(sub {
                my($this, $loc) = @_;
                return unless $this->type eq 'name';
                my $name = $this->args->[0];
                my $binding = $this->binding->id;
                return if $binding >= $hwm;     # local to the value
                $thismap{$name}[0] //= $binding;
                if ($thismap{$name}[0] != $binding) {
                    $self->set_error(sprintf(
                        'var %s mapped to multiple bind ids', $name
                    ));
                    die 'set_error';
                }
                push @{ $thismap{$name} }, [ @$loc ];
                return;
            });
        }
        return $v;
    }) };
    if ($@) {
        die $@ if $@ !~ /^set_error/;
        return undef;
    }
    return $result;
}

1;
