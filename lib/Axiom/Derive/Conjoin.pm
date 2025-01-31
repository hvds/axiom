package Axiom::Derive::Conjoin;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Conjoin - join two theorems with 'and'

=head1 USAGE

  derive: conjoin ( line?, conline )
  rule: [ line, conline ]

Given prior theorems C< P > and C< Q >, constructs the new theorem
C< P & Q >.

C< \Ax: P > and C< \Ax: Q > may give either C< (\Ax: P) & (\Ax: Q) >
or C< \Ax: (P & Q) >.

=cut

sub rulename { 'conjoin' }

sub derive_args {
    (2, q{ <[args=optline]> \s* <[args=line]> });
}

sub derive {
    my($self, $args) = @_;
    return $self->validate($args);
}

sub _topall {
    my($expr) = @_;
    my @vars;
    while ($expr->type eq 'forall') {
        (my($var), $expr) = @{ $expr->args };
        push @vars, $var;
    }
    return +(\@vars, $expr);
}

sub validate {
    my($self, $args) = @_;
    my($line, $conline) = @$args;
    my $dict = $self->dict;
    my $ea = $self->line($line)->copy;
    my $eb = $self->line($conline)->copy;
    my $ec = $self->expr;
    $_->resolve($dict) for ($ea, $eb, $ec);
    my($shared, undef) = _topall($ec);
    my($sepa, $sepb);
    if (@$shared) {
        ($sepa, $ea) = _topall($ea);
        ($sepb, $eb) = _topall($eb);
        my($ai, $bi) = ($#$shared) x 2;
        for (reverse 0 .. $#$sepa) {
            last if $ai < 0;
            next unless $sepa->[$_]->name eq $shared->[$ai]->name;
            splice @$sepa, $_, 1;
            --$ai;
        }
        for (reverse 0 .. $#$sepb) {
            last if $bi < 0;
            next unless $sepb->[$_]->name eq $shared->[$bi]->name;
            splice @$sepb, $_, 1;
            --$bi;
        }
        --$ai while $ai >= 0 && $ea->is_independent($shared->[$ai]);
        --$bi while $bi >= 0 && $eb->is_independent($shared->[$bi]);
        return $self->set_error(sprintf(
            'Mismatched vars'
        )) unless $ai < 0 && $bi < 0;
        $ea = Axiom::Expr->new({
            type => 'forall',
            args => [ $_, $ea ]
        }) for reverse @$sepa;
        $eb = Axiom::Expr->new({
            type => 'forall',
            args => [ $_, $eb ]
        }) for reverse @$sepb;
    }
    my @args;
    push @args, ($ea->type eq 'andlist') ? @{ $ea->args } : $ea;
    push @args, ($eb->type eq 'andlist') ? @{ $eb->args } : $eb;
    my $repl = Axiom::Expr->new({
        type => 'andlist',
        args => \@args,
    });
    $repl = Axiom::Expr->new({
        type => 'forall',
        args => [ $_, $repl ],
    }) for reverse @$shared;
    $repl->resolve($dict);

    $self->validate_diff($repl) or return;
    $self->rule(sprintf 'conjoin(%s, %s)',
            $self->_linename($line), $conline);

    return 1;
}

1;
