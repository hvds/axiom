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

=cut

sub rulename { 'conjoin' }

sub derive_args {
    q{
        \( <[args=optline]> \s* <[args=line]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
    };
}

sub derive {
    my($self, $args) = @_;
    return $self->validate($args);
}

sub validate {
    my($self, $args) = @_;
    my($line, $conline) = @$args;
    my $ea = $self->line($line)->copy;
    $ea->resolve($self->dict);
    my $eb = $self->line($conline)->copy;
    $eb->resolve($self->dict);
    my @args;
    push @args, ($ea->type eq 'andlist') ? @{ $ea->args } : $ea;
    push @args, ($eb->type eq 'andlist') ? @{ $eb->args } : $eb;
    my $repl = Axiom::Expr->new({
        type => 'andlist',
        args => \@args,
    });

    $self->validate_diff($repl) or return;
    $self->rule(sprintf 'conjoin(%s, %s)',
            $self->_linename($line), $conline);

    return 1;
}

1;
