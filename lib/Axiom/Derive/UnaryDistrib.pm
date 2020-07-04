package Axiom::Derive::UnaryDistrib;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;
use List::Util qw{ first };

=head1 NAME

Axiom::Derive::UnaryDistrib - distribute an operator over its argument

=head1 USAGE

  unarydistrib ( optline, location )

Distribute the unary operator at the given I<location>. 

TODO: we currently support only type C<negate> distributing over a
C<pluslist> or C<mullist>, and type C<sum> distributing over a C<pluslist>.

=cut

sub rulename { 'unarydistrib' }
sub rulere { <<'RE' }
    <rule: unarydistrib>
        unarydistrib \( <[args=optline]> <[args=location]> \)
        (?{ $MATCH{args}[$_] = $MATCH{args}[$_]{args} for (0, 1) })
RE

sub validate {
    my($self, $args) = @_;
    my($line, $loc) = @$args;
    my $starting = $self->line($line);

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
            my @var = map $self->new_local($name),
                    0 .. $#{ $arg->args };
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
    }
    unless ($repl) {
        die sprintf "don't know how to distribute a %s%s\n",
            $expr->type, $arg ? ' over a ' . $arg->type : '';
    }

    my $result = $starting->substitute($loc, $repl);
    $result->resolve($self->dict);
    $self->working($result);

    push @{ $self->rules }, sprintf 'unarydistrib(%s%s)',
            $self->_linename($line), join('.', @$loc);

    return 1;
}

1;
