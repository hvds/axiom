package Axiom::Derive::Induction;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;

=head1 NAME

Axiom::Derive::Induction - derive a new theorem by induction

=head1 USAGE

  derive: induction
  rule: [ var, expr ]

Applies induction to the last two theorems; these are expected to be of
the form C< P(base) > and C<< \Ax: P(x) -> P(x + 1) >>. The specified
I<var> is the variable used in the second theorem; the specified I<expr>
is the base value used in the first expression. The result is the new
theorem C< \Ax: P(x) >.

TODO: a) allow invocations to override which theorems will be used as
input; b) restrict the resulting theorem to C<< x: x >= base >> unless
that covers the whole domain of the variable (which means knowing what
the domain is, which requires some degree of support for sets).

=cut

*_one = \&Axiom::Derive::_one;

sub rulename { 'induction' }

sub derivere { <<'RE' }
    <rule: induction> induction
        (?{ $MATCH{args} = [] })
RE

sub _inputs {
    my($self, $args) = @_;
    # FIXME: one or both of these should be specifiable
    my $starting = $self->working;
    my $base = $self->context->lines->{$self->context->curline}[-2]->expr;
    return +($starting, $base);
}

sub derive {
    my($self, $args) = @_;
    my($starting, $base) = _inputs($self, $args);
    $starting->type eq 'forall' or die "cannot derive";
    my($var, $se) = @{ $starting->args };
    $se->type eq 'implies' or die "cannot derive";
    $se = $se->args->[0];

    my $map = $self->find_mapping($se, $base, [ $var ]);
    return [ $var, $map->{$var->name} ] if $map;

    die "can't derive this induction";
}

sub validate {
    my($self, $args) = @_;
    my($var, $base_expr) = @$args;
    my($starting, $base) = _inputs($self, $args);
    $starting->type eq 'forall' or die sprintf
            "Induction requires 'forall', not %s\n", $starting->type;

    my($ivar, $iexpr) = @{ $starting->args };
    $ivar->name eq $var->name or die sprintf(
        "Induction variable '%s' does not match '%s' found\n",
        $var->name, $ivar->name,
    );
    $iexpr->type eq 'implies' or die sprintf(
        "Induction requires 'implies', not '%s' in forall\n",
        $iexpr->type,
    );
    my($result, $next) = @{ $iexpr->args };

    # Allow the base_expr to reference any names resolvable at
    # the deepest common subexpr that covers all references
    # to be substituted.
    my $common = $result->common_loc($ivar->binding->id);
    # $result is at [ 2, 1 ] in the primary expr
    my $subdict = $starting->dict_at([ 2, 1, @$common ]);
    $base_expr->resolve($subdict);
    my $expect_base = $result->subst_var($ivar, $base_expr);
    my $diff = $expect_base->diff($base);
    if ($diff) {
        die sprintf "base expressions differ at\n  %s\n  %s\n",
                map $_->locate($diff)->str, $expect_base, $base;
    }

    # The next_expr may resolve the same set of names as above,
    # but may also reference the variable we're substituting.
    $subdict->dict->{$ivar->name} = $ivar->binding;
    my $next_expr = Axiom::Expr->new({
        type => 'pluslist',
        args => [ $var->copy, _one() ],
    });
    $next_expr->resolve($subdict);
    my $expect_next = $result->subst_var($ivar, $next_expr);
    $diff = $expect_next->diff($next);
    if ($diff) {
        die sprintf "next expressions differ at\n  %s\n  %s\n",
                map $_->locate($diff)->str, $expect_next, $next;
    }

    # FIXME: attach 'var >= base_expr -> ...' unless that covers
    # the whole domain of the var.
    $result = Axiom::Expr->new({
        type => 'forall',
        args => [ $ivar->copy, $result ],
    });
    $self->working($result->copy);

    push @{ $self->rules }, sprintf 'induction(%s, %s)',
            $var->name, $base_expr->rawexpr;

    return 1;
}

1;
