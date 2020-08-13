package Axiom::Derive;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;
use Scalar::Util qw{ weaken };

=head1 NAME

Axiom::Derive - objects representing and validating derivation of a line

=head1 Derivations

By default, derivations that refer to a previous theorem will use the
most recently derived expression. This can be overridden by preceding
the other arguments with an explicit reference to another theorem (by
name or by line number) followed by a colon.

=head1 SEE ALSO

L<Axiom::Derive::Axiom>
L<Axiom::Derive::Theorem>
L<Axiom::Derive::Identity>
L<Axiom::Derive::Specify>
L<Axiom::Derive::CondStart>
L<Axiom::Derive::CondEnd>
L<Axiom::Derive::Induction>
L<Axiom::Derive::Equate>
L<Axiom::Derive::Distrib>
L<Axiom::Derive::UnaryDistrib>
L<Axiom::Derive::Add>
L<Axiom::Derive::Multiply>
L<Axiom::Derive::Factor>
L<Axiom::Derive::IterExpand>
L<Axiom::Derive::IterExtend>
L<Axiom::Derive::IterVar>
L<Axiom::Derive::Recurse>

=cut

my %class; BEGIN {
    %class = map {
        my $class = $_;
        eval qq{ use $class; 1; } or die $@;
        +($class->rulename => $class),
    } qw{
        Axiom::Derive::Axiom
        Axiom::Derive::Theorem
        Axiom::Derive::Identity
        Axiom::Derive::Specify
        Axiom::Derive::CondStart
        Axiom::Derive::CondEnd
        Axiom::Derive::Induction
        Axiom::Derive::Equate
        Axiom::Derive::Distrib
        Axiom::Derive::UnaryDistrib
        Axiom::Derive::Add
        Axiom::Derive::Multiply
        Axiom::Derive::Factor
        Axiom::Derive::IterExpand
        Axiom::Derive::IterExtend
        Axiom::Derive::IterVar
        Axiom::Derive::Recurse
    };
}

sub new {
    my($class, $context, $source) = @_;
    my $self = bless {
        context => $context,
        source => $source,
        dict => $context->dict->copy,
        rule => [],
        working => $context->last_expr,
        scope => 0,
    }, $class;
    weaken $self->{context};
    return $self;
}

sub is_derived { 1 }
sub late_resolve { 0 }

sub context { shift->{context} }
sub source { shift->{source} }
sub expr { shift->{expr} }
sub dict { shift->{dict} }
sub rawexpr { shift->{rawexpr} }
sub rule {
    my($self, $new) = @_;
    $self->{rule} = $new if @_ > 1;
    return $self->{rule};
}
sub working {
    my($self, $new) = @_;
    $self->{working} = $new if @_ > 1;
    return $self->{working};
}
sub name {
    my($self, $new) = @_;
    $self->{name} = $new if @_ > 1;
    return $self->{name};
}
sub lookup {
    my($self, $name) = @_;
    return $self->dict->lookup($name);
}
sub introduce {
    my($self, $name) = @_;
    return $self->dict->introduce($name);
}
sub str {
    my($self) = @_;
    return sprintf '%s: %s', $self->rule, $self->rawexpr;
}
sub line {
    my($self, $index) = @_;
    return $index eq ''
        ? $self->working
        : $self->context->expr($index);
}
sub scope {
    my($self, $new) = @_;
    $self->{scope} = $new if @_ > 1;
    return $self->{scope};
}

sub set_error {
    my($self, $error) = @_;
    $self->{error} = $error;
    return 0;
}
sub clear_error {
    my($self) = @_;
    return delete $self->{error};
}

{
    my %derive_args; END { %derive_args = () }
    sub _derive_args {
        my($class) = @_;
        use Regexp::Grammars;
        return $derive_args{$class} //= do {
            my $rule = $class->rulename;
            my $args = $class->derive_args;
            qr{
                <extends: Axiom::Derive>
                <nocontext:>
                ^ \s* $rule \s* $args \s* : \s* <expr=Relation> \s* \z
            }x;
        };
    }
}

sub derive {
    my($class, $source, $context, $debug) = @_;
    my($name) = ($source =~ /^\s*(\w+)/)
            or die "Can't find rule: $source";
    $class = $class{$name}
            or die "Unknown rule '$name' in $source";
    my $self = $class->new($context, $source, $debug);
    {
        my $local = Axiom::Expr->local_dict($self->dict);
        $source =~ _derive_args($class)
                or die "Can't parse derivation: $source";
    }
    my($args, $expr) = @/{qw{ args expr }};
    $expr->resolve($self->dict) unless $self->late_resolve;
    $self->{rawexpr} = $expr->rawexpr;
    $self->{expr} = $expr;
    die $self->clear_error unless $self->derive($args);
    return $self;
}

sub include {
    my($class, $source, $context, $debug) = @_;
    my($name) = ($source =~ /^\s*(\w+)/)
            or die "Can't find rule: $source";
    $class = $class{$name}
            or die "Unknown rule '$name' in $source";
    return undef if $class->can('include') == \&include;
    my $self = $class->new($context, $source, $debug);
    {
        my $local = Axiom::Expr->local_dict($self->dict);
        $source =~ _derive_args($class)
                or die "Can't parse derivation: $source";
    }
    my($args, $expr) = @/{qw{ args expr }};
    $expr->resolve($self->dict);
    $self->{rawexpr} = $expr->rawexpr;
    $self->{expr} = $expr;
    die $self->clear_error unless $self->include($args);
    return $self;
}

sub derivere {
    use Regexp::Grammars;
    return state $dre = qr{
<grammar: Axiom::Derive>
<extends: Axiom::Expr>
<nocontext:>
<debug: same>

<rule: varmap> (?: \{ (?: <[args=pair]>* % , )? \} )
<rule: pair> <[args=Variable]> := <[args=Expr]>
<rule: varlist> \{ <[args=Variable]>* % , <.ws>? \}

<token: optline>
    <args=line> : <args=(?{ $MATCH{args}{args} })>
    | <args=(?{ '' })>
<token: line>
    <args=(?: \d+ (?: \. \d+ )* )>
    | <args=rulename> <args=(?{ $MATCH{args}{args} })>
<token: rulename> <args=(?:(?:[a-z]\w*\.)?[A-Z]\w*(?!\w))>
<token: location> <[args=arg]>+ % \.
<token: arg> \d+
<token: num> -?\d+
    }x;
}
BEGIN { derivere() }

sub _zero {
    return Axiom::Expr->new({
        type => 'integer',
        args => [ '0' ],
    });
}

sub _one {
    return Axiom::Expr->new({
        type => 'integer',
        args => [ '1' ],
    });
}

sub _mone {
    return Axiom::Expr->new({
        type => 'integer',
        args => [ '-1' ],
    });
}

sub _linename {
    my($self, $line) = @_;
    return '' unless defined $line && length $line;
    return "$line: ";
}

sub _varmap {
    my($self, $map) = @_;
    return '{ }' unless defined $map && keys %$map;
    return sprintf '{ %s }', join ', ', map {
        my($var, $expr) = @{ $_->{args} };
        sprintf '%s := %s', $var->name, $expr->rawexpr;
    } @{ $map->{args} };
}

sub validate_diff {
    my($self, $result) = @_;
    my $expr = $self->expr;
    if (my $diff = $result->diff($expr)) {
        return $self->set_error(sprintf(
            "Expressions differ at\n  %s\n  %s\nclean:\n  %s\n  %s\n",
            map($_->locate($diff)->str, $expr, $result),
            map $_->str, $expr->clean, $result->clean,
        ));
    }
    $self->working($result);
    return 1;
}

sub _new_vars {
    my($self, $expr, $dict, $new) = @_;
    if ($expr->has_newvar) {
        my $ivar = $expr->intro_newvar;
        my $iexpr = $expr->affect_newvar;
        my $args = $expr->args;
        my $name = $args->[$ivar]->name;
        for my $i (0 .. $#$args) {
            local $dict->{$name} = 1 if $i == $ivar || $i == $iexpr;
            $self->_new_vars($args->[$i], $dict, $new);
        }
    } elsif ($expr->type eq 'name') {
        my $name = $expr->name;
        $new->{$name} = 1 unless $dict->{$name};
    } elsif (!$expr->is_const) {
        $self->_new_vars($_, $dict, $new) for @{ $expr->args };
    }
    return;
}

sub new_vars {
    my($self, $expr) = @_;
    my %names = map +($_ => 1), %{ $self->dict->dict };
    my %new;
    $self->_new_vars($expr, \%names, \%new);
    return [ sort keys %new ];
}

sub _all_vars {
    my($expr) = @_;
    my %v;
    $expr->walk_tree(sub {
        my($e) = @_;
        $v{$e->binding->id} = $e
                if $e->type eq 'name' && $e->bindtype ne 'func';
        return;
    });
    return [ values %v ];
}

#
# Find a mapping of the variables in the (name => id) hashref $vars that
# transforms $left to $right.
# If the mapping expression in the (name => expr) hashref $map is defined,
# succeeds only if that mapping is honoured; else sets $map->{name} to any
# mapping found.
#
# Currently very simplistic: will succeed only if a subtree of $right
# exactly maps to each occurrence of a mapped var in $left, or if the LHS
# is a plus- or mul-list for which all but one of the arguments map to
# arguments on the RHS; so it will not # for example find the mapping
# C<a := a + 1> to map C<a + b> to C<a + 1 + b>.
#
sub _find_mapping {
    my($left, $right, $vars, $map) = @_;
    if ($left->is_atom) {
        return $left->diff($right) ? 0 : 1
                unless $left->type eq 'name';
        my $name = $left->name;
        my $id = $left->binding->id;
        return $left->diff($right) ? 0 : 1
                unless defined $vars->{$name};
        die "Name clash: mapped var $name found with conflicting binding"
                unless $id == $vars->{$name};

        return $right->diff($map->{$name})
                if defined $map->{$name};
        $map->{$name} = $right;
        return 1;
    }
    my @la = @{ $left->args };
    my @ra = @{ $right->args };
    if ($left->type ne $right->type) {
        return 0 unless $left->is_list;
        @ra = ($right);
    }
    if (! $left->is_list) {
        return 0 unless @la == @ra;
        for my $i (0 .. $#la) {
            return 0 unless _find_mapping($la[$i], $ra[$i], $vars, $map);
            return 1 unless grep !defined, values %$map;
        }
        return 1;
    }
  LEFT_ARG:
    for (my $li = 0; $li < @la; ++$li) {
        my $la = $la[$li] // next;
        my $v = _all_vars($la);
        next if grep +($vars->{$_->name} // -1) == $_->binding->id, @$v;
        for my $ri (0 .. $#ra) {
            my $ra = $ra[$ri];
            next if $la->diff($ra);
            splice @la, $li, 1;
            splice @ra, $ri, 1;
            redo LEFT_ARG;
        }
        return 0;
    }
    return 0 unless @la == 1;
    my $newleft = $la[0];
    my $newright = @ra ? Axiom::Expr->new({
            type => $right->type,
            args => \@ra,
        })
        : $left->type eq 'pluslist' ? _zero()
        : $left->type eq 'mullist' ? _one()
        : die "logic error";

    return _find_mapping($newleft, $newright, $vars, $map);
}

#
# Finds a mapping of the variables listed in the arrayref $vars that
# transforms the expression $left to $right. Returns undef on failure,
# else a hashref mapping variable names to the appropriate mapping
# expressions.
#
# The variables in $vars are expected to have names distinct from each
# other, and from any other variables in the $left expression.
#
# FIXME: variables _not_ listed in $vars need to match left and right,
# but may not have the same ids. Except if $left and $right are subexprs
# of the same expression - so we'll need a flag to indicate that.
#
sub find_mapping {
    my($self, $left, $right, $vars) = @_;
    my %vars = map +($_->name => $_->binding->id), @$vars;
    my %map = map +($_->name => undef), @$vars;
    die "find_mapping: names clash in input vars"
            unless @$vars == keys %vars;
    return undef unless _find_mapping($left, $right, \%vars, \%map);
    return undef if grep !defined, values %map;
    $_ = $_->copy for values %map;
    return \%map;
}

1;
