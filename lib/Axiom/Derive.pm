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

sub classes {
    state @class = map {
        my $class = $_;
        eval qq{ use $class; 1; } or die $@;
        my $name = $class->rulename;
        my $rulere = $class->rulere;
        my $validate = $class->can('validate');
        my $derivere = $class->derivere;
        my $derive = $class->can('derive');
        +{
            class => $class,
            name => $name,
            rulere => $rulere,
            validate => $validate,
            derivere => $derivere,
            derive => $derive,
        };
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
    \@class;
}

sub new {
    my($class, $context, $source) = @_;
    my $self = bless {
        context => $context,
        source => $source,
        dict => $context->dict->copy,
        rules => [],
        working => $context->last_expr,
        working_name => [],
        scope => 0,
    };
    weaken $self->{context};
    return $self;
}

sub is_derived { 1 }

sub context { shift->{context} }
sub source { shift->{source} }
sub rules { shift->{rules} }
sub expr { shift->{expr} }
sub dict { shift->{dict} }
sub rawexpr { shift->{rawexpr} }
sub working {
    my($self, $new) = @_;
    $self->{working} = $new if @_ > 1;
    return $self->{working};
}
sub working_name { shift->{working_name} }
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
    return sprintf '%s: %s', join('; ', @{ $self->rules }), $self->rawexpr;
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

sub derive {
    my($class, $line, $context, $debug) = @_;
    my $self = $class->new($context, $line);
    my @rules;
    my $dre = derivere($debug);

    my $local = Axiom::Expr->local_dict($self->dict);
    while ($line =~ s{$dre}{}) {
        my($rule, $value) = %{ $/{rule} };
        push @rules, [ $rule, $value->{args} ];
    }
    $line =~ s/^\s+//;

    my $expr = Axiom::Expr->parse($self->dict, $line, $debug) or return;
    $self->{rawexpr} = $line;
    $self->{expr} = $expr;
    $self->validate(\@rules) or return;
    return $self;
}

# FIXME: these new vars are temporary, somehow we need to make them valid
# while they're needed for comparison, then discard them.
sub new_local {
    my($self, $name) = @_;
    my $subdict = $self->dict->subsidiary;
    my $binding = $subdict->insert_local($name);
    my $new = Axiom::Expr->new({
        type => 'name',
        args => [ $binding->name ],
    });
    $new->bind($binding);
    return $new;
}

sub _rulere {
    use Regexp::Grammars;
    return state $gdrre = do {
        my $classes = classes();
        my $indent = " " x 4;
        my $names = join "\n$indent| ",
                map sprintf('<%s>', $_->{name}), @$classes;
        my $rules = join "", map $_->{rulere}, @$classes;
        qr{
<grammar: Axiom::Derive::Validate>
<extends: Axiom::Expr>
<nocontext:>
<debug: same>

<rule: rule> (?:
    @{[ $names ]}
)
@{[ $rules ]}

<rule: varmap> (?: \{ (?: <[args=pair]>* % , )? \} )
<rule: pair> <[args=Variable]> := <[args=Expr]>
<rule: varlist> \{ <[args=Variable]>* % , <.ws>? \}

<token: optline>
    <args=line> : <args=(?{ $MATCH{args}{args} })>
    | <args=(?{ '' })>
<token: line>
    <args=(?: \d+ (?: \. \d+ )* )>
    | <args=rulename> <args=(?{ $MATCH{args}{args} })>
<token: rulename> <args=(?:(?:[a-z]+\.)?[A-Z]\w*(?!\w))>
<token: location> <[args=arg]>+ % \.
<token: arg> \d+
<token: num> -?\d+
        }x;
    };
}
BEGIN { _rulere() }

sub rulere {
    use Regexp::Grammars;
    my($debug) = @_;
    return $debug
        ? (state $drre = qr{
            <extends: Axiom::Derive::Validate>
            <nocontext:>
            <debug: match>
            ^ <rule> \z
        }x)
        : (state $rre = qr{
            <extends: Axiom::Derive::Validate>
            <nocontext:>
            ^ <rule> \z
        }x);
}

sub _derivere {
    use Regexp::Grammars;
    return state $gddre = do {
        my $classes = classes();
        my $indent = " " x 4;
        my $names = join "\n$indent| ",
                map sprintf('<%s>', $_->{name}), @$classes;
        my $rules = join "", map $_->{derivere}, @$classes;
        qr{
<grammar: Axiom::Derive>
<extends: Axiom::Expr>
<nocontext:>
<debug: same>

<rule: rule> (?:
    @{[ $names ]}
)
@{[ $rules ]}

<rule: varmap> (?: \{ (?: <[args=pair]>* % , )? \} )
<rule: pair> <[args=Variable]> := <[args=Expr]>
<rule: varlist> \{ <[args=Variable]>* % , <.ws>? \}

<token: optline>
    <args=line> : <args=(?{ $MATCH{args}{args} })>
    | <args=(?{ '' })>
<token: line>
    <args=(?: \d+ (?: \. \d+ )* )>
    | <args=rulename> <args=(?{ $MATCH{args}{args} })>
<token: rulename> <args=(?:(?:[a-z]+\.)?[A-Z]\w*(?!\w))>
<token: location> <[args=arg]>+ % \.
<token: arg> \d+
<token: num> -?\d+
        }x;
    };
}
BEGIN { _derivere() }

sub derivere {
    use Regexp::Grammars;
    my($debug) = @_;
    return $debug
        ? (state $ddre = qr{
            <extends: Axiom::Derive>
            <nocontext:>
            <debug: match>
            ^ <rule> [:;]
        }x)
        : (state $dre = qr{
            <extends: Axiom::Derive>
            <nocontext:>
            ^ <rule> [:;]
        }x);
}

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
    return "$line:";
}

sub _varmap {
    my($self, $map) = @_;
    return '{ }' unless defined $map && keys %$map;
    return sprintf '{ %s }', join ', ', map {
        my($var, $expr) = @{ $_->{args} };
        sprintf '%s := %s', $var->name, $expr->rawexpr;
    } @{ $map->{args} };
}

{
    state %validate_for = map +($_->{name} => $_->{validate}), @{ classes() };
    state %derive_for = map +($_->{name} => $_->{derive}), @{ classes() };
    sub validate {
        my($self, $rules) = @_;
        for my $rule (@$rules) {
            my($type, $args) = @$rule;
            my $vargs = $derive_for{$type}->($self, $args);
            return unless $validate_for{$type}->($self, $vargs);
        }
        my $expr = $self->expr;
        $expr->resolve($self->dict);
        my $diff = $expr->diff($self->working);
        return $self unless $diff;
        die sprintf "Expressions differ at\n  %s\n  %s\nclean:\n  %s\n  %s\n",
                map($_->locate($diff)->str, $expr, $self->working),
                map $_->str, $expr->clean, $self->working->clean;
    }
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

1;
