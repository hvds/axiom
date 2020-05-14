package Axiom::Symbol;

use v5.10;
use strict;
use warnings;

use Axiom::Expr;
use Axiom::Bind;
use Axiom::Derive;
use Axiom::Dict;

our $DEBUG = 0;

sub new {
    my($class) = @_;
    my $self = bless {}, $class;
    $self->reset;
    return $self;
}

sub lines { shift->{lines} }
sub named { shift->{named} }
sub dict { shift->{dict} }
sub reset {
    my($self) = @_;
    $self->{lines} = [];
    $self->{named} = {};
    $self->{dict} = Axiom::Dict->new;
    return;
}

sub next { 1 + @{ shift->{lines} } }
sub expr {
    my($self, $index) = @_;
    my $lines = $self->lines;
    my $named = $self->named;
    $index = $named->{$index} if defined $named->{$index};
    die "Unknown theorem name '$index'\n" if $index !~ /^-?\d+$/;
    $index = @$lines + $index if $index < 0;
    $index >= 0 or return undef;
    my $line = $lines->[$index] or return undef;
    my $derived = $line->[1] or return undef;
    return $derived->expr;
}

sub add {
    my($self, $line, $quiet) = @_;
    if ($line =~ /^\*/) {
        $self->apply_directive($line, $quiet);
        return;
    }
    my $derive = Axiom::Derive->derive($line, $self, $DEBUG) or return;
    push @{ $self->lines }, [ $line, $derive ];
    for my $name (@{ $derive->working_name }) {
        warn "Replacing name '$name'\n" if defined $self->named->{$name};
        $self->named->{$name} = $#{ $self->lines };
    }
    print $derive->str, "\n" unless $quiet;
    return;
}

sub bindre {
    use Regexp::Grammars;
    return state $bindre = qr{
        <extends: Axiom::Expr>
        ^ <Type=BindType> <Name=BindNameList> \z

        <rule: BindNameList> <[Name]>+ %% ,
        <token: BindType> \* (var|func) (?{ $MATCH = $^N })
    }x;
}

sub apply_directive {
    my($self, $line, $quiet) = @_;
    if ($line eq '*reset') {
        $self->reset;
    } elsif ($line eq '*debug') {
        $DEBUG = !$DEBUG;
        $quiet or print $DEBUG ? "debug ON\n" : "debug OFF\n";
        return;
    } elsif ($line =~ m{^\*diag(?:\s+(-?\w+))?\z}) {
        my $name = $1 // -1;
        my $expr = $self->expr($name)
                // die "No line to diagnose for '$name'\n";
        use Data::Dumper; print Dumper($expr);
        print $expr->str, "\n";
        return;
    } elsif ($line =~ bindre()) {
        my $type = $/{Type};
        my @names = map $_->name, @{ $/{Name}{Name} };
        my $dict = $self->dict->copy;
        $dict->insert($_, $type) for @names;
        $self->{dict} = $dict;    # if successful for all names
        push @{ $self->{lines} }, [ $line ];
    } elsif ($line eq '*terse') {
        my $named = $self->named;
        my $lines = $self->lines;
        for (sort { $named->{$a} <=> $named->{$b} } keys %$named) {
            printf "%s: %s\n", $_, $lines->[$named->{$_}]->[1]->source;
        }
        return;
    } elsif ($line eq '*list') {
        my $i = 1;
        for (@{ $self->lines }) {
            printf "%s: %s\n", $i++, $_->[0];
        }
        return;
    } elsif ($line eq '*dict') {
        print $self->dict->str;
        return;
    } elsif ($line =~ /^\*save\s+(\S.+)\z/) {
        my $file = $1 . '.aa';
        open(my $f, '>', $file) or die "$file: $!\n";
        $quiet or print $f $_->[0], "\n" for @{ $self->{lines} };
        close $f;
    } elsif ($line =~ /^\*load\s*(\S.+)\z/) {
        my $file = $1 . '.aa';
        open(my $f, '<', $file) or die "$file: $!\n";
        $self->reset;
        while (<$f>) {
            chomp;
            eval { $self->add($_) };
            warn($@), return if $@;
        }
        close $f;
        $self->apply_directive('*list');
        return;
    } else {
        die "Unknown directive: <$line>\n";
    }
    print $line, "\n" unless $quiet;
}

1;
