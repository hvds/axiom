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
sub curline { shift->{curline} }
sub curlines {
    my($self) = @_;
    return $self->lines->{$self->curline} //= [];
}
sub curindex {
    my($self) = @_;
    return join '.', grep length, $self->curline, 0 + @{ $self->curlines };
}
sub reset {
    my($self) = @_;
    $self->{lines} = { '' => [] };
    $self->{named} = {};
    $self->{dict} = Axiom::Dict->new;
    $self->{curline} = '';
    return;
}

sub last_expr {
    my($self) = @_;
    my $lines = $self->lines->{$self->curline};
    return undef unless @$lines;
    # Find last line with a derivation (hence a theorem)
    for (my $i = $#$lines; $i >= 0; --$i) {
        return $lines->[$i][1]->expr if $lines->[$i][1];
    }
    return undef;
}
sub line {
    my($self, $index) = @_;
    my $lines = $self->lines;
    my $named = $self->named;
    my $i = $index;
    $i = $named->{$i} if defined $named->{$i};
    $i =~ /^\d+(\.\d+)*$/
            or die "Unknown theorem name '$index' ($i)\n";
    my @parts = split /\./, $i;
    my $where = join '.', @parts[0 .. $#parts - 1];
    my $wlines = $lines->{$where}
            or die "Unknown prefix '$where' for $index\n";
    my $line = $wlines->[$parts[-1]]
            or die "Unknown line $i for $index\n";
    return $line;
}
sub expr {
    my($self, $index) = @_;
    my $line = $self->line($index);
    my $derived = $line->[1]
            or die "Line $index is not a theorem\n";
    return $derived->expr;
}
sub add_line {
    my($self, $entry) = @_;
    my $curindex = $self->curindex;
    push @{ $self->curlines }, $entry;
    return $curindex;
}

sub enter_scope {
    my($self, $entry) = @_;
    $self->{curline} = $self->curindex;
    return $self->add_line($entry);
}

sub leave_scope {
    my($self, $entry) = @_;
    $self->{curline} =~ s{(?:^|\.)\d+\z}{}
            or die "Cannot leave_scope: no scope at $self->{curline}\n";
    return $self->add_line($entry);
}

sub add {
    my($self, $line, $quiet) = @_;
    return if $line =~ /^\s*(?:#.*)?\z/;
    if ($line =~ /^\*/) {
        $self->apply_directive($line, $quiet);
        return;
    }
    my $derive = Axiom::Derive->derive($line, $self, $DEBUG) or return;
    my $struct = [ $line, $derive ];
    my $where = $derive->scope;
    my $curindex;
    if ($where > 0) {
        $curindex = $self->enter_scope($struct);
    } elsif ($where < 0) {
        $curindex = $self->leave_scope($struct);
    } else {
        $curindex = $self->add_line($struct);
    }
    for my $name (@{ $derive->working_name }) {
        warn "Replacing name '$name'\n" if defined $self->named->{$name};
        $self->named->{$name} = $curindex;
    }
    print $derive->str, "\n" unless $quiet;
    return;
}

sub print_lines {
    my($self, $where) = @_;
    my $lines = $self->lines;
    my $these = $lines->{$where} // die "No data for $where";
    $where .= '.' if length $where;
    for (0 .. @$these) {
        my $this = "$where$_";
        if ($lines->{$this}) {
            $self->print_lines($this);
        }
        last if $_ == @$these;
        printf "%s: %s\n", $this, $these->[$_][0];
    }
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
        my $expr = $self->line($name)
                // die "No line to diagnose for '$name'\n";
        use Data::Dumper; print Dumper($expr);
        print $expr->[0], "\n";
        print $expr->[1]->expr->str, "\n";
        return;
    } elsif ($line =~ bindre()) {
        my $type = $/{Type};
        my @names = map $_->name, @{ $/{Name}{Name} };
        my $dict = $self->dict->copy;
        $dict->insert($_, $type) for @names;
        $self->{dict} = $dict;    # if successful for all names
        $self->add_line([ $line ]);
    } elsif ($line eq '*terse') {
        my $named = $self->named;
        my $lines = $self->lines;
        for (sort { $named->{$a} <=> $named->{$b} } keys %$named) {
            printf "%s: %s\n", $_, $self->line($_)->[0];
        }
        return;
    } elsif ($line eq '*list') {
        $self->print_lines('');
        return;
    } elsif ($line eq '*dict') {
        print $self->dict->str;
        return;
    } elsif ($line eq '*named') {
        use Data::Dumper; print Dumper($self->named);
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
