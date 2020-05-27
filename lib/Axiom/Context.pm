package Axiom::Context;

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
sub onamed { shift->{onamed} }
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
    $self->{onamed} = [];
    $self->{dict} = Axiom::Dict->new;
    $self->{curline} = '';
    return;
}

sub subsidiary {
    my($self) = @_;
    my $new = ref($self)->new;
    $new->{dict} = $self->dict->subsidiary;
    return $new;
}

sub last_expr {
    my($self) = @_;
    my $lines = $self->lines->{$self->curline};
    return undef unless @$lines;
    # Find last line with a derivation (hence a theorem)
    for (my $i = $#$lines; $i >= 0; --$i) {
        return $lines->[$i]->expr if $lines->[$i]->is_derived;
    }
    return undef;
}
sub line {
    my($self, $name) = @_;
    my $lines = $self->lines;
    my $named = $self->named;
    return $named->{$name} if $named->{$name};
    $name =~ /^\d+(\.\d+)*$/
            or die "Unknown theorem name '$name'\n";
    my @parts = split /\./, $name;
    my $where = join '.', @parts[0 .. $#parts - 1];
    my $wlines = $lines->{$where}
            or die "Unknown prefix '$where' for $name\n";
    my $line = $wlines->[$parts[-1]]
            or die "Unknown line $name\n";
    return $line;
}
sub expr {
    my($self, $index) = @_;
    my $line = $self->line($index);
    $line->is_derived
            or die "Line $index is not a theorem\n";
    return $line->expr;
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
    my $where = $derive->scope;
    if ($where > 0) {
        $self->enter_scope($derive);
    } elsif ($where < 0) {
        $self->leave_scope($derive);
    } else {
        $self->add_line($derive);
    }
    for my $name (@{ $derive->working_name }) {
        warn "Replacing name '$name'\n" if defined $self->named->{$name};
        $self->named->{$name} = $derive;
        push @{ $self->onamed }, $name;
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
        printf "%s: %s\n", $this, $these->[$_]->rawexpr;
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
        my $derive = $self->line($name)
                // die "No line to diagnose for '$name'\n";
        {
            use Data::Dumper;
            local $derive->{context};
            print Dumper($derive);
        }
        print $derive->rawexpr, "\n";
        print $derive->expr->str, "\n";
        return;
    } elsif ($line =~ bindre()) {
        my $type = $/{Type};
        my @names = map $_->name, @{ $/{Name}{Name} };
        my $dict = $self->dict->copy;
        $dict->insert($_, $type) for @names;
        $self->{dict} = $dict;    # if successful for all names
        $self->add_line(Axiom::Context::Directive->new($line));
    } elsif ($line eq '*terse') {
        my $lines = $self->lines;
        my $named = $self->named;
        my $onamed = $self->onamed;
        for my $name (@$onamed) {
            my $line = $self->line($name);
            printf "%s: %s\n", $name, $line->rawexpr;
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
        my $file = filename($1);
        open(my $f, '>', $file) or die "$file: $!\n";
        $quiet or print $f $_->rawexpr, "\n" for @{ $self->{lines} };
        close $f;
    } elsif ($line =~ /^\*load\s*(\S.+)\z/) {
        my $file = filename($1);
        open(my $f, '<', $file) or die "$file: $!\n";
        while (<$f>) {
            chomp;
            eval { $self->add($_) };
            warn($@), return if $@;
        }
        close $f;
        $self->apply_directive('*list') unless $quiet;
        return;
    } elsif ($line =~ /^\*import\s*(\S.+)\z/) {
        my $file = $1;
        my $named = $self->named;
        my $onamed = $self->onamed;

        my $sub = $self->subsidiary;
        $sub->apply_directive("*load $file", 1);
        for my $subname (@{ $sub->onamed }) {
            my $derive = $sub->line($subname);
            my $name = "$file.$subname";
            $named->{$name} = $derive;
            push @$onamed, $name;
        }
        $self->add_line(Axiom::Context::Directive->new($line));
    } else {
        die "Unknown directive: <$line>\n";
    }
    print $line, "\n" unless $quiet;
}

sub filename {
    my($file) = @_;
    $file .= '.aa' unless $file =~ /\.aa\z/;
    return $file;
}

package Axiom::Context::Directive {
    sub new {
        my($class, $raw) = @_;
        return bless { rawexpr => $raw }, $class;
    }
    sub is_derived { 0 }
    sub rawexpr { shift->{rawexpr} }
};

1;
