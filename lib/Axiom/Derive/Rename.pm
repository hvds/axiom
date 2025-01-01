package Axiom::Derive::Rename;

use v5.10;
use strict;
use warnings;

use parent qw{ Axiom::Derive };
use Axiom::Expr;

=head1 NAME

Axiom::Derive::Rename - rename variables in a theorem

=head1 USAGE

  derive: rename ( line? )
  rule: [ line, [oldvar, newvar ]+ ]

Given a prior theorem of the form C< P(x) >, constructs the new theorem
C< P(y) >.

=cut

sub rulename { 'rename' }

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
    my $from = $self->line($line);
    my $to = $self->expr;
    $to->resolve($self->dict);
    my $fs = $from->str;
    my $ts = $to->str;
    return $self->set_error(sprintf(
        'Cannot derive %s from %s', $ts, $fs
    )) unless length($fs) == length($ts);
    my $diff = $fs ^ $ts;
    my(%fmap, %tmap);
    while ($diff =~ /[^\x{0}]/g) {
        my $pos = $-[0];
        my($fc, $tc) = map substr($_, $pos, 1), ($fs, $ts);
        return $self->set_error(sprintf(
            "String mismatch: '%s' in '%s' vs. '%s' in '%s'",
            $fc, $fs, $tc, $ts
        )) unless "$fc$tc" =~ /^\w{2}$/;
        if ($fmap{$fc}) {
            return $self->set_error(sprintf(
                "Cannot map '%s' to both '%s' and '%s'",
                $fc, $fmap{$fc}, $tc
            )) unless $fmap{$fc} eq $tc;
        } else {
            return $self->set_error(sprintf(
                "Cannot map both '%s' and '%s' to '%s'",
                $tmap{$tc}, $fc, $tc
            )) if $tmap{$tc};
            $fmap{$fc} = $tc;
            $tmap{$tc} = $fc;
        }
    }
    return $self->validate([ $line, \%fmap ]);
}

sub validate {
    my($self, $args) = @_;
    my($line, $map) = @$args;
    my $result = $self->line($line);
    $self->validate_diff($result, -1) or return;
    $self->rule(sprintf 'rename(%s, {%s})', $self->_linename($line),
        join ', ', map "$_ => $map->{$_}", sort keys %$map
    );
    return 1;
}

1;
