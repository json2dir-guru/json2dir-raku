#!/usr/bin/env raku
# json2dir: create the directory tree a JSON document describes, in the current directory.
# Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
# Core Raku only: a grammar for JSON, IO::Path for the file system.

class X::J2D is Exception {
    has $.message;
}
sub fail-j2d($message) { X::J2D.new(:$message).throw }

# A JSON scalar json2dir does not accept (number, true, false, null).
class Bad { has $.kind }

# §3: strict UTF-8, checked byte by byte (no overlongs, no surrogates, nothing above U+10FFFF).
sub check-utf8(Blob $b) {
    my $i = 0;
    my $n = $b.elems;
    while $i < $n {
        my $c = $b[$i];
        if $c < 0x80 { $i++; next }
        my $len;
        my $lo = 0x80;
        my $hi = 0xBF;
        if    0xC2 <= $c <= 0xDF { $len = 2 }
        elsif $c == 0xE0         { $len = 3; $lo = 0xA0 }
        elsif 0xE1 <= $c <= 0xEC { $len = 3 }
        elsif $c == 0xED         { $len = 3; $hi = 0x9F }
        elsif 0xEE <= $c <= 0xEF { $len = 3 }
        elsif $c == 0xF0         { $len = 4; $lo = 0x90 }
        elsif 0xF1 <= $c <= 0xF3 { $len = 4 }
        elsif $c == 0xF4         { $len = 4; $hi = 0x8F }
        else                     { fail-j2d("input is not valid UTF-8") }
        fail-j2d("input is not valid UTF-8") if $i + $len > $n;
        my $c1 = $b[$i + 1];
        fail-j2d("input is not valid UTF-8") unless $lo <= $c1 <= $hi;
        loop (my $k = 2; $k < $len; $k++) {
            fail-j2d("input is not valid UTF-8") unless 0x80 <= $b[$i + $k] <= 0xBF;
        }
        $i += $len;
    }
}

grammar JSON {
    token TOP     { <.ws> <value> <.ws> }
    token ws      { [ <[\x20\x09\x0A\x0D]> | "\r\n" ]* }
    token value   { <object> | <array> | <string> | <number> | <true> | <false> | <null> }
    token true    { 'true' }
    token false   { 'false' }
    token null    { 'null' }
    token object  { '{' <.ws> [ <pair> [ <.ws> ',' <.ws> <pair> ]* ]? <.ws> '}' }
    token pair    { <string> <.ws> ':' <.ws> <value> }
    token array   { '[' <.ws> [ <value> [ <.ws> ',' <.ws> <value> ]* ]? <.ws> ']' }
    token string  { '"' <part>* '"' }
    token part    { <plain> | \\ <esc> }
    token plain   { <-["\\\x[00]..\x[1F]]>+ }
    token esc     { <["\\/bfnrt]> | 'u' $<hex>=[<[0..9a..fA..F]> ** 4] }
    token number  { '-'? [ '0' | <[1..9]> <[0..9]>* ] [ '.' <[0..9]>+ ]? [ <[eE]> <[+-]>? <[0..9]>+ ]? }
}

class JSON-Actions {
    method TOP($/)    { make $<value>.made }
    method value($/)  { make ($<object> // $<array> // $<string> // $<number> // $<true> // $<false> // $<null>).made }
    method true($/)   { make Bad.new(:kind<true>) }
    method false($/)  { make Bad.new(:kind<false>) }
    method null($/)   { make Bad.new(:kind<null>) }
    method number($/) { make Bad.new(:kind<number>) }
    method object($/) {
        my %h;
        %h{.<string>.made} = .<value>.made for $<pair>.list;
        make %h;
    }
    method array($/)  { make [ $<value>.map(*.made) ] }
    method string($/) {
        my @out;
        my $pending;   # a high surrogate waiting for its low half
        for $<part>.list -> $p {
            if $p<plain> {
                fail-j2d("string contains an unpaired surrogate") if $pending.defined;
                @out.push: ~$p<plain>;
                next;
            }
            my $e = $p<esc>;
            if $e<hex> {
                my $cp = :16(~$e<hex>);
                if 0xD800 <= $cp <= 0xDBFF {
                    fail-j2d("string contains an unpaired surrogate") if $pending.defined;
                    $pending = $cp;
                } elsif 0xDC00 <= $cp <= 0xDFFF {
                    fail-j2d("string contains an unpaired surrogate") unless $pending.defined;
                    @out.push: chr(0x10000 + ($pending - 0xD800) * 0x400 + ($cp - 0xDC00));
                    $pending = Nil;
                } else {
                    fail-j2d("string contains an unpaired surrogate") if $pending.defined;
                    @out.push: chr($cp);
                }
            } else {
                fail-j2d("string contains an unpaired surrogate") if $pending.defined;
                @out.push: %( '"' => '"', '\\' => '\\', '/' => '/', b => "\b",
                              f => "\f", n => "\n", r => "\r", t => "\t" ){~$e};
            }
        }
        fail-j2d("string contains an unpaired surrogate") if $pending.defined;
        make @out.join;
    }
}

sub check-name($name, $where) {
    fail-j2d("$where: invalid name {$name.raku}")
        if $name eq '' || $name eq '.' || $name eq '..' || $name.contains('/') || $name.contains("\0");
}

# §4, §6: validate the whole document before touching the file system.
sub validate($value, $where) {
    given $value {
        when Str { return }
        when Bad { fail-j2d("$where: {$value.kind} values are not allowed") }
        when Array {
            fail-j2d("$where: an array must be [\"link\", target] or [\"script\", content]")
                unless $value.elems == 2 && $value[0] ~~ Str && $value[1] ~~ Str;
            fail-j2d("$where: unknown array kind {$value[0].raku}")
                unless $value[0] eq 'link' | 'script';
            fail-j2d("$where: a link target cannot contain NUL")
                if $value[0] eq 'link' && $value[1].contains("\0");
        }
        when Hash {
            for $value.keys -> $name {
                my $child = $where eq '.' ?? $name !! "$where/$name";
                check-name($name, $child);
                validate($value{$name}, $child);
            }
        }
    }
}

# §5.2, §5.3: remove an existing non-directory (a symlink itself, never its target);
# §5.4: a directory in the way of a non-object is an error.
sub clear(IO::Path $p) {
    if $p.l { $p.unlink; return }
    fail-j2d("$p: a directory is in the way") if $p.d;
    $p.unlink if $p.e;
}

sub write-file(IO::Path $p, Str $content, Bool $executable) {
    # :x = O_CREAT | O_EXCL, so we never write through an entry that appeared after clear().
    my $fh = $p.open(:x, :bin);
    $fh.write($content.encode('utf8-c8'));
    $fh.close;
    $p.chmod($p.mode +| 0o111) if $executable;
}

sub apply(Str $dir, %tree) {
    for %tree.keys.sort -> $name {
        my $p = "$dir/$name".IO;
        my $value = %tree{$name};
        if $value ~~ Str {
            clear($p);
            write-file($p, $value, False);
        } elsif $value ~~ Array {
            clear($p);
            if $value[0] eq 'link' {
                $value[1].IO.symlink($p, :!absolute) or fail-j2d("$p: cannot create symlink");
            } else {
                write-file($p, $value[1], True);
            }
        } else {
            if $p.l || ($p.e && !$p.d) {
                $p.unlink;
            }
            $p.mkdir unless $p.d;
            apply("$dir/$name", $value);
        }
    }
}

sub MAIN-impl(@args) {
    if @args {
        note "usage: json2dir < document.json";
        return 2;
    }
    my Blob $bytes = $*IN.slurp(:bin);
    check-utf8($bytes);
    # utf8-c8 keeps the exact code points (no NFC normalization), as §4.2.1 requires.
    my $text = $bytes.decode('utf8-c8');
    $text .= substr(1) if $text.starts-with("\x[FEFF]");
    my $m = JSON.parse($text, :actions(JSON-Actions)) or fail-j2d("input is not valid JSON");
    my $doc = $m.made;
    fail-j2d("the root of the document must be an object") unless $doc ~~ Hash;
    validate($doc, '.');
    apply('.', $doc);
    return 0;
    CATCH {
        default { note "json2dir: {.message}"; return 1 }
    }
}

exit MAIN-impl(@*ARGS);
