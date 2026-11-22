#!/usr/bin/env python3
"""Make a lemma's explicit binders implicit, then drop those positional
arguments at every use of the lemma.

  tools/fmt/dev/implicit.py [--dry-run] [--force | --name-real]
                            LEMMA BINDER [BINDER ...]
  tools/fmt/dev/implicit.py [--dry-run] [--force | --name-real] --from-file SPEC
  task fmt:implicit -- LEMMA BINDER [BINDER ...]

`SPEC` has one lemma per line, `Name: b1 b2` (blank lines and lines starting
with `#` or `--` are ignored).  The header binder groups `(x: T)` named on
the command line become `[x: T]`; a grouped binder `(a b: T)` is split when
only some of its names are named.  A binder already written `[x: T]` is left
alone, and its argument is not dropped (it is already implicit).

`LEMMA` may be bare (`hangsCons`) or namespace-qualified
(`Fmt.HangProofs.hangsCons`).  A qualified name is checked against the file's
`namespace` declaration (and the declaration's own dotted prefix), so a name
from a different namespace is refused with the namespace where the lemma is
declared instead of being edited.

At every use, arguments are read bracket-aware, so record literals,
parentheses spanning lines, lists, and string/character literals count as
one argument.  Only positional arguments are dropped: named arguments
(`[x := ...]` and `(x := ...)`) are kept, and an explicit named `(x := ...)`
for a binder made implicit is changed to `[x := ...]`.  A use whose target
arguments cannot all be identified is skipped and reported rather than
edited, so arguments are never deleted from the wrong positions.

An argument in a slot that becomes implicit must be the placeholder `_`.
Anything else is a real term that would be silently lost, so it is
reported as

  REAL <file>:<line>: <lemma> slot <binder>: <argument text, first 60 chars>

and the whole run is refused before any file is written.  `--force` drops
such arguments anyway.  `--name-real` instead rewrites each one in place
as `[binder := <argument>]`, keeping the argument's text; this is what a
person does by hand today.  A multi-line argument keeps its layout.

The default roots are tools/fmt/src, crates/elab/src/std,
aoc/src, games/rogue/src and examples.  Files are deduplicated by real path
(some trees contain symlinks).  With --dry-run a
unified diff is printed and nothing is written.

Each file is read completely before any edit.  Writes go to a temporary
file in the same directory and are renamed over the original, so an
interrupted run cannot leave a truncated file.
"""
import difflib
import os
import re
import sys
import tempfile
from collections import namedtuple

DEFAULT_ROOTS = [
    "tools/fmt/src",
    "crates/elab/src/std",
    "aoc/src",
    "games/rogue/src",
    "examples",
]

DECL_KEYWORDS = {"theorem", "def", "lemma", "fn"}
STOP_KEYWORDS = {
    "then", "in", "else", "with", "if", "match", "let", "rewrite", "at",
    "by", "calc", "from", "have", "show", "where", "end", "do", "return",
}
Token = namedtuple("Token", "kind text start end")
Arg = namedtuple("Arg", "start end next")


# ---------------------------------------------------------------- lexing

def scan_char(text, i):
    """End of a character literal starting at i."""
    n = len(text)
    j = i + 1
    while j < n:
        if text[j] == "\\":
            j += 2
        elif text[j] == "'":
            return j + 1
        elif text[j] in "\r\n":
            return j
        else:
            j += 1
    return n


def scan_interp(text, j):
    """End of a ${...} interpolation whose body starts at j."""
    n = len(text)
    depth = 1
    while j < n and depth:
        c = text[j]
        if c == '"':
            j = scan_string(text, j)
        elif c == "'":
            j = scan_char(text, j)
        elif text.startswith("--", j):
            k = text.find("\n", j)
            j = n if k < 0 else k
        elif c == "{":
            depth += 1
            j += 1
        elif c == "}":
            depth -= 1
            j += 1
        else:
            j += 1
    return j


def scan_string(text, i):
    """End of a string or text-block literal starting at i."""
    n = len(text)
    if text.startswith('"""', i):
        j = i + 3
        while j < n:
            if text[j] == "\\":
                j += 2
            elif text.startswith('"""', j):
                return j + 3
            elif text.startswith("${", j):
                j = scan_interp(text, j + 2)
            else:
                j += 1
        return n
    j = i + 1
    while j < n:
        c = text[j]
        if c == "\\":
            j += 2
        elif c == '"':
            return j + 1
        elif text.startswith("${", j):
            j = scan_interp(text, j + 2)
        else:
            j += 1
    return n


def tokenize(text):
    """Tokens with source offsets. Comments and literals are single tokens."""
    tokens = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            tokens.append(Token("comment", text[i:j], i, j))
            i = j
            continue
        if c == '"':
            j = scan_string(text, i)
            tokens.append(Token("string", text[i:j], i, j))
            i = j
            continue
        if c == "'":
            j = scan_char(text, i)
            tokens.append(Token("char", text[i:j], i, j))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i + 1
            while j < n:
                ch = text[j]
                if ch.isalnum() or ch in "_'?!":
                    j += 1
                elif (ch == "." and j + 1 < n
                      and (text[j + 1].isalnum() or text[j + 1] in "_'")):
                    j += 1
                else:
                    break
            tokens.append(Token("ident", text[i:j], i, j))
            i = j
            continue
        if c.isdigit():
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] in "._'"):
                j += 1
            tokens.append(Token("number", text[i:j], i, j))
            i = j
            continue
        op = None
        for candidate in ("=>", "->", ":=", "==", "!=", "<=", ">=",
                          "&&", "||", "++", "::"):
            if text.startswith(candidate, i):
                op = candidate
                break
        if op is None:
            op = c
        j = i + len(op)
        tokens.append(Token("punct", op, i, j))
        i = j
    return tokens


def bracket_map(tokens):
    """Map an opening bracket token index to its closing one, and back."""
    pairs = {")": "(", "]": "[", "}": "{"}
    stack, out = [], {}
    for i, t in enumerate(tokens):
        if t.kind != "punct":
            continue
        if t.text in "([{":
            stack.append(i)
        elif t.text in ")]}":
            if stack and tokens[stack[-1]].text == pairs[t.text]:
                j = stack.pop()
                out[i] = j
                out[j] = i
    return out


# --------------------------------------------------------------- headers

def find_declaration_tokens(tokens, text, name):
    """Indices of the name token in declarations of `name`."""
    found = []
    for i, t in enumerate(tokens):
        if t.kind != "ident" or t.text != name:
            continue
        j = i - 1
        while j >= 0 and tokens[j].kind == "comment":
            j -= 1
        if (j >= 0 and tokens[j].kind == "ident"
                and tokens[j].text in DECL_KEYWORDS
                and not text[tokens[j].end:t.start].strip()):
            found.append(i)
    return found


def parse_header_groups(text, tokens, bmap, name_idx):
    """Binder groups after a declaration name, with their name lists."""
    i = name_idx + 1
    if i < len(tokens) and tokens[i].text == "∀":
        i += 1
    groups = []
    while i < len(tokens) and tokens[i].kind == "punct" and tokens[i].text in "([":
        close = bmap.get(i)
        if close is None:
            break
        open_t, close_t = tokens[i], tokens[close]
        colon_idx = None
        depth = 0
        for k in range(i + 1, close):
            tk = tokens[k]
            if tk.kind == "punct" and tk.text in "([{":
                depth += 1
            elif tk.kind == "punct" and tk.text in ")]}":
                depth -= 1
            elif depth == 0 and tk.kind == "punct" and tk.text == ":":
                colon_idx = k
                break
        if colon_idx is None:
            raise SystemExit(
                "implicit.py: cannot find ':' in binder group %r"
                % text[open_t.start:close_t.end])
        names_text = text[open_t.end:tokens[colon_idx].start]
        names = names_text.replace("\n", " ").split()
        if names and names[0] == "auto":
            names = names[1:]
        groups.append({
            "start": open_t.start,
            "end": close_t.end,
            "delim": open_t.text,
            "names": names,
            "colon_end": tokens[colon_idx].end,
        })
        i = close + 1
    if not groups and i < len(tokens) and tokens[i].text != ":":
        # A declaration without binders still has a result-type colon.
        pass
    return groups


def header_new_text(text, group, selected):
    """The replacement text for one explicit binder group, or None."""
    names = group["names"]
    chosen = [n for n in names if n in selected]
    if not chosen or group["delim"] != "(":
        return None
    if len(chosen) == len(names):
        return "[" + text[group["start"] + 1:group["end"] - 1] + "]"
    type_text = text[group["colon_end"]:group["end"] - 1]
    runs = []
    for name in names:
        delim = "[" if name in selected else "("
        if runs and runs[-1][0] == delim:
            runs[-1][1].append(name)
        else:
            runs.append([delim, [name]])
    rendered = []
    for delim, run in runs:
        close = "]" if delim == "[" else ")"
        rendered.append("%s%s:%s%s" % (delim, " ".join(run), type_text, close))
    return " ".join(rendered)


def build_info(text, tokens, bmap, name, selected):
    """The header plan and the explicit-binder positions for one lemma."""
    decls = find_declaration_tokens(tokens, text, name)
    if not decls:
        return None
    if len(decls) > 1:
        raise SystemExit("implicit.py: %s is declared more than once" % name)
    name_idx = decls[0]
    groups = parse_header_groups(text, tokens, bmap, name_idx)

    explicit = []
    explicit_group_indices = []
    implicit_names = set()
    for gi, group in enumerate(groups):
        indices = []
        if group["delim"] == "(":
            for n in group["names"]:
                indices.append(len(explicit))
                explicit.append(n)
        else:
            implicit_names.update(group["names"])
        explicit_group_indices.append(indices)

    missing = [n for n in selected if n not in explicit and n not in implicit_names]
    if missing:
        available = ", ".join(explicit) or "(none)"
        raise SystemExit(
            "implicit.py: %s has no binder %s; explicit binders: %s"
            % (name, ", ".join(missing), available))

    newly = [n for n in selected if n in explicit]
    drop_indices = {i for i, n in enumerate(explicit) if n in newly}
    edits = []
    for gi, group in enumerate(groups):
        if group["delim"] != "(":
            continue
        chosen = {n for n in group["names"] if n in newly}
        if not chosen:
            continue
        new = header_new_text(text, group, chosen)
        if new is not None:
            edits.append((group["start"], group["end"], new))
    return {
        "name": name,
        "decl_token": name_idx,
        "groups": groups,
        "explicit": explicit,
        "drop_indices": drop_indices,
        "drop_names": set(newly),
        "edits": edits,
        "already": [n for n in selected if n in implicit_names],
        "found": [n for n in selected if n in explicit],
    }


# ------------------------------------------------------------------ uses

def line_start(text, pos):
    return text.rfind("\n", 0, pos) + 1


def line_indent(text, pos):
    ls = line_start(text, pos)
    prefix = text[ls:pos]
    return len(prefix) - len(prefix.lstrip(" \t"))


def parse_atom(text, tokens, bmap, i):
    """One argument: a bracket group, literal, name, or dotted/called term."""
    if i >= len(tokens):
        return None
    t = tokens[i]
    if t.kind == "comment":
        return None
    if t.kind == "punct" and t.text in "([{":
        close = bmap.get(i)
        if close is None:
            return None
        end, i = tokens[close].end, close + 1
        while i < len(tokens) and tokens[i].start == end:
            nt = tokens[i]
            if nt.kind == "punct" and nt.text in "([{":
                close = bmap.get(i)
                if close is None:
                    break
                end, i = tokens[close].end, close + 1
            elif (nt.kind == "punct" and nt.text == "."
                  and i + 1 < len(tokens)
                  and tokens[i + 1].start == nt.end
                  and tokens[i + 1].kind == "ident"):
                end, i = tokens[i + 1].end, i + 2
            else:
                break
        return Arg(t.start, end, i)
    if t.kind in ("ident", "number", "string", "char"):
        end, i = t.end, i + 1
        while i < len(tokens) and tokens[i].start == end:
            nt = tokens[i]
            if nt.kind == "punct" and nt.text in "([{":
                close = bmap.get(i)
                if close is None:
                    break
                end, i = tokens[close].end, close + 1
            elif (nt.kind == "punct" and nt.text == "."
                  and i + 1 < len(tokens)
                  and tokens[i + 1].start == nt.end
                  and tokens[i + 1].kind == "ident"):
                end, i = tokens[i + 1].end, i + 2
            else:
                break
        return Arg(t.start, end, i)
    if (t.kind == "punct" and t.text == "-"
            and i + 1 < len(tokens)
            and tokens[i + 1].kind == "number"
            and tokens[i + 1].start == t.end):
        return Arg(t.start, tokens[i + 1].end, i + 2)
    return None


def can_start_arg(text, tokens, i, prev_end, base_indent):
    t = tokens[i]
    if t.kind == "comment":
        return False
    gap = text[prev_end:t.start]
    if not gap:
        # `f(...)` is a call; for a lemma it is still its first argument.
        return t.kind == "punct" and t.text in "(["
    if "\n" in gap or "\r" in gap:
        if line_indent(text, t.start) <= base_indent:
            return False
    if t.kind == "ident":
        return t.text not in STOP_KEYWORDS
    if t.kind in ("number", "string", "char"):
        return True
    if t.kind == "punct":
        return t.text in "([{" or t.text == "-"
    return False


def named_arg(text, arg):
    """The name of a `(x := ...)` or `[x := ...]` argument, if it is one."""
    if text[arg.start] not in "([":
        return None
    inner = text[arg.start + 1:arg.end - 1]
    m = re.match(r"\s*([A-Za-z_][\w'?!]*)\s*:=", inner)
    return m.group(1) if m else None


def parse_application(text, tokens, bmap, start, prev_end, base_indent,
                      explicit):
    """Positional and named arguments up to the last explicit binder slot."""
    positional, named, filled = [], [], set()
    i = start
    while i < len(tokens) and len(filled) < len(explicit):
        if not can_start_arg(text, tokens, i, prev_end, base_indent):
            break
        arg = parse_atom(text, tokens, bmap, i)
        if arg is None:
            break
        name = named_arg(text, arg)
        if name is not None:
            named.append((name, arg))
            candidates = [k for k, n in enumerate(explicit)
                          if n == name and k not in filled]
            if candidates:
                filled.add(candidates[0])
            i, prev_end = arg.next, arg.end
            continue
        free = [k for k in range(len(explicit)) if k not in filled]
        if not free:
            break
        positional.append((free[0], arg.start, arg.end))
        filled.add(free[0])
        i, prev_end = arg.next, arg.end
    return positional, named, filled


def is_placeholder(text, start, end):
    """True when the argument is the lone wildcard `_`."""
    return text[start:end].strip() == "_"


def argument_snippet(argument):
    """The argument text on one line, for the REAL diagnostic."""
    return argument.replace("\r", " ").replace("\n", " ")[:60]


def removal_span(text, start, end):
    """Delete an argument plus the whitespace that introduced it."""
    s = start
    while s > 0 and text[s - 1] in " \t":
        s -= 1
    if s > 0 and text[s - 1] in "\r\n":
        if s > 1 and text[s - 2] == "\r" and text[s - 1] == "\n":
            s -= 2
        else:
            s -= 1
    return s, end


def normalize_edits(edits):
    """Drop edits inside a larger edit; error on a partial overlap."""
    edits = sorted(edits, key=lambda e: (e[0], -(e[1] - e[0])))
    out = []
    for e in edits:
        if out and e[0] >= out[-1][0] and e[1] <= out[-1][1]:
            continue
        if out and e[0] < out[-1][1]:
            raise SystemExit(
                "implicit.py: overlapping edits at %d..%d and %d..%d"
                % (out[-1][0], out[-1][1], e[0], e[1]))
        out.append(e)
    return out


def apply_edits(text, edits):
    for start, end, replacement in sorted(edits, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text


# ----------------------------------------------------------------- files

def iter_sw_files(root):
    """Every .sw file under root, by real path, without duplicates or loops."""
    if os.path.isfile(root):
        yield os.path.realpath(root)
        return
    if not os.path.isdir(root):
        return
    seen_dirs, seen_files = set(), set()
    for dirpath, dirnames, filenames in os.walk(root, followlinks=True):
        real_dir = os.path.realpath(dirpath)
        if real_dir in seen_dirs:
            dirnames[:] = []
            continue
        seen_dirs.add(real_dir)
        dirnames.sort()
        for name in sorted(filenames):
            if not name.endswith(".sw"):
                continue
            path = os.path.realpath(os.path.join(dirpath, name))
            if path in seen_files or not os.path.isfile(path):
                continue
            seen_files.add(path)
            yield path


def read_text(path):
    with open(path, "r", encoding="utf-8", newline="") as handle:
        return handle.read()


def write_atomic(path, text):
    directory = os.path.dirname(os.path.abspath(path))
    mode = os.stat(path).st_mode
    fd, tmp = tempfile.mkstemp(prefix="." + os.path.basename(path) + ".",
                               suffix=".tmp", dir=directory)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(tmp, mode)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


# --------------------------------------------------------------- names

def file_namespace(text, tokens):
    """The namespace the file declares, or None when it declares none."""
    for i, token in enumerate(tokens):
        if token.kind != "ident" or token.text != "namespace":
            continue
        start = text.rfind("\n", 0, token.start) + 1
        if text[start:token.start].strip():
            continue
        if i + 1 < len(tokens) and tokens[i + 1].kind == "ident":
            return tokens[i + 1].text
    return None


def qualified_name(namespace, decl_name):
    """A declaration's full name, given its file namespace and token text."""
    if not namespace:
        return decl_name
    if decl_name == namespace or decl_name.startswith(namespace + "."):
        return decl_name
    return namespace + "." + decl_name


def find_declarations(files, loaded, decl_name):
    """Every (path, token index) declaration of `decl_name` under the roots."""
    hits = []
    for path in files:
        text, tokens = loaded[path][0], loaded[path][1]
        for index in find_declaration_tokens(tokens, text, decl_name):
            hits.append((path, index))
    return hits


def resolve_declaration(given, files, loaded):
    """The declaration name to use, its hits, and a namespace-mismatch error.

    A bare name, or a name written exactly as the declaration token, is used
    as given.  Otherwise a qualified name is split at each dot and the suffix
    is tried, but only where the file's namespace makes the full name equal
    the one given.
    """
    hits = find_declarations(files, loaded, given)
    if hits or "." not in given:
        return given, hits, None
    parts = given.split(".")
    mismatches = []
    for k in range(1, len(parts)):
        namespace = ".".join(parts[:k])
        rest = ".".join(parts[k:])
        rest_hits = find_declarations(files, loaded, rest)
        if not rest_hits:
            continue
        exact = []
        for path, index in rest_hits:
            actual = qualified_name(loaded[path][3], rest)
            if actual == given:
                exact.append((path, index))
            else:
                mismatches.append((namespace, actual, rest, path))
        if exact:
            return rest, exact, None
    if mismatches:
        namespace, actual, rest, path = mismatches[0]
        return None, [], (
            "implicit.py: %s: namespace %s does not match %s, where %s "
            "is declared (%s)"
            % (given, namespace, actual, rest, path))
    return given, [], None


# ------------------------------------------------------------------- cli

def parse_specs(args):
    if args.from_file:
        specs = []
        with open(args.from_file, "r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line or line.startswith("#") or line.startswith("--"):
                    continue
                if ":" not in line:
                    raise SystemExit(
                        "implicit.py: %s: expected 'Name: b1 b2'" % line)
                name, binders = line.split(":", 1)
                specs.append((name.strip(), binders.split()))
        if not specs:
            raise SystemExit("implicit.py: %s has no specs" % args.from_file)
        return specs
    if not args.lemma:
        raise SystemExit(__doc__)
    return [(args.lemma, args.binders)]


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    dry = False
    force = False
    name_real = False
    from_file = None
    roots = []
    positional = []
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg in ("--dry-run", "--dry"):
            dry = True
        elif arg == "--force":
            force = True
        elif arg == "--name-real":
            name_real = True
        elif arg == "--from-file":
            i += 1
            if i >= len(argv):
                raise SystemExit("implicit.py: --from-file needs a path")
            from_file = argv[i]
        elif arg in ("--roots", "--root"):
            i += 1
            if i >= len(argv):
                raise SystemExit("implicit.py: %s needs a path" % arg)
            roots.extend(a for a in argv[i].split(",") if a)
        elif arg in ("-h", "--help"):
            print(__doc__)
            return 0
        elif arg.startswith("-"):
            raise SystemExit("implicit.py: unknown option %s" % arg)
        else:
            positional.append(arg)
        i += 1

    class Args:
        pass

    args = Args()
    args.from_file = from_file
    args.lemma = positional[0] if positional else None
    args.binders = positional[1:]
    if from_file and positional:
        raise SystemExit("implicit.py: give --from-file or a lemma, not both")
    specs = parse_specs(args)
    if not roots:
        roots = DEFAULT_ROOTS
    roots = [os.path.abspath(r) for r in roots]

    files = sorted({p for root in roots for p in iter_sw_files(root)})
    for given in roots:
        if not os.path.exists(given):
            print("implicit.py: skipping missing root %s" % given,
                  file=sys.stderr)
    if not files:
        raise SystemExit("implicit.py: no .sw files under the roots")

    loaded = {}
    for path in files:
        text = read_text(path)
        tokens = tokenize(text)
        loaded[path] = [text, tokens, bracket_map(tokens),
                        file_namespace(text, tokens)]

    infos = {}
    edits = {path: [] for path in files}
    for name, binders in specs:
        decl_name, hits, namespace_error = resolve_declaration(
            name, files, loaded)
        if namespace_error:
            raise SystemExit(namespace_error)
        if not hits:
            raise SystemExit("implicit.py: no declaration of %s under the roots"
                             % name)
        paths = sorted({path for path, _ in hits})
        if len(paths) > 1:
            raise SystemExit(
                "implicit.py: %s is declared in both %s and %s"
                % (decl_name, paths[0], paths[1]))
        decl_path = paths[0]
        text, tokens, bmap = loaded[decl_path][:3]
        info = build_info(text, tokens, bmap, decl_name, binders)
        if info is None:
            raise SystemExit("implicit.py: no declaration of %s under the roots"
                             % name)
        if not info["found"]:
            print("implicit.py: %s: already implicit: %s"
                  % (decl_name, ", ".join(info["already"])), file=sys.stderr)
        elif info["already"]:
            print("implicit.py: %s: already implicit: %s"
                  % (decl_name, ", ".join(info["already"])), file=sys.stderr)
        info["decl_path"] = decl_path
        infos[decl_name] = info
        edits[decl_path].extend(info["edits"])

    uses = dropped = skipped = 0
    real = []
    for path in files:
        text, tokens, bmap = loaded[path][:3]
        for name, info in infos.items():
            if not info["drop_indices"]:
                continue
            for i, tok in enumerate(tokens):
                if tok.kind != "ident" or tok.text != name:
                    continue
                if path == info["decl_path"] and i == info["decl_token"]:
                    continue
                base = line_indent(text, tok.start)
                line = text.count("\n", 0, tok.start) + 1
                positional, named, filled = parse_application(
                    text, tokens, bmap, i + 1, tok.end, base,
                    info["explicit"])
                needed = info["drop_indices"]
                if not needed.issubset(filled):
                    missing = sorted(needed - filled)
                    skipped += 1
                    print(
                        "implicit.py: SKIP %s:%d %s: cannot identify "
                        "argument(s) for %s"
                        % (path, line, name,
                           ", ".join(info["explicit"][k] for k in missing)),
                        file=sys.stderr)
                    continue
                uses += 1
                for index, start, end in positional:
                    if index not in needed:
                        continue
                    binder = info["explicit"][index]
                    argument = text[start:end]
                    if not is_placeholder(text, start, end):
                        real.append((path, line, name, binder, argument))
                        if name_real:
                            edits[path].append((
                                start, end,
                                "[%s := %s]" % (binder, argument)))
                        elif force:
                            s, e = removal_span(text, start, end)
                            edits[path].append((s, e, ""))
                            dropped += 1
                        continue
                    s, e = removal_span(text, start, end)
                    edits[path].append((s, e, ""))
                    dropped += 1
                for arg_name, arg in named:
                    if arg_name in info["drop_names"] and text[arg.start] == "(":
                        edits[path].append((arg.start, arg.start + 1, "["))
                        edits[path].append((arg.end - 1, arg.end, "]"))

    for path, line, name, binder, argument in real:
        print("REAL %s:%d: %s slot %s: %s"
              % (path, line, name, binder, argument_snippet(argument)),
              file=sys.stderr)
    if real and not (force or name_real):
        print(
            "implicit.py: refusing to drop %d real argument(s); use "
            "--force to drop them or --name-real to name them"
            % len(real),
            file=sys.stderr)
        return 1

    changed = 0
    for path in files:
        if not edits[path]:
            continue
        old = loaded[path][0]
        new = apply_edits(old, normalize_edits(edits[path]))
        if old == new:
            continue
        changed += 1
        if dry:
            sys.stdout.writelines(difflib.unified_diff(
                old.splitlines(keepends=True),
                new.splitlines(keepends=True),
                fromfile=path, tofile=path))
        else:
            write_atomic(path, new)
    print(
        "implicit.py: %d use(s), %d argument(s) dropped, %d file(s) %s, "
        "%d skipped"
        % (uses, dropped, changed, "would change" if dry else "changed",
           skipped),
        file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
