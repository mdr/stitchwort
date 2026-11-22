# The slice 1 counterexample search

SW-3955's search for files the self-hosted formatter gets wrong
(docs/proposals/self-hosted-fmt-s1-sketch.md, section 3), kept so that
later lanes can rerun it. The files it generates are written at run time
to a folder you name, outside the repo; none are committed.

## The twin

The scripts call the twin, `Fmt.Twin.main`, as a command taking `--stage
NAME --batch LIST`. The native build peaks over 2 GB, so run it
interpreted, from a copy of `tools/fmt` without the proof files and tests
(they make `stitchwort run` check far more than the twin needs):

```sh
SLIM=/path/to/scratch/slim
mkdir -p $SLIM/src/Fmt $SLIM/src/Syntax
cp tools/fmt/stitchwort.yaml $SLIM/
cp tools/fmt/src/Syntax/*.sw $SLIM/src/Syntax/
rm $SLIM/src/Syntax/LexProofs.sw
for f in Blank Meaning Passes Rules Spacing Slice1 Slice2 Slice3 Slice4a Slice5a Slice4b Slice4c DocDump Twin; do
  cp tools/fmt/src/Fmt/$f.sw $SLIM/src/Fmt/
done
cp target/release/stitchwort /path/to/scratch/stitchwort
printf '#!/bin/sh\nSTITCHWORT_STD_DIR=%s exec nice -n 15 %s run --project %s Fmt.Twin.main -- "$@"\n' \
  "$PWD/crates/elab/src/std" /path/to/scratch/stitchwort "$SLIM" > /path/to/scratch/twin
chmod +x /path/to/scratch/twin
```

A copied binary doesn't find std beside it, hence `STITCHWORT_STD_DIR`.
Copy the binary so a rebuild in the worktree doesn't change it mid-run,
and use a fresh `FMT_TWIN_CACHE` for a gate: the harness's cache is keyed
on the sources, not the binary.

Copy the slim folder again after changing the formatter. Each batch
starts by checking the project (about 25 s), then takes 850 MB to 1.5 GB.

## The scripts

| Script | Arguments | What it does |
|---|---|---|
| `probe.py` | `--twin TWIN --out OUT --seed N --count N` (`--bin STITCHWORT`, `--rust N`, `--sketch`) | Generates the files into OUT, formats them with the twin (`OUT/x*.out.sw`), and counts the files that fail each check: idempotence, the tidied tree, comments in order, long lines, and with `--rust N` Rust's output for the first N |
| `hangs.py` | `OUT …` | Checks K3a (section 1.4, in its final form `Fmt.hangs`, SW-3969) on the outputs in Python: where each line starts against the block column in force. Family A shows here as `closer-at-block`. `twin --stage hangs --batch LIST` evaluates `Fmt.hangs` itself on the same outputs, a line a declaration |
| `classify.py` | `OUT` (`--bin STITCHWORT`) | Sorts the outputs that differ from `stitchwort fmt -` on the same input: glued pairs (section 3.5), layout, other |
| `sketchall.py` | `--twin TWIN OUT …` | Runs the twin's `sketch` stage over the outputs |
| `implicit.py` | `[--dry-run] [--force \| --name-real] [--roots DIRS] LEMMA BINDER …`, or `--from-file SPEC` | Makes the lemma's named explicit binders implicit and drops those positional arguments at every use (see below) |
| `spellings.py` | `[--sw PATH] [--names a,b,… or all] [--no-prune] [--list] FILE.sw` | Deletes the spelled named arguments a proof step does not need, keeping those the namespace still checks (see below) |

`--sketch` and `sketchall.py` need SW-3955's stages `words`, `calmwords`
and `sketch` (the predicates of section 1, in a file `S1Sketch.sw`), which
were written in its scratch copy and are not in the repo's twin; without
them the repo's twin echoes the input for an unknown stage. `hangs.py`
checks the same line rule with any twin.

The generator makes slice 1 files only (`def name: T := e`, no binders,
blocks or `if`). About 60% of the files fall within slice 1 and parse.

```sh
tools/fmt/dev/probe.py --twin /path/to/scratch/twin --out /path/to/scratch/search --seed 9 --count 1500
tools/fmt/dev/hangs.py /path/to/scratch/search
tools/fmt/dev/classify.py /path/to/scratch/search
```

## Making binders implicit

`implicit.py` is the one-step version of "make these lemma binders implicit
and drop the matching arguments at every use":

```sh
python3 tools/fmt/dev/implicit.py --dry-run Parse.readsDone x
python3 tools/fmt/dev/implicit.py Parse.readsDone x
python3 tools/fmt/dev/implicit.py --name-real Parse.readsDone x
task fmt:implicit -- --dry-run Parse.readsDone x
```

It edits the lemma header, turning `(x: T)` into `[x: T]`; a grouped
binder `(a b: T)` is split when only some of its names are named, and a
binder that is already `[x: T]` is left alone (its argument is already
gone, so it is not counted as a positional slot). It then walks the default
roots `tools/fmt/src`, `crates/elab/src/std`,
`aoc/src`, `games/rogue/src` and `examples` (or the directories after
`--roots`, comma-separated or repeated), deduplicating files by real path
because those trees contain symlinks.

At each use it reads arguments bracket-aware, so record literals,
parentheses spanning lines, lists, text blocks and string or character
literals are single arguments. It drops only the positional arguments in
the selected slots and keeps named arguments such as `[inv := …]`; an
explicit named `(x := …)` for a binder made implicit is changed to
`[x := …]`. If a use does not have enough arguments to identify every
selected slot, it prints `SKIP` with the file and line and leaves that use
alone rather than risking a wrong deletion.

An argument in a selected slot must be the placeholder `_`: dropping a
real term would silently lose it. If any real term is found the run prints

```
REAL <file>:<line>: <lemma> slot <binder>: <argument text, first 60 chars>
```

for each one and refuses the whole run, exiting non-zero before writing
any file, so nothing is half-applied. `--force` drops such arguments
anyway. `--name-real` instead rewrites each real argument in place as
`[binder := <argument>]`, keeping the argument's text (including a
multi-line parenthesised argument's layout), which is what a person does
by hand today. `--name-real` wins if both flags are given.

`--dry-run` prints a unified diff and writes nothing. Otherwise each file
is read completely before it is edited, and the new text goes to a
temporary file in the same directory that is renamed over the original,
so an interrupted run cannot leave a truncated file.

`--from-file SPEC` does several lemmas at once, one `Name: b1 b2` per line
(blank lines and lines starting with `#` or `--` are ignored).

A lemma may be named bare (`hangsCons`) or namespace-qualified
(`Fmt.HangProofs.hangsCons`). The qualified form is checked against the
namespace the lemma is declared in, and a name from another namespace is
refused rather than edited. Both forms make the same edits:

```sh
python3 tools/fmt/dev/implicit.py --dry-run --force hangsCons docs
python3 tools/fmt/dev/implicit.py --dry-run --force Fmt.HangProofs.hangsCons docs
```

## Deleting unneeded spelled arguments

`spellings.py` (also `task fmt:unspell -- FILE.sw`) deletes the spelled
named arguments (`[p := …]`, `[alike := …]`, …) a proof step does not need
and keeps the ones it does. A *unit* is a run of spelled groups with only
whitespace between them, such as the `[p := …]` / `[j := …]` lines under a
`givesThen`, or `[p := …] [q := …]` after `followsThen`.

The tool deletes every unit and checks the file's namespace. For each
error it puts back the nearest unit before the error (preferring the unit
whose head, the function it follows, is the one the error names), until
the namespace is clean. It then prunes the put-back units:

1. it tries each unit whole, one check per unit;
2. when the whole unit does not check, it tries each named argument in that
   unit on its own, keeping each drop that checks.

So a group no longer goes all or none: if `[q := …]` is needed and
`[p := …]` is not, only `p` is deleted. Trying the whole unit first keeps
the common case fast; the per-argument fallback costs one extra check for
each argument in a unit that cannot all go.

`--names a,b,…` limits the run to those spelled names. The default is
`p,q,j,k,alike,g2,spec,weaker,holds,inv,x,first,second,self,selfTwin,item,start,later,goals`;
`--names all` considers every name, including the type arguments `a` and
`b` of statements. Groups whose names are not selected are left untouched,
so the same result no longer needs separate `--names p,q` and `--names
j,k` runs.

`--list` only counts the groups per name and changes nothing, which is the
safe read-only way to see what a file offers. There is no full `--dry-run`:
the tool rewrites the file in place after each check and saves its progress
in `$TMPDIR/spellings/<file>.json`, so an interrupted run continues from
that state. `--no-prune` stops after the put-back step, keeping whole units
only. `--sw PATH` names the release CLI (default
`target/release/stitchwort` in the repo).

A namespace check takes 10 to 60 s and a file may need dozens, so run it in
the background, one file at a time, in dependency order. Format the file
afterwards with `task fmt:sw -- FILE.sw`.
