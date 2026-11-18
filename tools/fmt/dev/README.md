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
for f in Blank Meaning Passes Rules Spacing Slice1 Slice2 Slice3 DocDump Twin; do
  cp tools/fmt/src/Fmt/$f.sw $SLIM/src/Fmt/
done
printf '#!/bin/sh\nexec nice -n 15 %s run --project %s Fmt.Twin.main -- "$@"\n' \
  "$PWD/target/release/stitchwort" "$SLIM" > /path/to/scratch/twin
chmod +x /path/to/scratch/twin
```

Copy the slim folder again after changing the formatter. Each batch
starts by checking the project (about 25 s), then takes 850 MB to 1.5 GB.

## The scripts

| Script | Arguments | What it does |
|---|---|---|
| `probe.py` | `--twin TWIN --out OUT --seed N --count N` (`--bin STITCHWORT`, `--rust N`, `--sketch`) | Generates the files into OUT, formats them with the twin (`OUT/x*.out.sw`), and counts the files that fail each check: idempotence, the tidied tree, comments in order, long lines, and with `--rust N` Rust's output for the first N |
| `hangs.py` | `OUT …` | Checks K3a (section 1.4) on the outputs in Python: where each line starts against the block column in force. Family A shows here as `closer-at-block` |
| `classify.py` | `OUT` (`--bin STITCHWORT`) | Sorts the outputs that differ from `stitchwort fmt -` on the same input: glued pairs (section 3.5), layout, other |
| `sketchall.py` | `--twin TWIN OUT …` | Runs the twin's `sketch` stage over the outputs |

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
