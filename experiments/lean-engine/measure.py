#!/usr/bin/env python3
"""Measures a set of proof files the same way for Stitchwort and Lean.

  measure.py lean FILE...                 every declaration in the files
  measure.py sw --roots A,B [--emit OUT] FILE...
                                          only what the root theorems rest on

A file is split into blocks at each `theorem` or `def` (with the doc
comment above it). A theorem's proof is the text after the `:=` that
ends its statement, or from its first `|` clause when it is written by
cases; its size is its non-blank lines. Line counts follow each
language's layout (Stitchwort's formatter gives each hypothesis a line),
so the character counts are the steadier comparison. For `sw`, the live set is the
roots and everything they mention, transitively; its line count is the
blocks, one blank line after each, and each file's header if any of its
blocks is live.
"""
import re
import statistics
import sys

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(theorem|def)\s+([^\s:(]+)")


def is_doc_start(line, lang):
    stripped = line.strip()
    return stripped.startswith("--|") if lang == "sw" else stripped.startswith("/--")


def blocks_of(path, lang):
    """The file's header lines, then its blocks: (kind, name, lines)."""
    lines = open(path, encoding="utf-8").read().split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    starts = []
    for index, line in enumerate(lines):
        if DECL.match(line):
            start = index
            if lang == "sw":
                while start > 0 and lines[start - 1].strip().startswith("--|"):
                    start -= 1
            else:
                probe = index - 1
                while probe >= 0 and lines[probe].strip() and not DECL.match(lines[probe]):
                    if lines[probe].strip().startswith("/--"):
                        start = probe
                        break
                    probe -= 1
            starts.append((start, index))
    blocks = []
    for position, (start, decl) in enumerate(starts):
        end = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        kind, name = DECL.match(lines[decl]).groups()
        body = lines[start:end]
        while body and not body[-1].strip():
            body.pop()
        blocks.append((kind, name, body, lines[decl:end]))
    header = lines[: starts[0][0]] if starts else lines
    return header, blocks


def proof_text(decl_lines):
    """The proof: the text after the statement's `:=`, or from the first `|` clause."""
    text = "\n".join(decl_lines)
    depth = 0
    index = 0
    start = None
    while index < len(text):
        char = text[index]
        if char in "([{⟨":
            depth += 1
        elif char in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(":=", index):
            start = index + 2
            break
        elif depth == 0 and char == "\n" and text[index + 1 :].lstrip(" ").startswith("|"):
            start = index + 1
            break
        index += 1
    return "" if start is None else text[start:]


def proof_lines(decl_lines):
    return sum(1 for line in proof_text(decl_lines).split("\n") if line.strip())


def non_blank(text):
    return sum(1 for char in text if not char.isspace())


def mentions(text, name):
    last = name.split(".")[-1]
    if "." in name:
        return re.search(r"\." + re.escape(last) + r"\b", text) is not None
    return re.search(r"(?<![\w.])" + re.escape(name) + r"\b", text) is not None


def main():
    args = sys.argv[1:]
    lang = args.pop(0)
    roots, emit = None, None
    while args and args[0].startswith("--"):
        flag = args.pop(0)
        if flag == "--roots":
            roots = args.pop(0).split(",")
        elif flag == "--emit":
            emit = args.pop(0)
    files = [(path,) + blocks_of(path, lang) for path in args]
    every = [(path, block) for path, _, blocks in files for block in blocks]
    if roots is None:
        live = every
        total_lines = sum(len(open(path, encoding="utf-8").read().split("\n")) - 1 for path in args)
        text = "".join(open(path, encoding="utf-8").read() for path in args)
    else:
        by_name = {block[1]: (path, block) for path, block in every}
        wanted, queue = set(), list(roots)
        while queue:
            name = queue.pop()
            if name in wanted:
                continue
            wanted.add(name)
            body = "\n".join(by_name[name][1][3])
            queue.extend(other for other in by_name if other not in wanted and mentions(body, other))
        live = [(path, block) for path, block in every if block[1] in wanted]
        dead = [block[1] for _, block in every if block[1] not in wanted and block[0] == "theorem"]
        pieces = []
        for path, header, blocks in files:
            kept = [block for block in blocks if block[1] in wanted]
            if kept:
                pieces.extend(header)
                for block in kept:
                    pieces.extend(block[2] + [""])
        total_lines = len(pieces)
        text = "\n".join(pieces)
        if emit:
            open(emit, "w", encoding="utf-8").write(text + "\n")
        print(f"theorems in the files not in the live set: {len(dead)}")
    theorems = [block for _, block in live if block[0] == "theorem"]
    defs = [block for _, block in live if block[0] == "def"]
    sizes = sorted(proof_lines(block[3]) for block in theorems)
    largest = max(theorems, key=lambda block: proof_lines(block[3]))
    print(f"lines: {total_lines}")
    print(f"non-blank characters: {non_blank(text)}")
    print(f"theorems: {len(theorems)}")
    print(f"definitions: {len(defs)}")
    print(f"proof lines: {sum(sizes)}")
    print(f"proof non-blank characters: {sum(non_blank(proof_text(block[3])) for block in theorems)}")
    statement = sum(sum(1 for line in block[3] if line.strip()) for block in theorems) - sum(sizes)
    print(f"statement lines: {statement}")
    print(f"definition lines: {sum(sum(1 for line in block[3] if line.strip()) for block in defs)}")
    print(f"median proof: {statistics.median(sizes)} lines")
    print(f"largest proof: {sizes[-1]} lines ({largest[1]})")


main()
