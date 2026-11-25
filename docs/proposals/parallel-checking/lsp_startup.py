#!/usr/bin/env python3
"""The editor's start-up on a project with a cold check cache, with and
without the start-up fill (SW-4760, docs/proposals/parallel-checking.md 9.9).

Starts `stitchwort lsp` on PROJECT (a folder holding stitchwort.yaml),
opens the file DEEP, and reports the seconds from opening it to its first
diagnostics, and to the moment every source file of the project has had
diagnostics published once (the whole project checked). WORKERS is the
`startupWorkers` setting: "off", "auto" or a number. The server's own log
lines (stderr) are copied to LOG, among them the fill's summary; the
server is shut down at the end. STITCHWORT may carry a prefix
(`"/usr/bin/time -l stitchwort"`, for the peak memory in LOG).

Usage: python3 -I lsp_startup.py STITCHWORT PROJECT DEEP WORKERS LOG
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path


def send(proc, message):
    body = json.dumps(message).encode()
    proc.stdin.write(b"Content-Length: %d\r\n\r\n" % len(body) + body)
    proc.stdin.flush()


def receive(proc):
    length = None
    while True:
        line = proc.stdout.readline()
        if not line:
            raise EOFError("the server closed its output")
        line = line.strip()
        if not line:
            break
        name, _, value = line.partition(b":")
        if name.lower() == b"content-length":
            length = int(value)
    return json.loads(proc.stdout.read(length))


def main():
    binary, project, deep, workers, log = sys.argv[1:6]
    project = Path(project).resolve()
    sources = sorted(project.glob("src/**/*.sw"))
    wanted = {p.as_uri() for p in sources}
    deep_uri = (project / deep).as_uri()
    with open(log, "w") as err:
        proc = subprocess.Popen(
            binary.split() + ["lsp"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=err,
            cwd=project,
        )
        send(proc, {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
            "processId": os.getpid(),
            "rootUri": project.as_uri(),
            "capabilities": {},
            "initializationOptions": {"startupWorkers": workers},
        }})
        while receive(proc).get("id") != 1:
            pass
        send(proc, {"jsonrpc": "2.0", "method": "initialized", "params": {}})
        began = time.monotonic()
        send(proc, {"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {
                "uri": deep_uri,
                "languageId": "stitchwort",
                "version": 1,
                "text": (project / deep).read_text(),
            },
        }})
        first = None
        published = set()
        problems = 0
        while not wanted <= published:
            message = receive(proc)
            if message.get("method") != "textDocument/publishDiagnostics":
                continue
            uri = message["params"]["uri"]
            if uri == deep_uri and first is None:
                first = time.monotonic() - began
            if uri in wanted and uri not in published:
                published.add(uri)
                problems += len(message["params"]["diagnostics"])
        whole = time.monotonic() - began
        send(proc, {"jsonrpc": "2.0", "id": 2, "method": "shutdown"})
        while receive(proc).get("id") != 2:
            pass
        send(proc, {"jsonrpc": "2.0", "method": "exit"})
        proc.wait()
    print(
        "workers %-4s  first diagnostics of %s  %6.1f s  whole project (%d files, %d diagnostics)  %6.1f s"
        % (workers, deep, first, len(sources), problems, whole)
    )


if __name__ == "__main__":
    main()
