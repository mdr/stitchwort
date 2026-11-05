# Overnight run, 5–6 Nov 2026 (until about 8am)

Matt's instructions, 5 Nov ~22:45–23:00. This file survives compaction: reread it
after a summary.

## Rules for the night

- **Keep working until about 8am** if there's valuable work to pick up. Don't idle
  slots (up to three lanes).
- **Usage:** check `~/.claude/usage.json` (`seven_day.used_percentage`) at least
  hourly and before each new lane. From 80%: start no new lanes. Above 85%:
  pause work for the night. At the start: 54% used, 72% of the week gone,
  pace 0.75, resets 7 Nov 21:00. A heartbeat script
  (`scratchpad/heartbeat.sh`, run in the background) wakes the orchestrator
  hourly or as soon as usage reaches 85%; restart it each time it fires.
- **Decisions:** make small and medium decisions myself and list them in the
  morning summary; defer large ones (direction, language or kernel design,
  anything Matt would want to weigh) as D questions for the morning.
- **No daily or full tier** overnight (D2444). Matt may run one in the morning.
- **Don't get stuck:** no huge test runs. Checks after a merge stay about two
  minutes (D2441): targeted tests picked by recorded time, `audit:touched` for
  proof lanes, nothing else. Lanes keep to their time estimates (stop at
  1.5×, end at 3×). A DeepSeek run stopped at 2× if it's going in circles.
  If something hangs, stop it and move on rather than wait.
- The playground server is off (Matt, 5 Nov ~22:55); port 8000 is free.

## Priorities

1. **The main editor track** (D2439, speed first, then the capabilities
   discussed). Language-server lanes run one at a time:
   - SW-1117 (small editor wins: import quick fix, signature help, `let`
     hints, semantic tokens): done, closing test gaps before merge.
   - SW-1459 (a broken shared file floods its dependents with E-UNKNOWN-NAME).
   - SW-1446 and SW-1456 (stack limits: nested operations; native vs wasm).
   - SW-1439 (dot-call links).
   - Std cache follow-ups: SW-1458 (proof-search worker), SW-1460 (one
     decoded copy instead of three), SW-1455 (shrink the 7.5 MB cache).
   - SW-1117's findings: unused `let` hints; same-short-name signature lookup.
2. **AoC 2020** on Opus (D2427): day 10 (SW-1461, D2442), then day 11 without
   a friction review in between (D2443); "feel free to carry on further if you
   have time", but aim for 10/11. Days' ticket-worthy findings get filed.
3. **Small fixes in parallel**, known ones or found along the way: e.g.
   SW-1398 (browser-test helper), SW-1073 (f.induct skips), single findings
   split out of SW-741 / SW-758 / SW-762. Only work with a clear benefit.
4. Bigger, only with room: SW-745 (Map/Set list-model lemmas, 2024 day 9
   part 2), SW-1029 (audit stage 2). Leave SW-199 (well-founded recursion)
   for daytime.

## Morning summary (for Matt, about 8am)

- What merged, each ticket with its bracket hint, organised by the priorities
  above.
- What's running or stopped, and why.
- Day 10 and 11 friction notes ready to review (`aoc/NOTES-2020.md`).
- Small and medium decisions I made overnight.
- Open D questions (large decisions), each with a recommendation.
- Usage at the end.

## Log

- 22:45 Started: SW-1461 (2020 day 10, Opus), SW-1398 (DeepSeek). SW-1117
  (Sonnet) closing test gaps. Merged earlier tonight: SW-1403, SW-1422/1437,
  SW-1424, SW-1442, SW-1443, SW-1441, SW-1432/1454, SW-1433, SW-1449,
  SW-1445 (doc part); SW-1457 closed (nothing to do).
- 23:20 Merged SW-1117 (editor small wins; resolved a browser.mjs drawn() conflict with SW-1433 by keeping both); batch 58 check running (lsp lane, features, wasm, two browser tests). Filed SW-1462 (unused let hints), SW-1463 (signature lookup by short name). Started SW-1459 (quiet dependents of a broken file, Sonnet).
- 23:30 Merged SW-1398 (browser helpers fail on a missing needle). Its run found a regression: hover in a library file opened by Cmd-click (SW-1464); my call (medium): fix it now, ahead of the queue, on Sonnet alongside SW-1459.
- 23:05 Merged SW-1461 (2020 day 10: both parts proved exactly, 17 min); batch 58 (SW-1117) and 59 (day 10, 28 s) checks passed. Filed SW-1465..1469 from day 10 (omega ignores Ord ≤ facts; omega note after match; List.subsequences; takeWhile/chainMono lemmas; goal printer spreads and folds). Started SW-1470 (2020 day 11, Opus). Usage 54%.
- 23:15 SW-1459 closed: already fixed by SW-1432's ordering fix; merged its test. Filed SW-1471 (hover empty in a dependent of a failed import). Started SW-1465 (omega reads Ord ≤ facts; note for unusable bracketed facts; DeepSeek).
- 23:25 DeepSeek overloaded a second time (SW-1465 lost its run): moved SW-1465 to GLM (glm-5.3), CLAUDE.md's fallback. My call: overnight, an overloaded DeepSeek run goes to GLM at once rather than retrying.
- 23:35 Merged SW-1464 (library hover: the page's jump left the name at the window edge; jumps now centre; std.cache was fine). Its debug run hit an underflow at core value.rs:2191 (quoting a variable at the wrong level): folded into SW-1448, started on Opus now (my call: possibly kernel-relevant, so ahead of the editor queue).
- 23:40 OpenCode Go hit its usage limit ('Go usage limit exceeded') on SW-1465's GLM run: no DeepSeek/GLM for the rest of the night. My call: small fixes go to Sonnet instead. SW-1465 restarted on Sonnet.
- 23:50 Merged SW-1465 (omega reads Ord <= at Nat/Int; note for unusable listed facts; 12 min, Sonnet). Batch 61 check running.
- 23:40 Merged SW-1448 (the underflow: omega's waiting-let note quoted unbound parameters; harmless in release; my call: no Opus review, no kernel term change) and SW-1470 (2020 day 11: exact within a 1000-round limit; settling itself unproved; main 19 s). Filed SW-1472 (omega note names facts by position) and SW-1473..1482 (day 11's findings). Started SW-1483 (2020 day 12, Opus; Matt allowed more days) and SW-1455 (shrink std.cache, Sonnet). Usage 54%.
- 23:50 Merged SW-1446/1456 (nested stack floors clamped; native vs wasm limits explained). My call: option C (leave native ≠ wasm); option B (also a frame-count limit) is a morning D question.
- 00:00 Merged SW-1483 (2020 day 12: exact, no hypotheses; 18 min); batch 63 (stack limits) and 64 (day 12) checks passed. Filed SW-1484..1488 from day 12. Started the omega bundle (SW-1488 Bool != facts + Result.getOr, SW-1472 note by source text, SW-1466 match-refined note; Sonnet). Usage 55%.
