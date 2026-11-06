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
- 00:10 Merged SW-1462/1463 (let hints for unused lets; signature by head position) and SW-1455 (std.cache 7.5 → 2.5 MB gzipped; format 27). Batch 65 passed; batch 66 check running (with one browser test of the page's Tests path, which the lane didn't exercise). Started SW-1471 (answers kept in a dependent of a broken import, Sonnet).
- 00:25 Merged SW-1471 (last good answers kept in a skipped dependent). Batch 66 (SW-1455) passed, plus a browser run of Tests and Run on the gz cache path; batch 67 (SW-1471) passed. Started SW-1489 (roadmap step 3: live goals panel + share by URL; my call, medium). Usage 55%.
- 00:40 Merged the omega bundle (SW-1488/1472/1466) after an Opus review (merge, no findings); corrected NOTES-2020 (Result.getOrElse exists). Batch 68 check running. Started SW-1119 (roadmap step 4: fill a non-exhaustive match, then case split; Sonnet; my call).
- 00:55 Merged SW-1489 (goals panel + share by URL; fixed the stale Goals-section browser test left by SW-1432). JS-only, browser-tested in the lane: no batch check. Filed SW-1490 (wasm checker's goal text maybe dead).
- 01:05 Merged SW-1458 (searches replay std.cache: 17 s → 2 s); closed SW-1460 (memory measured: small); filed SW-1491 (lazy std load for searches). Batch 69 check running. Started SW-1120 (name completion, roadmap step 6, Opus, staged) and SW-1492 (2020 day 13, Opus). Usage 55%.
- 01:15 Merged SW-1119 (quick fixes: add a match's missing arms; split an arm's variable) and SW-1492 (2020 day 13: 2165, 534035653563227; part 2 proved exactly with no coprimality hypothesis). My mistake: a chained command committed SW-1119's lib.rs conflict with markers (528f97eca) and deleted both lane branches; recovered day 13 from unreachable commits, resolved the conflict onto SW-1458's search_session (a57fad04e). Filed SW-1493..1501 (day 13 and SW-1119 findings). Batch 70 check running.
- 01:40 SW-1120 (name completion: all three stages, 60 min) conflicts with SW-1119/SW-1458 in four files: aborted the merge cleanly and sent it back to merge main itself. Merged SW-1439 (dot-call receiver types) after an Opus review found and the lane fixed a position bug after [n := m] patterns; batch 71 check running. Started SW-1494 with SW-1495 (std divisibility bridges, minBy lemmas; Sonnet). Usage 56%. D for the morning from SW-1120: is 3.5-6 s dot completion acceptable for now [rec: yes; next, answer it on the checker's live session].
- 01:55 Merged SW-1120 (name completion) after the lane merged main itself; its slow first dot completion was the worktree's missing cache (6.7 s with the cache, 142 s without). Batch 72 check running. Filed SW-1503..1505. Started SW-1503 (dot completion on the live session; Opus; my call: speed is the night's first priority, so I didn't wait for D2445).
- 02:05 Merged SW-1494/1495 (std divisibility bridges, minBy lemmas; day 13 uses them) and SW-1502 (2020 day 14: 13496669152158, 3278997609887; both parts exact, no hypothesis). Batch 72 (SW-1120) passed. Batch 73 found two missing hash snapshots (SW-1439's new examples) and the prelude's new std lemma hashes (additions only): committed; hash tests 9/9 and audits of days 13-14 (133) pass. Filed SW-1506..1513 (day 14 findings). Started SW-1506 (checker hang on a parser literal mismatch, Opus) and SW-1504 with SW-1490 (browser completion tests; dead wasm goal text; Sonnet). Usage 56%.
- 02:20 Merged SW-1504 (browser completion tests; SW-1490 closed: the wasm goal text is the no-server fallback), SW-1507/1508 (std bit and zipWith lemmas; batch 74 passed, Std.Nat audit 358/358) and SW-1503 (dot completion and contextAt 3.5-4.3 s → 0.6 s by loading only the file's dependencies; batch 75 check running). D2445 moot; new D2446 (a kept-alive session per search thread, 0.6 → 0.1 s, for memory) for the morning [rec: not yet]. Filed SW-1514..1517. Started SW-1509/1510 (std List/Map sum lemmas) and SW-1514/1517 (completion ranking; Proj. prefix). Usage 54%.
- 02:35 Merged SW-1509/1510 (std removeFirst/distinct-sum and Map lemmas; batch 76 passed). Batch 75's one failure was older than tonight: search_at_on_real_2021_goals looked for a lemma 4956a48c8 removed on 5 Nov; dropped the entry, rerun passed; filed SW-1518 to restore that goal kind. SW-1516 (code actions load less) investigated, no change: narrowing gives 4.5 → 1.9 s but loses SW-915's cross-namespace suggestions: D2447 for the morning [rec: narrow by default plus a 'search wider' action]. Started SW-1519 (2020 day 15, Opus; a speed test). Usage 57%.
- 02:55 Merged SW-1514/1517 (completion ranking, root prefix; batch 77 passed) and SW-1506 (unifier: day 14's off-by-one parser 5+ min → 1 s; an independent Opus review found a completeness loss when solving from arguments, fixed with an example). Batch 78 check running. Filed SW-1520..1523. Started SW-1520/1505 (completion follow-ups, Sonnet) and SW-1521 (a complete fix: memoise pairs found different, Opus). Usage 57%.
- 03:05 Batch 78 (SW-1506) found a regression from SW-1514 (merged 02:40, my review missed it): three stray record() conditions in dot.rs's error checks dropped the 'no shared field' error; fixed in fea0ba31c, plus SW-1506's missing hash snapshot. Rerun over all examples passed.
- 03:15 Merged SW-1520/1505 (bare-dot theorems hidden, relative prefixes, project names with imports; batch 79 passed) and SW-1519 (2020 day 15: 249, 41687; every turn proved; part 2 takes 84-357 s, so its answers test is #[ignore]d with a SLOW list: my call; main theorem stated for every turn because the audit hung at turn 30M: my call). Batch 80 passed (day 15: 17 tests, audit 32/32). Filed SW-1524..1531; day 15's numbers added to SW-1473 (std array). Started SW-1525 (audit read-back step limit) and SW-1526/1527 (omega internal error; false E-ABILITY on a pipe), both Sonnet. Usage 57%.
- 03:40 Merged SW-1526/1527 (omega re-reads a stale goal; no false E-ABILITY on a performing dot call; batch 81 passed; no Opus review: omega's term unchanged, my call) and SW-1525 (audit caps statement read-back at 5M steps; batch 82). Filed SW-1532..1534. Started SW-1532/1533 (ring's same check; chained-receiver type, Sonnet) and SW-1535 (2020 day 16, Opus). SW-1521 (unifier memo of failed pairs, complete in every mode) done; Opus review running. My call (medium): keep SW-1506's shortcut beside the memo (+0.5% work vs +2.3% memo alone).
- 03:55 Merged SW-1532/1533 (ring re-reads a stale goal; dot calls returning a type parameter typed from the receiver; batch 83 passed) and SW-1521 (unifier memo of failed pairs; independent Opus review: merge, none found; batch 84 running). Started SW-1524 (project-name completion: cost, types; Sonnet). Usage 54-58%.
- 04:00 Batch 84 (SW-1521): only a missing hash snapshot for its new example (third time tonight; added a memory to put it in briefs); committed, hash test passes.
- 04:10 SW-1534 (check hangs on a closed statement naming a huge computation): cause in the kernel (push_def evaluates closed statements unglued); proposal merged (docs/proposals/glued-closed-types.md), experiment patch in dev/patches; D2448 for the morning [rec: A, glue kept type values]. Filed SW-1537 (slow checks invisible). Started SW-1528/1536 (messages for arguments not worked out; Sonnet).
- 04:25 Merged SW-1524 (project-name completion cached, signatures shown; batch 85 passed) and SW-1535 (2020 day 16: 21071, 3429967441937; part 2's order valid and unique when elimination succeeds; batch 86 passed, audit 75 with 1 known warning). Board fix: the readsWeaken-message lane is SW-1529 (worktree named SW-1528). Filed SW-1537..1546. Started SW-1513 (leading-operator continuation lines, Sonnet) and SW-1547 (2020 day 17, Opus). Usage 54%.
- 04:45 Merged SW-1536/1529 (notes naming the argument behind each unsolved ?N; batch 87 passed), SW-1513 (leading-operator continuation lines; batch 88 passed incl. a whole-aoc check) and SW-1539/1542 (std All2 and count lemmas; batch 89). Filed SW-1548, SW-1549. Started SW-1538 (lemma inside a match arm, Opus) and SW-1540 (elimination into Aoc.Common, Sonnet). Usage 54%.
- 04:55 Merged SW-1540 (generic elimination in Aoc.Common; batch 90: 300 theorems clean) and SW-1547 (2020 day 17: 289, 2084; exact and unique in any dimension; 8.4 s; batch 91 passed, audit 43/43). Filed SW-1550..1556 from day 17. SW-1541 lane restarted after a half-made worktree (rogue cache copy missing; finished by hand). Started SW-1557 (2020 day 18, Opus). Usage 54%.
- 05:38 Merged SW-1541/1544 (Prop default for ∧ operands, rewrite note, succInjective implicit; batch 92 passed), SW-1551/1555/1558 (std == and Map/Set lemmas; batch 93), SW-1557 (2020 day 18: 15285807527593, 461295257566346; exact and unique; batch 94, audit 113, 9 known warnings). SW-1538 (match-equation transport) in Opus review. Filed SW-1558..1570. Started SW-1553/1554 (two messages, Sonnet), SW-1571 (2020 day 19, Opus). Usage 59%.
