# State measurements: state-step6-after-raw

- commit: 2987550a
- date: Wed Nov  4 00:25:43 GMT 2026
- machine: Darwin arm64, 10 cpus
- aoc cycles (early,middle,late): 10,100,300; rogue: 50,150,250; cli runs: 2
load start: 11.22, 8.83, 12.38

## Build
binary: /Users/matt/repos/mdr/stitchwort/.claude/worktrees/SW-1177/target/release/stitchwort

## Edit loop: aoc
load start: 10.80, 8.79, 12.34
```
    Finished `release` profile [optimized] target(s) in 0.10s
     Running tests/lsp.rs (target/release/deps/lsp-b85e4aa4dd0e0112)

running 1 test
test state_edit_loop ... first diagnostics	src/Aoc/Year2025/Day09/Proofs/Part2.sw	34.2 s
first diagnostics	src/Aoc/Common/Range.sw	201.4 s
first diagnostics	src/Aoc/Year2024/Day10/Day10.sw	201.4 s
first check: 201.4 s (to the last file's diagnostics)
sample	cycle 0	rss_kb 4016688	heap_bytes 1265344786
journal	cycle 0	entries 580346	peak_entries 322334	held 322334	bytes_held 26975232	distinct_keys 322313	open 208	rewinds 1	undone 0	checkpoints 208	transactions 273
cycle	1	src/Aoc/Common/Range.sw	edit	461 ms
cycle	2	src/Aoc/Common/Range.sw	undo	228 ms
cycle	3	src/Aoc/Common/Range.sw	edit	273 ms
cycle	4	src/Aoc/Common/Range.sw	undo	220 ms
cycle	5	src/Aoc/Common/Range.sw	edit	291 ms
cycle	6	src/Aoc/Common/Range.sw	undo	222 ms
cycle	7	src/Aoc/Common/Range.sw	edit	275 ms
cycle	8	src/Aoc/Common/Range.sw	undo	236 ms
cycle	9	src/Aoc/Common/Range.sw	edit	282 ms
cycle	10	src/Aoc/Common/Range.sw	undo	220 ms
sample	cycle 10	rss_kb 4131472	heap_bytes 557674665
journal	cycle 10	entries 608792	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 20	undone 342054	checkpoints 227	transactions 292
cycle	11	src/Aoc/Year2024/Day10/Day10.sw	edit	249 ms
cycle	12	src/Aoc/Year2024/Day10/Day10.sw	undo	235 ms
cycle	13	src/Aoc/Year2024/Day10/Day10.sw	edit	243 ms
cycle	14	src/Aoc/Year2024/Day10/Day10.sw	undo	230 ms
cycle	15	src/Aoc/Year2024/Day10/Day10.sw	edit	252 ms
cycle	16	src/Aoc/Year2024/Day10/Day10.sw	undo	230 ms
cycle	17	src/Aoc/Year2024/Day10/Day10.sw	edit	237 ms
cycle	18	src/Aoc/Year2024/Day10/Day10.sw	undo	250 ms
cycle	19	src/Aoc/Year2024/Day10/Day10.sw	edit	241 ms
cycle	20	src/Aoc/Year2024/Day10/Day10.sw	undo	232 ms
sample	cycle 20	rss_kb 4243216	heap_bytes 561518112
journal	cycle 20	entries 614642	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 39	undone 347506	checkpoints 247	transactions 312
cycle	21	src/Aoc/Year2024/Day10/Day10.sw	edit	229 ms
cycle	22	src/Aoc/Year2024/Day10/Day10.sw	undo	247 ms
cycle	23	src/Aoc/Year2024/Day10/Day10.sw	edit	238 ms
cycle	24	src/Aoc/Year2024/Day10/Day10.sw	undo	228 ms
cycle	25	src/Aoc/Year2024/Day10/Day10.sw	edit	257 ms
cycle	26	src/Aoc/Year2024/Day10/Day10.sw	undo	232 ms
cycle	27	src/Aoc/Year2024/Day10/Day10.sw	edit	240 ms
cycle	28	src/Aoc/Year2024/Day10/Day10.sw	undo	240 ms
cycle	29	src/Aoc/Year2024/Day10/Day10.sw	edit	239 ms
cycle	30	src/Aoc/Year2024/Day10/Day10.sw	undo	233 ms
sample	cycle 30	rss_kb 4354896	heap_bytes 561804056
journal	cycle 30	entries 620492	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 59	undone 353356	checkpoints 267	transactions 332
cycle	31	src/Aoc/Year2024/Day10/Day10.sw	edit	227 ms
cycle	32	src/Aoc/Year2024/Day10/Day10.sw	undo	243 ms
cycle	33	src/Aoc/Year2024/Day10/Day10.sw	edit	243 ms
cycle	34	src/Aoc/Year2024/Day10/Day10.sw	undo	232 ms
cycle	35	src/Aoc/Year2024/Day10/Day10.sw	edit	255 ms
cycle	36	src/Aoc/Year2024/Day10/Day10.sw	undo	229 ms
cycle	37	src/Aoc/Year2024/Day10/Day10.sw	edit	241 ms
cycle	38	src/Aoc/Year2024/Day10/Day10.sw	undo	242 ms
cycle	39	src/Aoc/Year2024/Day10/Day10.sw	edit	247 ms
cycle	40	src/Aoc/Year2024/Day10/Day10.sw	undo	233 ms
sample	cycle 40	rss_kb 4462368	heap_bytes 559012794
journal	cycle 40	entries 626342	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 79	undone 359206	checkpoints 287	transactions 352
cycle	41	src/Aoc/Year2024/Day10/Day10.sw	edit	236 ms
cycle	42	src/Aoc/Year2024/Day10/Day10.sw	undo	250 ms
cycle	43	src/Aoc/Year2024/Day10/Day10.sw	edit	244 ms
cycle	44	src/Aoc/Year2024/Day10/Day10.sw	undo	228 ms
cycle	45	src/Aoc/Year2024/Day10/Day10.sw	edit	260 ms
cycle	46	src/Aoc/Year2024/Day10/Day10.sw	undo	232 ms
cycle	47	src/Aoc/Year2024/Day10/Day10.sw	edit	242 ms
cycle	48	src/Aoc/Year2024/Day10/Day10.sw	undo	241 ms
cycle	49	src/Aoc/Year2024/Day10/Day10.sw	edit	239 ms
cycle	50	src/Aoc/Year2024/Day10/Day10.sw	undo	228 ms
sample	cycle 50	rss_kb 4471408	heap_bytes 559212799
journal	cycle 50	entries 632192	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 99	undone 365056	checkpoints 307	transactions 372
cycle	51	src/Aoc/Year2024/Day10/Day10.sw	edit	229 ms
cycle	52	src/Aoc/Year2024/Day10/Day10.sw	undo	242 ms
cycle	53	src/Aoc/Year2024/Day10/Day10.sw	edit	238 ms
cycle	54	src/Aoc/Year2024/Day10/Day10.sw	undo	225 ms
cycle	55	src/Aoc/Year2024/Day10/Day10.sw	edit	257 ms
cycle	56	src/Aoc/Year2024/Day10/Day10.sw	undo	226 ms
cycle	57	src/Aoc/Year2024/Day10/Day10.sw	edit	237 ms
cycle	58	src/Aoc/Year2024/Day10/Day10.sw	undo	236 ms
cycle	59	src/Aoc/Year2024/Day10/Day10.sw	edit	243 ms
cycle	60	src/Aoc/Year2024/Day10/Day10.sw	undo	230 ms
sample	cycle 60	rss_kb 4561872	heap_bytes 558928036
journal	cycle 60	entries 638042	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 119	undone 370906	checkpoints 327	transactions 392
cycle	61	src/Aoc/Year2024/Day10/Day10.sw	edit	231 ms
cycle	62	src/Aoc/Year2024/Day10/Day10.sw	undo	248 ms
cycle	63	src/Aoc/Year2024/Day10/Day10.sw	edit	233 ms
cycle	64	src/Aoc/Year2024/Day10/Day10.sw	undo	225 ms
cycle	65	src/Aoc/Year2024/Day10/Day10.sw	edit	243 ms
cycle	66	src/Aoc/Year2024/Day10/Day10.sw	undo	223 ms
cycle	67	src/Aoc/Year2024/Day10/Day10.sw	edit	232 ms
cycle	68	src/Aoc/Year2024/Day10/Day10.sw	undo	224 ms
cycle	69	src/Aoc/Year2024/Day10/Day10.sw	edit	250 ms
cycle	70	src/Aoc/Year2024/Day10/Day10.sw	undo	224 ms
sample	cycle 70	rss_kb 4562048	heap_bytes 559493417
journal	cycle 70	entries 643892	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 139	undone 376756	checkpoints 347	transactions 412
cycle	71	src/Aoc/Year2024/Day10/Day10.sw	edit	234 ms
cycle	72	src/Aoc/Year2024/Day10/Day10.sw	undo	248 ms
cycle	73	src/Aoc/Year2024/Day10/Day10.sw	edit	236 ms
cycle	74	src/Aoc/Year2024/Day10/Day10.sw	undo	226 ms
cycle	75	src/Aoc/Year2024/Day10/Day10.sw	edit	251 ms
cycle	76	src/Aoc/Year2024/Day10/Day10.sw	undo	228 ms
cycle	77	src/Aoc/Year2024/Day10/Day10.sw	edit	238 ms
cycle	78	src/Aoc/Year2024/Day10/Day10.sw	undo	223 ms
cycle	79	src/Aoc/Year2024/Day10/Day10.sw	edit	248 ms
cycle	80	src/Aoc/Year2024/Day10/Day10.sw	undo	222 ms
sample	cycle 80	rss_kb 4562048	heap_bytes 561267662
journal	cycle 80	entries 649742	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 159	undone 382606	checkpoints 367	transactions 432
cycle	81	src/Aoc/Year2024/Day10/Day10.sw	edit	225 ms
cycle	82	src/Aoc/Year2024/Day10/Day10.sw	undo	236 ms
cycle	83	src/Aoc/Year2024/Day10/Day10.sw	edit	230 ms
cycle	84	src/Aoc/Year2024/Day10/Day10.sw	undo	219 ms
cycle	85	src/Aoc/Year2024/Day10/Day10.sw	edit	236 ms
cycle	86	src/Aoc/Year2024/Day10/Day10.sw	undo	229 ms
cycle	87	src/Aoc/Year2024/Day10/Day10.sw	edit	229 ms
cycle	88	src/Aoc/Year2024/Day10/Day10.sw	undo	221 ms
cycle	89	src/Aoc/Year2024/Day10/Day10.sw	edit	244 ms
cycle	90	src/Aoc/Year2024/Day10/Day10.sw	undo	219 ms
sample	cycle 90	rss_kb 4562048	heap_bytes 559463251
journal	cycle 90	entries 655592	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 179	undone 388456	checkpoints 387	transactions 452
cycle	91	src/Aoc/Year2024/Day10/Day10.sw	edit	224 ms
cycle	92	src/Aoc/Year2024/Day10/Day10.sw	undo	230 ms
cycle	93	src/Aoc/Year2024/Day10/Day10.sw	edit	233 ms
cycle	94	src/Aoc/Year2024/Day10/Day10.sw	undo	222 ms
cycle	95	src/Aoc/Year2024/Day10/Day10.sw	edit	230 ms
cycle	96	src/Aoc/Year2024/Day10/Day10.sw	undo	236 ms
cycle	97	src/Aoc/Year2024/Day10/Day10.sw	edit	231 ms
cycle	98	src/Aoc/Year2024/Day10/Day10.sw	undo	225 ms
cycle	99	src/Aoc/Year2024/Day10/Day10.sw	edit	241 ms
cycle	100	src/Aoc/Year2024/Day10/Day10.sw	undo	220 ms
sample	cycle 100	rss_kb 4562048	heap_bytes 559601928
journal	cycle 100	entries 661442	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 199	undone 394306	checkpoints 407	transactions 472
cycle	101	src/Aoc/Year2024/Day10/Day10.sw	edit	223 ms
cycle	102	src/Aoc/Year2024/Day10/Day10.sw	undo	219 ms
cycle	103	src/Aoc/Year2024/Day10/Day10.sw	edit	247 ms
cycle	104	src/Aoc/Year2024/Day10/Day10.sw	undo	219 ms
cycle	105	src/Aoc/Year2024/Day10/Day10.sw	edit	231 ms
cycle	106	src/Aoc/Year2024/Day10/Day10.sw	undo	236 ms
cycle	107	src/Aoc/Year2024/Day10/Day10.sw	edit	230 ms
cycle	108	src/Aoc/Year2024/Day10/Day10.sw	undo	220 ms
cycle	109	src/Aoc/Year2024/Day10/Day10.sw	edit	245 ms
cycle	110	src/Aoc/Year2024/Day10/Day10.sw	undo	222 ms
sample	cycle 110	rss_kb 4562048	heap_bytes 559004109
journal	cycle 110	entries 667292	peak_entries 322334	held 9124	bytes_held 26975232	distinct_keys 9124	open 6	rewinds 219	undone 400156	checkpoints 427	transactions 492
cycle	111	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1921 ms
cycle	112	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	234 ms
cycle	113	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1939 ms
cycle	114	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	115	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1930 ms
cycle	116	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	117	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1928 ms
cycle	118	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	119	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1929 ms
cycle	120	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	233 ms
sample	cycle 120	rss_kb 4383424	heap_bytes 553471647
journal	cycle 120	entries 718453	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 239	undone 451715	checkpoints 448	transactions 513
cycle	121	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1932 ms
cycle	122	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	254 ms
cycle	123	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1945 ms
cycle	124	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	125	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1937 ms
cycle	126	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	127	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1924 ms
cycle	128	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	234 ms
cycle	129	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1916 ms
cycle	130	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
sample	cycle 130	rss_kb 4194336	heap_bytes 553358528
journal	cycle 130	entries 769614	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 259	undone 502876	checkpoints 469	transactions 534
cycle	131	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1972 ms
cycle	132	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	133	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1912 ms
cycle	134	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
cycle	135	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1914 ms
cycle	136	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	230 ms
cycle	137	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1916 ms
cycle	138	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	139	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1925 ms
cycle	140	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
sample	cycle 140	rss_kb 4091984	heap_bytes 553391836
journal	cycle 140	entries 820775	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 279	undone 554037	checkpoints 490	transactions 555
cycle	141	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1958 ms
cycle	142	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	143	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1918 ms
cycle	144	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	236 ms
cycle	145	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1923 ms
cycle	146	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	236 ms
cycle	147	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1920 ms
cycle	148	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	149	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1956 ms
cycle	150	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
sample	cycle 150	rss_kb 3979376	heap_bytes 553485841
journal	cycle 150	entries 871936	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 299	undone 605198	checkpoints 511	transactions 576
cycle	151	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1961 ms
cycle	152	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	153	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1940 ms
cycle	154	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
cycle	155	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1928 ms
cycle	156	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	227 ms
cycle	157	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1958 ms
cycle	158	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
cycle	159	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1913 ms
cycle	160	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	232 ms
sample	cycle 160	rss_kb 4089184	heap_bytes 553454871
journal	cycle 160	entries 923097	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 319	undone 656359	checkpoints 532	transactions 597
cycle	161	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1926 ms
cycle	162	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	233 ms
cycle	163	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1913 ms
cycle	164	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	165	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1937 ms
cycle	166	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	167	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1929 ms
cycle	168	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	169	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1930 ms
cycle	170	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	233 ms
sample	cycle 170	rss_kb 3992656	heap_bytes 553486325
journal	cycle 170	entries 974258	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 339	undone 707520	checkpoints 553	transactions 618
cycle	171	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1928 ms
cycle	172	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	173	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1932 ms
cycle	174	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	175	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1918 ms
cycle	176	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
cycle	177	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1917 ms
cycle	178	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	233 ms
cycle	179	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1913 ms
cycle	180	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
sample	cycle 180	rss_kb 4005248	heap_bytes 553514557
journal	cycle 180	entries 1025419	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 359	undone 758681	checkpoints 574	transactions 639
cycle	181	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1940 ms
cycle	182	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	183	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1937 ms
cycle	184	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	185	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1922 ms
cycle	186	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
cycle	187	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1952 ms
cycle	188	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	228 ms
cycle	189	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1914 ms
cycle	190	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
sample	cycle 190	rss_kb 4004000	heap_bytes 553547085
journal	cycle 190	entries 1076580	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 379	undone 809842	checkpoints 595	transactions 660
cycle	191	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1967 ms
cycle	192	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
cycle	193	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1913 ms
cycle	194	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	237 ms
cycle	195	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1917 ms
cycle	196	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	197	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1934 ms
cycle	198	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	199	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1933 ms
cycle	200	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
sample	cycle 200	rss_kb 4004048	heap_bytes 553579091
journal	cycle 200	entries 1127741	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 399	undone 861003	checkpoints 616	transactions 681
cycle	201	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1936 ms
cycle	202	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
cycle	203	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1928 ms
cycle	204	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	205	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1940 ms
cycle	206	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	228 ms
cycle	207	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1939 ms
cycle	208	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	209	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1931 ms
cycle	210	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	232 ms
sample	cycle 210	rss_kb 4001904	heap_bytes 553610733
journal	cycle 210	entries 1178902	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 419	undone 912164	checkpoints 637	transactions 702
cycle	211	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1953 ms
cycle	212	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	213	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1943 ms
cycle	214	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	215	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1932 ms
cycle	216	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	217	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1931 ms
cycle	218	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	231 ms
cycle	219	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1918 ms
cycle	220	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	227 ms
sample	cycle 220	rss_kb 4111680	heap_bytes 553353004
journal	cycle 220	entries 1230063	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 439	undone 963325	checkpoints 658	transactions 723
cycle	221	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1940 ms
cycle	222	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	223	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1937 ms
cycle	224	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	225	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1920 ms
cycle	226	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	233 ms
cycle	227	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1917 ms
cycle	228	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	229	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1942 ms
cycle	230	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
sample	cycle 230	rss_kb 4080736	heap_bytes 553781767
journal	cycle 230	entries 1281224	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 459	undone 1014486	checkpoints 679	transactions 744
cycle	231	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1945 ms
cycle	232	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	233	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1950 ms
cycle	234	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	241 ms
cycle	235	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1923 ms
cycle	236	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	237	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1924 ms
cycle	238	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	239	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1925 ms
cycle	240	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
sample	cycle 240	rss_kb 4081056	heap_bytes 553712230
journal	cycle 240	entries 1332385	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 479	undone 1065647	checkpoints 700	transactions 765
cycle	241	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1916 ms
cycle	242	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
cycle	243	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1919 ms
cycle	244	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	245	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1923 ms
cycle	246	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
cycle	247	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1928 ms
cycle	248	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	249	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1922 ms
cycle	250	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
sample	cycle 250	rss_kb 4059136	heap_bytes 553404077
journal	cycle 250	entries 1383546	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 499	undone 1116808	checkpoints 721	transactions 786
cycle	251	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1863 ms
cycle	252	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	219 ms
cycle	253	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1866 ms
cycle	254	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	255	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1857 ms
cycle	256	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	257	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1847 ms
cycle	258	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	229 ms
cycle	259	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1871 ms
cycle	260	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
sample	cycle 260	rss_kb 4070160	heap_bytes 553522046
journal	cycle 260	entries 1434707	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 519	undone 1167969	checkpoints 742	transactions 807
cycle	261	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1867 ms
cycle	262	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	263	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1863 ms
cycle	264	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	265	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1845 ms
cycle	266	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	267	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1856 ms
cycle	268	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	221 ms
cycle	269	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1873 ms
cycle	270	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	220 ms
sample	cycle 270	rss_kb 4179952	heap_bytes 553799874
journal	cycle 270	entries 1485868	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 539	undone 1219130	checkpoints 763	transactions 828
cycle	271	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1878 ms
cycle	272	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	273	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1853 ms
cycle	274	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	275	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1878 ms
cycle	276	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	277	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1863 ms
cycle	278	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	279	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1867 ms
cycle	280	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	227 ms
sample	cycle 280	rss_kb 4147072	heap_bytes 553828718
journal	cycle 280	entries 1537029	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 559	undone 1270291	checkpoints 784	transactions 849
cycle	281	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1951 ms
cycle	282	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	237 ms
cycle	283	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1929 ms
cycle	284	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	285	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1930 ms
cycle	286	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	287	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1947 ms
cycle	288	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
cycle	289	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1943 ms
cycle	290	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	236 ms
sample	cycle 290	rss_kb 3991264	heap_bytes 554983745
journal	cycle 290	entries 1588190	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 579	undone 1321452	checkpoints 805	transactions 870
cycle	291	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1970 ms
cycle	292	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	227 ms
cycle	293	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1947 ms
cycle	294	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	295	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1929 ms
cycle	296	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	239 ms
cycle	297	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1940 ms
cycle	298	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	228 ms
cycle	299	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2273 ms
cycle	300	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	393 ms
sample	cycle 300	rss_kb 4101056	heap_bytes 567463043
journal	cycle 300	entries 1657944	peak_entries 322334	held 27319	bytes_held 26975232	distinct_keys 27317	open 19	rewinds 599	undone 1372613	checkpoints 840	transactions 905
cycle	301	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3118 ms
cycle	302	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	339 ms
cycle	303	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3112 ms
cycle	304	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	394 ms
cycle	305	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2300 ms
cycle	306	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	300 ms
cycle	307	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3071 ms
cycle	308	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	350 ms
cycle	309	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2635 ms
cycle	310	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	277 ms
sample	cycle 310	rss_kb 4048256	heap_bytes 567267299
journal	cycle 310	entries 1727527	peak_entries 322334	held 26942	bytes_held 26975232	distinct_keys 26940	open 18	rewinds 619	undone 1442573	checkpoints 874	transactions 939
cycle	311	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1956 ms
cycle	312	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	239 ms
cycle	313	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1939 ms
cycle	314	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	315	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1932 ms
cycle	316	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
cycle	317	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1921 ms
cycle	318	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	236 ms
cycle	319	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1924 ms
cycle	320	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	231 ms
sample	cycle 320	rss_kb 4050240	heap_bytes 555076247
journal	cycle 320	entries 1778519	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 639	undone 1511781	checkpoints 895	transactions 960
cycle	321	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3826 ms
cycle	322	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	404 ms
cycle	323	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4178 ms
cycle	324	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	492 ms
cycle	325	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4407 ms
cycle	326	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	462 ms
cycle	327	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4305 ms
cycle	328	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	359 ms
cycle	329	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4037 ms
cycle	330	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	474 ms
sample	cycle 330	rss_kb 4016128	heap_bytes 567418343
journal	cycle 330	entries 1850453	peak_entries 322334	held 26942	bytes_held 26975232	distinct_keys 26940	open 18	rewinds 658	undone 1565499	checkpoints 929	transactions 994
cycle	331	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4355 ms
cycle	332	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	425 ms
cycle	333	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3828 ms
cycle	334	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	236 ms
cycle	335	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3150 ms
cycle	336	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	410 ms
cycle	337	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3469 ms
cycle	338	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	386 ms
cycle	339	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3061 ms
cycle	340	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	373 ms
sample	cycle 340	rss_kb 3996176	heap_bytes 573511556
journal	cycle 340	entries 1924593	peak_entries 322334	held 29317	bytes_held 26975232	distinct_keys 29315	open 22	rewinds 677	undone 1637264	checkpoints 967	transactions 1032
cycle	341	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2937 ms
cycle	342	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	385 ms
cycle	343	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2986 ms
cycle	344	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	312 ms
cycle	345	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2882 ms
cycle	346	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	377 ms
cycle	347	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2813 ms
cycle	348	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	227 ms
cycle	349	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1937 ms
cycle	350	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
sample	cycle 350	rss_kb 4009424	heap_bytes 553820683
journal	cycle 350	entries 1975586	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 697	undone 1708848	checkpoints 988	transactions 1053
cycle	351	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1948 ms
cycle	352	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	234 ms
cycle	353	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1882 ms
cycle	354	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	355	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1865 ms
cycle	356	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	357	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1878 ms
cycle	358	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	219 ms
cycle	359	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1879 ms
cycle	360	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
sample	cycle 360	rss_kb 4119200	heap_bytes 554079850
journal	cycle 360	entries 2026747	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 717	undone 1760009	checkpoints 1009	transactions 1074
cycle	361	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1883 ms
cycle	362	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	223 ms
cycle	363	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1942 ms
cycle	364	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	365	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1944 ms
cycle	366	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	235 ms
cycle	367	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1918 ms
cycle	368	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	369	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1927 ms
cycle	370	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
sample	cycle 370	rss_kb 4229008	heap_bytes 554240710
journal	cycle 370	entries 2077908	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 737	undone 1811170	checkpoints 1030	transactions 1095
cycle	371	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1913 ms
cycle	372	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	373	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1858 ms
cycle	374	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	375	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1852 ms
cycle	376	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	377	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1856 ms
cycle	378	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	379	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1856 ms
cycle	380	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	216 ms
sample	cycle 380	rss_kb 4207088	heap_bytes 554114375
journal	cycle 380	entries 2129069	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 757	undone 1862331	checkpoints 1051	transactions 1116
cycle	381	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1865 ms
cycle	382	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
cycle	383	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1848 ms
cycle	384	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	222 ms
cycle	385	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1858 ms
cycle	386	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	387	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1855 ms
cycle	388	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	216 ms
cycle	389	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1845 ms
cycle	390	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	224 ms
sample	cycle 390	rss_kb 4152304	heap_bytes 554318953
journal	cycle 390	entries 2180230	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 777	undone 1913492	checkpoints 1072	transactions 1137
cycle	391	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1862 ms
cycle	392	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	228 ms
cycle	393	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1844 ms
cycle	394	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	395	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1863 ms
cycle	396	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	397	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1842 ms
cycle	398	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	399	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1843 ms
cycle	400	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	225 ms
sample	cycle 400	rss_kb 4076688	heap_bytes 554203773
journal	cycle 400	entries 2231391	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 797	undone 1964653	checkpoints 1093	transactions 1158
cycle	401	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1861 ms
cycle	402	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	403	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1861 ms
cycle	404	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
cycle	405	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1865 ms
cycle	406	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	218 ms
cycle	407	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1845 ms
cycle	408	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	226 ms
cycle	409	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1845 ms
cycle	410	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	217 ms
sample	cycle 410	rss_kb 4043824	heap_bytes 554220061
journal	cycle 410	entries 2282552	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 817	undone 2015814	checkpoints 1114	transactions 1179
final	cycle 410	rss_kb 4043824	heap_bytes 560704572
latency	src/Aoc/Common/Range.sw	edit	n 5	median 282 ms	p95 461 ms
latency	src/Aoc/Common/Range.sw	undo	n 5	median 222 ms	p95 236 ms
latency	src/Aoc/Year2024/Day10/Day10.sw	edit	n 50	median 239 ms	p95 257 ms
latency	src/Aoc/Year2024/Day10/Day10.sw	undo	n 50	median 230 ms	p95 248 ms
latency	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	n 150	median 1928 ms	p95 3469 ms
latency	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	n 150	median 226 ms	p95 393 ms
journal	cycle 410	entries 2282552	peak_entries 322334	held 8726	bytes_held 26975232	distinct_keys 8726	open 5	rewinds 817	undone 2015814	checkpoints 1114	transactions 1179
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 35 filtered out; finished in 682.60s

```
load end: 8.90, 12.97, 14.22

## Edit loop: rogue
load start: 8.90, 12.97, 14.22
```
    Finished `release` profile [optimized] target(s) in 0.15s
     Running tests/lsp.rs (target/release/deps/lsp-b85e4aa4dd0e0112)

running 1 test
test state_edit_loop ... first diagnostics	src/Rogue/Model.sw	20.1 s
first diagnostics	src/Rogue/Tests/PlayThrough.sw	20.1 s
first diagnostics	src/Rogue/Proofs/Loop.sw	22.2 s
first check: 22.2 s (to the last file's diagnostics)
sample	cycle 0	rss_kb 1632480	heap_bytes 337847747
journal	cycle 0	entries 283166	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 1	undone 0	checkpoints 4	transactions 69
cycle	1	src/Rogue/Model.sw	edit	457 ms
cycle	2	src/Rogue/Model.sw	undo	152 ms
cycle	3	src/Rogue/Model.sw	edit	458 ms
cycle	4	src/Rogue/Model.sw	undo	143 ms
cycle	5	src/Rogue/Model.sw	edit	467 ms
cycle	6	src/Rogue/Model.sw	undo	144 ms
cycle	7	src/Rogue/Model.sw	edit	467 ms
cycle	8	src/Rogue/Model.sw	undo	143 ms
cycle	9	src/Rogue/Model.sw	edit	474 ms
cycle	10	src/Rogue/Model.sw	undo	143 ms
sample	cycle 10	rss_kb 1743120	heap_bytes 308014953
journal	cycle 10	entries 330642	peak_entries 26828	held 4440	bytes_held 1863424	distinct_keys 4440	open 2	rewinds 20	undone 68190	checkpoints 23	transactions 88
cycle	11	src/Rogue/Model.sw	edit	453 ms
cycle	12	src/Rogue/Model.sw	undo	152 ms
cycle	13	src/Rogue/Model.sw	edit	461 ms
cycle	14	src/Rogue/Model.sw	undo	143 ms
cycle	15	src/Rogue/Model.sw	edit	469 ms
cycle	16	src/Rogue/Model.sw	undo	144 ms
cycle	17	src/Rogue/Model.sw	edit	467 ms
cycle	18	src/Rogue/Model.sw	undo	143 ms
cycle	19	src/Rogue/Model.sw	edit	470 ms
cycle	20	src/Rogue/Model.sw	undo	143 ms
sample	cycle 20	rss_kb 1851552	heap_bytes 308167690
journal	cycle 20	entries 378452	peak_entries 26828	held 4440	bytes_held 1863424	distinct_keys 4440	open 2	rewinds 40	undone 116000	checkpoints 43	transactions 108
cycle	21	src/Rogue/Model.sw	edit	455 ms
cycle	22	src/Rogue/Model.sw	undo	152 ms
cycle	23	src/Rogue/Model.sw	edit	461 ms
cycle	24	src/Rogue/Model.sw	undo	143 ms
cycle	25	src/Rogue/Model.sw	edit	470 ms
cycle	26	src/Rogue/Model.sw	undo	144 ms
cycle	27	src/Rogue/Model.sw	edit	468 ms
cycle	28	src/Rogue/Model.sw	undo	144 ms
cycle	29	src/Rogue/Model.sw	edit	469 ms
cycle	30	src/Rogue/Model.sw	undo	144 ms
sample	cycle 30	rss_kb 1959920	heap_bytes 308050532
journal	cycle 30	entries 426262	peak_entries 26828	held 4440	bytes_held 1863424	distinct_keys 4440	open 2	rewinds 60	undone 163810	checkpoints 63	transactions 128
cycle	31	src/Rogue/Model.sw	edit	453 ms
cycle	32	src/Rogue/Model.sw	undo	152 ms
cycle	33	src/Rogue/Model.sw	edit	481 ms
cycle	34	src/Rogue/Model.sw	undo	152 ms
cycle	35	src/Rogue/Model.sw	edit	461 ms
cycle	36	src/Rogue/Model.sw	undo	145 ms
cycle	37	src/Rogue/Model.sw	edit	469 ms
cycle	38	src/Rogue/Model.sw	undo	144 ms
cycle	39	src/Rogue/Model.sw	edit	470 ms
cycle	40	src/Rogue/Model.sw	undo	144 ms
sample	cycle 40	rss_kb 1991328	heap_bytes 308039737
journal	cycle 40	entries 474072	peak_entries 26828	held 4440	bytes_held 1863424	distinct_keys 4440	open 2	rewinds 80	undone 211620	checkpoints 83	transactions 148
cycle	41	src/Rogue/Model.sw	edit	462 ms
cycle	42	src/Rogue/Model.sw	undo	144 ms
cycle	43	src/Rogue/Model.sw	edit	464 ms
cycle	44	src/Rogue/Model.sw	undo	152 ms
cycle	45	src/Rogue/Model.sw	edit	460 ms
cycle	46	src/Rogue/Model.sw	undo	144 ms
cycle	47	src/Rogue/Model.sw	edit	469 ms
cycle	48	src/Rogue/Model.sw	undo	144 ms
cycle	49	src/Rogue/Model.sw	edit	469 ms
cycle	50	src/Rogue/Model.sw	undo	145 ms
sample	cycle 50	rss_kb 2099680	heap_bytes 308207499
journal	cycle 50	entries 521882	peak_entries 26828	held 4440	bytes_held 1863424	distinct_keys 4440	open 2	rewinds 100	undone 259430	checkpoints 103	transactions 168
cycle	51	src/Rogue/Proofs/Loop.sw	edit	2132 ms
cycle	52	src/Rogue/Proofs/Loop.sw	undo	192 ms
cycle	53	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	54	src/Rogue/Proofs/Loop.sw	undo	193 ms
cycle	55	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	56	src/Rogue/Proofs/Loop.sw	undo	193 ms
cycle	57	src/Rogue/Proofs/Loop.sw	edit	2142 ms
cycle	58	src/Rogue/Proofs/Loop.sw	undo	192 ms
cycle	59	src/Rogue/Proofs/Loop.sw	edit	2137 ms
cycle	60	src/Rogue/Proofs/Loop.sw	undo	201 ms
sample	cycle 60	rss_kb 1847888	heap_bytes 334566242
journal	cycle 60	entries 697679	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 119	undone 414513	checkpoints 124	transactions 189
cycle	61	src/Rogue/Proofs/Loop.sw	edit	2245 ms
cycle	62	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	63	src/Rogue/Proofs/Loop.sw	edit	2155 ms
cycle	64	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	65	src/Rogue/Proofs/Loop.sw	edit	2216 ms
cycle	66	src/Rogue/Proofs/Loop.sw	undo	200 ms
cycle	67	src/Rogue/Proofs/Loop.sw	edit	2174 ms
cycle	68	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	69	src/Rogue/Proofs/Loop.sw	edit	2151 ms
cycle	70	src/Rogue/Proofs/Loop.sw	undo	196 ms
sample	cycle 70	rss_kb 1782640	heap_bytes 334608274
journal	cycle 70	entries 873142	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 138	undone 589976	checkpoints 144	transactions 209
cycle	71	src/Rogue/Proofs/Loop.sw	edit	2254 ms
cycle	72	src/Rogue/Proofs/Loop.sw	undo	203 ms
cycle	73	src/Rogue/Proofs/Loop.sw	edit	2144 ms
cycle	74	src/Rogue/Proofs/Loop.sw	undo	212 ms
cycle	75	src/Rogue/Proofs/Loop.sw	edit	2165 ms
cycle	76	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	77	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	78	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	79	src/Rogue/Proofs/Loop.sw	edit	2153 ms
cycle	80	src/Rogue/Proofs/Loop.sw	undo	196 ms
sample	cycle 80	rss_kb 1723712	heap_bytes 334641078
journal	cycle 80	entries 1048605	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 157	undone 765439	checkpoints 164	transactions 229
cycle	81	src/Rogue/Proofs/Loop.sw	edit	2245 ms
cycle	82	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	83	src/Rogue/Proofs/Loop.sw	edit	2151 ms
cycle	84	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	85	src/Rogue/Proofs/Loop.sw	edit	2150 ms
cycle	86	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	87	src/Rogue/Proofs/Loop.sw	edit	2148 ms
cycle	88	src/Rogue/Proofs/Loop.sw	undo	210 ms
cycle	89	src/Rogue/Proofs/Loop.sw	edit	2136 ms
cycle	90	src/Rogue/Proofs/Loop.sw	undo	204 ms
sample	cycle 90	rss_kb 1747904	heap_bytes 334687101
journal	cycle 90	entries 1224068	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 176	undone 940902	checkpoints 184	transactions 249
cycle	91	src/Rogue/Proofs/Loop.sw	edit	2235 ms
cycle	92	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	93	src/Rogue/Proofs/Loop.sw	edit	2156 ms
cycle	94	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	95	src/Rogue/Proofs/Loop.sw	edit	2156 ms
cycle	96	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	97	src/Rogue/Proofs/Loop.sw	edit	2150 ms
cycle	98	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	99	src/Rogue/Proofs/Loop.sw	edit	2143 ms
cycle	100	src/Rogue/Proofs/Loop.sw	undo	195 ms
sample	cycle 100	rss_kb 1757664	heap_bytes 334409564
journal	cycle 100	entries 1399531	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 195	undone 1116365	checkpoints 204	transactions 269
cycle	101	src/Rogue/Proofs/Loop.sw	edit	2244 ms
cycle	102	src/Rogue/Proofs/Loop.sw	undo	203 ms
cycle	103	src/Rogue/Proofs/Loop.sw	edit	2151 ms
cycle	104	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	105	src/Rogue/Proofs/Loop.sw	edit	2153 ms
cycle	106	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	107	src/Rogue/Proofs/Loop.sw	edit	2148 ms
cycle	108	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	109	src/Rogue/Proofs/Loop.sw	edit	2146 ms
cycle	110	src/Rogue/Proofs/Loop.sw	undo	195 ms
sample	cycle 110	rss_kb 1772016	heap_bytes 334442378
journal	cycle 110	entries 1574994	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 214	undone 1291828	checkpoints 224	transactions 289
cycle	111	src/Rogue/Proofs/Loop.sw	edit	2282 ms
cycle	112	src/Rogue/Proofs/Loop.sw	undo	202 ms
cycle	113	src/Rogue/Proofs/Loop.sw	edit	2199 ms
cycle	114	src/Rogue/Proofs/Loop.sw	undo	203 ms
cycle	115	src/Rogue/Proofs/Loop.sw	edit	2156 ms
cycle	116	src/Rogue/Proofs/Loop.sw	undo	203 ms
cycle	117	src/Rogue/Proofs/Loop.sw	edit	2155 ms
cycle	118	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	119	src/Rogue/Proofs/Loop.sw	edit	2157 ms
cycle	120	src/Rogue/Proofs/Loop.sw	undo	195 ms
sample	cycle 120	rss_kb 1807232	heap_bytes 334497123
journal	cycle 120	entries 1750457	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 233	undone 1467291	checkpoints 244	transactions 309
cycle	121	src/Rogue/Proofs/Loop.sw	edit	2247 ms
cycle	122	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	123	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	124	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	125	src/Rogue/Proofs/Loop.sw	edit	2145 ms
cycle	126	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	127	src/Rogue/Proofs/Loop.sw	edit	2152 ms
cycle	128	src/Rogue/Proofs/Loop.sw	undo	206 ms
cycle	129	src/Rogue/Proofs/Loop.sw	edit	2137 ms
cycle	130	src/Rogue/Proofs/Loop.sw	undo	204 ms
sample	cycle 130	rss_kb 1844944	heap_bytes 334529119
journal	cycle 130	entries 1925920	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 252	undone 1642754	checkpoints 264	transactions 329
cycle	131	src/Rogue/Proofs/Loop.sw	edit	2249 ms
cycle	132	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	133	src/Rogue/Proofs/Loop.sw	edit	2150 ms
cycle	134	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	135	src/Rogue/Proofs/Loop.sw	edit	2145 ms
cycle	136	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	137	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	138	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	139	src/Rogue/Proofs/Loop.sw	edit	2149 ms
cycle	140	src/Rogue/Proofs/Loop.sw	undo	196 ms
sample	cycle 140	rss_kb 1735504	heap_bytes 334561162
journal	cycle 140	entries 2101383	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 271	undone 1818217	checkpoints 284	transactions 349
cycle	141	src/Rogue/Proofs/Loop.sw	edit	2237 ms
cycle	142	src/Rogue/Proofs/Loop.sw	undo	204 ms
cycle	143	src/Rogue/Proofs/Loop.sw	edit	2140 ms
cycle	144	src/Rogue/Proofs/Loop.sw	undo	203 ms
cycle	145	src/Rogue/Proofs/Loop.sw	edit	2154 ms
cycle	146	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	147	src/Rogue/Proofs/Loop.sw	edit	2148 ms
cycle	148	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	149	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	150	src/Rogue/Proofs/Loop.sw	undo	197 ms
sample	cycle 150	rss_kb 1760032	heap_bytes 334588858
journal	cycle 150	entries 2276846	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 290	undone 1993680	checkpoints 304	transactions 369
cycle	151	src/Rogue/Proofs/Loop.sw	edit	2239 ms
cycle	152	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	153	src/Rogue/Proofs/Loop.sw	edit	2153 ms
cycle	154	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	155	src/Rogue/Proofs/Loop.sw	edit	2153 ms
cycle	156	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	157	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	158	src/Rogue/Proofs/Loop.sw	undo	205 ms
cycle	159	src/Rogue/Proofs/Loop.sw	edit	2138 ms
cycle	160	src/Rogue/Proofs/Loop.sw	undo	204 ms
sample	cycle 160	rss_kb 1783856	heap_bytes 334617233
journal	cycle 160	entries 2452309	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 309	undone 2169143	checkpoints 324	transactions 389
cycle	161	src/Rogue/Proofs/Loop.sw	edit	2243 ms
cycle	162	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	163	src/Rogue/Proofs/Loop.sw	edit	2152 ms
cycle	164	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	165	src/Rogue/Proofs/Loop.sw	edit	2148 ms
cycle	166	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	167	src/Rogue/Proofs/Loop.sw	edit	2152 ms
cycle	168	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	169	src/Rogue/Proofs/Loop.sw	edit	2150 ms
cycle	170	src/Rogue/Proofs/Loop.sw	undo	197 ms
sample	cycle 170	rss_kb 1806016	heap_bytes 334651874
journal	cycle 170	entries 2627772	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 328	undone 2344606	checkpoints 344	transactions 409
cycle	171	src/Rogue/Proofs/Loop.sw	edit	2245 ms
cycle	172	src/Rogue/Proofs/Loop.sw	undo	204 ms
cycle	173	src/Rogue/Proofs/Loop.sw	edit	2142 ms
cycle	174	src/Rogue/Proofs/Loop.sw	undo	205 ms
cycle	175	src/Rogue/Proofs/Loop.sw	edit	2136 ms
cycle	176	src/Rogue/Proofs/Loop.sw	undo	203 ms
cycle	177	src/Rogue/Proofs/Loop.sw	edit	2147 ms
cycle	178	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	179	src/Rogue/Proofs/Loop.sw	edit	2146 ms
cycle	180	src/Rogue/Proofs/Loop.sw	undo	196 ms
sample	cycle 180	rss_kb 1830464	heap_bytes 334684616
journal	cycle 180	entries 2803235	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 347	undone 2520069	checkpoints 364	transactions 429
cycle	181	src/Rogue/Proofs/Loop.sw	edit	2248 ms
cycle	182	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	183	src/Rogue/Proofs/Loop.sw	edit	2148 ms
cycle	184	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	185	src/Rogue/Proofs/Loop.sw	edit	2149 ms
cycle	186	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	187	src/Rogue/Proofs/Loop.sw	edit	2151 ms
cycle	188	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	189	src/Rogue/Proofs/Loop.sw	edit	2149 ms
cycle	190	src/Rogue/Proofs/Loop.sw	undo	210 ms
sample	cycle 190	rss_kb 1710208	heap_bytes 334443668
journal	cycle 190	entries 2978698	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 366	undone 2695532	checkpoints 384	transactions 449
cycle	191	src/Rogue/Proofs/Loop.sw	edit	2233 ms
cycle	192	src/Rogue/Proofs/Loop.sw	undo	204 ms
cycle	193	src/Rogue/Proofs/Loop.sw	edit	2144 ms
cycle	194	src/Rogue/Proofs/Loop.sw	undo	195 ms
cycle	195	src/Rogue/Proofs/Loop.sw	edit	2154 ms
cycle	196	src/Rogue/Proofs/Loop.sw	undo	196 ms
cycle	197	src/Rogue/Proofs/Loop.sw	edit	2146 ms
cycle	198	src/Rogue/Proofs/Loop.sw	undo	197 ms
cycle	199	src/Rogue/Proofs/Loop.sw	edit	2148 ms
cycle	200	src/Rogue/Proofs/Loop.sw	undo	195 ms
sample	cycle 200	rss_kb 1760384	heap_bytes 334475644
journal	cycle 200	entries 3154161	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 385	undone 2870995	checkpoints 404	transactions 469
cycle	201	src/Rogue/Tests/PlayThrough.sw	edit	1448 ms
cycle	202	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	203	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	204	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	205	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	206	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	207	src/Rogue/Tests/PlayThrough.sw	edit	1333 ms
cycle	208	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	209	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	210	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 210	rss_kb 1786048	heap_bytes 334490215
journal	cycle 210	entries 3190011	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 395	undone 2906845	checkpoints 414	transactions 479
cycle	211	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	212	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	213	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	214	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	215	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	216	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	217	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	218	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	219	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	220	src/Rogue/Tests/PlayThrough.sw	undo	140 ms
sample	cycle 220	rss_kb 1907776	heap_bytes 334555446
journal	cycle 220	entries 3225861	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 405	undone 2942695	checkpoints 424	transactions 489
cycle	221	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	222	src/Rogue/Tests/PlayThrough.sw	undo	140 ms
cycle	223	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	224	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	225	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	226	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	227	src/Rogue/Tests/PlayThrough.sw	edit	1331 ms
cycle	228	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	229	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	230	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 230	rss_kb 1908560	heap_bytes 334623493
journal	cycle 230	entries 3261711	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 415	undone 2978545	checkpoints 434	transactions 499
cycle	231	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	232	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	233	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	234	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	235	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	236	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	237	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	238	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	239	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	240	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 240	rss_kb 1882352	heap_bytes 334688980
journal	cycle 240	entries 3297561	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 425	undone 3014395	checkpoints 444	transactions 509
cycle	241	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	242	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	243	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	244	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	245	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	246	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	247	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	248	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	249	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	250	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 250	rss_kb 2004736	heap_bytes 334790819
journal	cycle 250	entries 3333411	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 435	undone 3050245	checkpoints 454	transactions 519
cycle	251	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	252	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	253	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	254	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	255	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	256	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	257	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	258	src/Rogue/Tests/PlayThrough.sw	undo	143 ms
cycle	259	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	260	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
sample	cycle 260	rss_kb 1956320	heap_bytes 334855794
journal	cycle 260	entries 3369261	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 445	undone 3086095	checkpoints 464	transactions 529
cycle	261	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	262	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	263	src/Rogue/Tests/PlayThrough.sw	edit	1331 ms
cycle	264	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	265	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	266	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	267	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	268	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	269	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	270	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 270	rss_kb 1883696	heap_bytes 334921793
journal	cycle 270	entries 3405111	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 455	undone 3121945	checkpoints 474	transactions 539
cycle	271	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	272	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	273	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	274	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	275	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	276	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	277	src/Rogue/Tests/PlayThrough.sw	edit	1333 ms
cycle	278	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	279	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	280	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 280	rss_kb 1810736	heap_bytes 334986768
journal	cycle 280	entries 3440961	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 465	undone 3157795	checkpoints 484	transactions 549
cycle	281	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	282	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	283	src/Rogue/Tests/PlayThrough.sw	edit	1331 ms
cycle	284	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	285	src/Rogue/Tests/PlayThrough.sw	edit	1330 ms
cycle	286	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	287	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	288	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	289	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	290	src/Rogue/Tests/PlayThrough.sw	undo	143 ms
sample	cycle 290	rss_kb 1932416	heap_bytes 334470026
journal	cycle 290	entries 3476811	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 475	undone 3193645	checkpoints 494	transactions 559
cycle	291	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	292	src/Rogue/Tests/PlayThrough.sw	undo	141 ms
cycle	293	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	294	src/Rogue/Tests/PlayThrough.sw	undo	141 ms
cycle	295	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	296	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	297	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	298	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	299	src/Rogue/Tests/PlayThrough.sw	edit	1331 ms
cycle	300	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 300	rss_kb 1871632	heap_bytes 334535001
journal	cycle 300	entries 3512661	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 485	undone 3229495	checkpoints 504	transactions 569
cycle	301	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	302	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	303	src/Rogue/Tests/PlayThrough.sw	edit	1333 ms
cycle	304	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	305	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	306	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	307	src/Rogue/Tests/PlayThrough.sw	edit	1336 ms
cycle	308	src/Rogue/Tests/PlayThrough.sw	undo	133 ms
cycle	309	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	310	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 310	rss_kb 1822992	heap_bytes 334599981
journal	cycle 310	entries 3548511	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 495	undone 3265345	checkpoints 514	transactions 579
cycle	311	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	312	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	313	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	314	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	315	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	316	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	317	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	318	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	319	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	320	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 320	rss_kb 1944592	heap_bytes 334664961
journal	cycle 320	entries 3584361	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 505	undone 3301195	checkpoints 524	transactions 589
cycle	321	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	322	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	323	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	324	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	325	src/Rogue/Tests/PlayThrough.sw	edit	1314 ms
cycle	326	src/Rogue/Tests/PlayThrough.sw	undo	143 ms
cycle	327	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	328	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	329	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	330	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 330	rss_kb 1896064	heap_bytes 334735061
journal	cycle 330	entries 3620211	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 515	undone 3337045	checkpoints 534	transactions 599
cycle	331	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	332	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	333	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	334	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	335	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	336	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	337	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	338	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	339	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	340	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 340	rss_kb 1859584	heap_bytes 334800041
journal	cycle 340	entries 3656061	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 525	undone 3372895	checkpoints 544	transactions 609
cycle	341	src/Rogue/Tests/PlayThrough.sw	edit	1333 ms
cycle	342	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	343	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	344	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	345	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	346	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	347	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	348	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	349	src/Rogue/Tests/PlayThrough.sw	edit	1333 ms
cycle	350	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 350	rss_kb 1810960	heap_bytes 334865021
journal	cycle 350	entries 3691911	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 535	undone 3408745	checkpoints 554	transactions 619
cycle	351	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	352	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	353	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	354	src/Rogue/Tests/PlayThrough.sw	undo	143 ms
cycle	355	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	356	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	357	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	358	src/Rogue/Tests/PlayThrough.sw	undo	144 ms
cycle	359	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	360	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 360	rss_kb 1932560	heap_bytes 334930001
journal	cycle 360	entries 3727761	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 545	undone 3444595	checkpoints 564	transactions 629
cycle	361	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	362	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	363	src/Rogue/Tests/PlayThrough.sw	edit	1330 ms
cycle	364	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	365	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	366	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	367	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	368	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	369	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	370	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 370	rss_kb 1871760	heap_bytes 334994981
journal	cycle 370	entries 3763611	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 555	undone 3480445	checkpoints 574	transactions 639
cycle	371	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	372	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	373	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	374	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	375	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	376	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	377	src/Rogue/Tests/PlayThrough.sw	edit	1332 ms
cycle	378	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	379	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	380	src/Rogue/Tests/PlayThrough.sw	undo	138 ms
sample	cycle 380	rss_kb 1811072	heap_bytes 334439933
journal	cycle 380	entries 3799461	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 565	undone 3516295	checkpoints 584	transactions 649
cycle	381	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	382	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	383	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	384	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	385	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	386	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	387	src/Rogue/Tests/PlayThrough.sw	edit	1313 ms
cycle	388	src/Rogue/Tests/PlayThrough.sw	undo	143 ms
cycle	389	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	390	src/Rogue/Tests/PlayThrough.sw	undo	143 ms
sample	cycle 390	rss_kb 1932688	heap_bytes 334506449
journal	cycle 390	entries 3835311	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 575	undone 3552145	checkpoints 594	transactions 659
cycle	391	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	392	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	393	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	394	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	395	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	396	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	397	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	398	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	399	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	400	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 400	rss_kb 1908384	heap_bytes 334571429
journal	cycle 400	entries 3871161	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 585	undone 3587995	checkpoints 604	transactions 669
cycle	401	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	402	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	403	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	404	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	405	src/Rogue/Tests/PlayThrough.sw	edit	1332 ms
cycle	406	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	407	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	408	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	409	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	410	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 410	rss_kb 1871904	heap_bytes 334636409
journal	cycle 410	entries 3907011	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 595	undone 3623845	checkpoints 614	transactions 679
cycle	411	src/Rogue/Tests/PlayThrough.sw	edit	1321 ms
cycle	412	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	413	src/Rogue/Tests/PlayThrough.sw	edit	1330 ms
cycle	414	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	415	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	416	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	417	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	418	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	419	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	420	src/Rogue/Tests/PlayThrough.sw	undo	145 ms
sample	cycle 420	rss_kb 1823264	heap_bytes 334704461
journal	cycle 420	entries 3942861	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 605	undone 3659695	checkpoints 624	transactions 689
cycle	421	src/Rogue/Tests/PlayThrough.sw	edit	1314 ms
cycle	422	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	423	src/Rogue/Tests/PlayThrough.sw	edit	1314 ms
cycle	424	src/Rogue/Tests/PlayThrough.sw	undo	145 ms
cycle	425	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	426	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	427	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	428	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	429	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	430	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 430	rss_kb 1947120	heap_bytes 334769441
journal	cycle 430	entries 3978711	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 615	undone 3695545	checkpoints 634	transactions 699
cycle	431	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	432	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	433	src/Rogue/Tests/PlayThrough.sw	edit	1331 ms
cycle	434	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	435	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	436	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	437	src/Rogue/Tests/PlayThrough.sw	edit	1328 ms
cycle	438	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	439	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	440	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
sample	cycle 440	rss_kb 1886320	heap_bytes 334834421
journal	cycle 440	entries 4014561	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 625	undone 3731395	checkpoints 644	transactions 709
cycle	441	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	442	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	443	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	444	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	445	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	446	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	447	src/Rogue/Tests/PlayThrough.sw	edit	1330 ms
cycle	448	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	449	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	450	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 450	rss_kb 1837696	heap_bytes 334899401
journal	cycle 450	entries 4050411	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 635	undone 3767245	checkpoints 654	transactions 719
final	cycle 450	rss_kb 1837696	heap_bytes 334886436
latency	src/Rogue/Model.sw	edit	n 25	median 467 ms	p95 474 ms
latency	src/Rogue/Model.sw	undo	n 25	median 144 ms	p95 152 ms
latency	src/Rogue/Proofs/Loop.sw	edit	n 75	median 2150 ms	p95 2247 ms
latency	src/Rogue/Proofs/Loop.sw	undo	n 75	median 196 ms	p95 205 ms
latency	src/Rogue/Tests/PlayThrough.sw	edit	n 125	median 1326 ms	p95 1333 ms
latency	src/Rogue/Tests/PlayThrough.sw	undo	n 125	median 134 ms	p95 143 ms
journal	cycle 450	entries 4050411	peak_entries 26828	held 25154	bytes_held 1863424	distinct_keys 25154	open 4	rewinds 635	undone 3767245	checkpoints 654	transactions 719
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 35 filtered out; finished in 406.35s

```
load end: 3.27, 6.22, 10.28

## Command line: stitchwort check on aoc
load start: 3.27, 6.22, 10.28

| mode | user CPU s | wall s | peak RSS MB |
|---|---|---|---|
| cold --no-cache #1 | 61.01 | 61.91 | 1536 |
| cold --no-cache #2 | 60.96 | 61.80 | 1536 |
| cold, empty cache folder #1 | 62.21 | 63.24 | 1569 |
| cold, empty cache folder #2 | 62.19 | 63.24 | 1569 |
| warm #1 | 2.65 | 2.78 | 669 |
| warm #2 | 2.64 | 2.78 | 669 |
| mixed, Aoc.Year2024.Day10 edited #1 | 2.91 | 3.10 | 671 |
| mixed, Aoc.Year2024.Day10 edited #2 | 2.93 | 3.13 | 671 |
load end: 3.34, 4.51, 8.40

## Mark and rewind on aoc
load start: 3.34, 4.51, 8.40
```
    Finished `release` profile [optimized] target(s) in 0.07s
     Running tests/rewind.rs (target/release/deps/rewind-6b16ef020c039ebc)

running 1 test
test mark_and_rewind_cost_alone ... aoc with navigation, in the last namespace: ten marks 1.61 ms, resident set 19056 KB more (1905 KB a mark)
aoc with navigation, the namespace left: ten marks 1.68 ms, resident set 21424 KB more (2142 KB a mark)
aoc with navigation: mark 0.25 ms, rewind to it 0.29 ms, rewind to the start 237.46 ms
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 7 filtered out; finished in 74.42s

```
```
    Finished `release` profile [optimized] target(s) in 0.08s
     Running tests/rewind.rs (target/release/deps/rewind-6b16ef020c039ebc)

running 1 test
test mark_and_rewind_cost_alone ... aoc with navigation, in the last namespace: ten marks 1.65 ms, resident set 19056 KB more (1905 KB a mark)
aoc with navigation, the namespace left: ten marks 1.74 ms, resident set 21424 KB more (2142 KB a mark)
aoc with navigation: mark 0.23 ms, rewind to it 0.24 ms, rewind to the start 248.79 ms
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 7 filtered out; finished in 74.45s

```
load end: 2.71, 3.85, 7.53

load finish: 2.71, 3.85, 7.53
