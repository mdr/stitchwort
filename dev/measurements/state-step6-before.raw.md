# State measurements: state-step6-before

- commit: 3706f183
- date: Tue Nov  3 22:00:35 GMT 2026
- machine: Darwin arm64, 10 cpus
- aoc cycles (early,middle,late): 10,100,300; rogue: 50,150,250; cli runs: 2
load start: 34.12, 17.73, 15.35

## Build
binary: /Users/matt/repos/mdr/stitchwort/.claude/worktrees/SW-1172/target/release/stitchwort

## Edit loop: aoc
load start: 36.77, 18.84, 15.77
```
    Finished `release` profile [optimized] target(s) in 0.23s
     Running tests/lsp.rs (target/release/deps/lsp-b85e4aa4dd0e0112)

running 1 test
test state_edit_loop ... first check: 0.0 s (to the last message)
sample	cycle 0	rss_kb 1407776	heap_bytes 399808551
cycle	1	src/Aoc/Common/Range.sw	edit	28315 ms
cycle	2	src/Aoc/Common/Range.sw	undo	1313 ms
cycle	3	src/Aoc/Common/Range.sw	edit	1041 ms
cycle	4	src/Aoc/Common/Range.sw	undo	1032 ms
cycle	5	src/Aoc/Common/Range.sw	edit	476 ms
cycle	6	src/Aoc/Common/Range.sw	undo	1592 ms
cycle	7	src/Aoc/Common/Range.sw	edit	769 ms
cycle	8	src/Aoc/Common/Range.sw	undo	1070 ms
cycle	9	src/Aoc/Common/Range.sw	edit	303 ms
cycle	10	src/Aoc/Common/Range.sw	undo	260 ms
sample	cycle 10	rss_kb 1820320	heap_bytes 363412872
cycle	11	src/Aoc/Year2024/Day10/Day10.sw	edit	271 ms
cycle	12	src/Aoc/Year2024/Day10/Day10.sw	undo	292 ms
cycle	13	src/Aoc/Year2024/Day10/Day10.sw	edit	317 ms
cycle	14	src/Aoc/Year2024/Day10/Day10.sw	undo	239 ms
cycle	15	src/Aoc/Year2024/Day10/Day10.sw	edit	335 ms
cycle	16	src/Aoc/Year2024/Day10/Day10.sw	undo	299 ms
cycle	17	src/Aoc/Year2024/Day10/Day10.sw	edit	327 ms
cycle	18	src/Aoc/Year2024/Day10/Day10.sw	undo	284 ms
cycle	19	src/Aoc/Year2024/Day10/Day10.sw	edit	283 ms
cycle	20	src/Aoc/Year2024/Day10/Day10.sw	undo	291 ms
sample	cycle 20	rss_kb 1934880	heap_bytes 365040409
cycle	21	src/Aoc/Year2024/Day10/Day10.sw	edit	348 ms
cycle	22	src/Aoc/Year2024/Day10/Day10.sw	undo	276 ms
cycle	23	src/Aoc/Year2024/Day10/Day10.sw	edit	316 ms
cycle	24	src/Aoc/Year2024/Day10/Day10.sw	undo	382 ms
cycle	25	src/Aoc/Year2024/Day10/Day10.sw	edit	449 ms
cycle	26	src/Aoc/Year2024/Day10/Day10.sw	undo	335 ms
cycle	27	src/Aoc/Year2024/Day10/Day10.sw	edit	447 ms
cycle	28	src/Aoc/Year2024/Day10/Day10.sw	undo	357 ms
cycle	29	src/Aoc/Year2024/Day10/Day10.sw	edit	335 ms
cycle	30	src/Aoc/Year2024/Day10/Day10.sw	undo	306 ms
sample	cycle 30	rss_kb 2044032	heap_bytes 368417750
cycle	31	src/Aoc/Year2024/Day10/Day10.sw	edit	315 ms
cycle	32	src/Aoc/Year2024/Day10/Day10.sw	undo	396 ms
cycle	33	src/Aoc/Year2024/Day10/Day10.sw	edit	326 ms
cycle	34	src/Aoc/Year2024/Day10/Day10.sw	undo	335 ms
cycle	35	src/Aoc/Year2024/Day10/Day10.sw	edit	393 ms
cycle	36	src/Aoc/Year2024/Day10/Day10.sw	undo	402 ms
cycle	37	src/Aoc/Year2024/Day10/Day10.sw	edit	279 ms
cycle	38	src/Aoc/Year2024/Day10/Day10.sw	undo	292 ms
cycle	39	src/Aoc/Year2024/Day10/Day10.sw	edit	349 ms
cycle	40	src/Aoc/Year2024/Day10/Day10.sw	undo	316 ms
sample	cycle 40	rss_kb 2152288	heap_bytes 369826708
cycle	41	src/Aoc/Year2024/Day10/Day10.sw	edit	338 ms
cycle	42	src/Aoc/Year2024/Day10/Day10.sw	undo	373 ms
cycle	43	src/Aoc/Year2024/Day10/Day10.sw	edit	385 ms
cycle	44	src/Aoc/Year2024/Day10/Day10.sw	undo	284 ms
cycle	45	src/Aoc/Year2024/Day10/Day10.sw	edit	348 ms
cycle	46	src/Aoc/Year2024/Day10/Day10.sw	undo	315 ms
cycle	47	src/Aoc/Year2024/Day10/Day10.sw	edit	409 ms
cycle	48	src/Aoc/Year2024/Day10/Day10.sw	undo	393 ms
cycle	49	src/Aoc/Year2024/Day10/Day10.sw	edit	386 ms
cycle	50	src/Aoc/Year2024/Day10/Day10.sw	undo	325 ms
sample	cycle 50	rss_kb 2262080	heap_bytes 369781273
cycle	51	src/Aoc/Year2024/Day10/Day10.sw	edit	422 ms
cycle	52	src/Aoc/Year2024/Day10/Day10.sw	undo	325 ms
cycle	53	src/Aoc/Year2024/Day10/Day10.sw	edit	414 ms
cycle	54	src/Aoc/Year2024/Day10/Day10.sw	undo	309 ms
cycle	55	src/Aoc/Year2024/Day10/Day10.sw	edit	371 ms
cycle	56	src/Aoc/Year2024/Day10/Day10.sw	undo	346 ms
cycle	57	src/Aoc/Year2024/Day10/Day10.sw	edit	325 ms
cycle	58	src/Aoc/Year2024/Day10/Day10.sw	undo	365 ms
cycle	59	src/Aoc/Year2024/Day10/Day10.sw	edit	299 ms
cycle	60	src/Aoc/Year2024/Day10/Day10.sw	undo	391 ms
sample	cycle 60	rss_kb 2341024	heap_bytes 371328950
cycle	61	src/Aoc/Year2024/Day10/Day10.sw	edit	282 ms
cycle	62	src/Aoc/Year2024/Day10/Day10.sw	undo	292 ms
cycle	63	src/Aoc/Year2024/Day10/Day10.sw	edit	286 ms
cycle	64	src/Aoc/Year2024/Day10/Day10.sw	undo	281 ms
cycle	65	src/Aoc/Year2024/Day10/Day10.sw	edit	289 ms
cycle	66	src/Aoc/Year2024/Day10/Day10.sw	undo	283 ms
cycle	67	src/Aoc/Year2024/Day10/Day10.sw	edit	294 ms
cycle	68	src/Aoc/Year2024/Day10/Day10.sw	undo	262 ms
cycle	69	src/Aoc/Year2024/Day10/Day10.sw	edit	332 ms
cycle	70	src/Aoc/Year2024/Day10/Day10.sw	undo	238 ms
sample	cycle 70	rss_kb 2350608	heap_bytes 366032742
cycle	71	src/Aoc/Year2024/Day10/Day10.sw	edit	387 ms
cycle	72	src/Aoc/Year2024/Day10/Day10.sw	undo	250 ms
cycle	73	src/Aoc/Year2024/Day10/Day10.sw	edit	352 ms
cycle	74	src/Aoc/Year2024/Day10/Day10.sw	undo	320 ms
cycle	75	src/Aoc/Year2024/Day10/Day10.sw	edit	309 ms
cycle	76	src/Aoc/Year2024/Day10/Day10.sw	undo	307 ms
cycle	77	src/Aoc/Year2024/Day10/Day10.sw	edit	292 ms
cycle	78	src/Aoc/Year2024/Day10/Day10.sw	undo	283 ms
cycle	79	src/Aoc/Year2024/Day10/Day10.sw	edit	356 ms
cycle	80	src/Aoc/Year2024/Day10/Day10.sw	undo	229 ms
sample	cycle 80	rss_kb 2350768	heap_bytes 370279325
cycle	81	src/Aoc/Year2024/Day10/Day10.sw	edit	245 ms
cycle	82	src/Aoc/Year2024/Day10/Day10.sw	undo	285 ms
cycle	83	src/Aoc/Year2024/Day10/Day10.sw	edit	295 ms
cycle	84	src/Aoc/Year2024/Day10/Day10.sw	undo	306 ms
cycle	85	src/Aoc/Year2024/Day10/Day10.sw	edit	278 ms
cycle	86	src/Aoc/Year2024/Day10/Day10.sw	undo	309 ms
cycle	87	src/Aoc/Year2024/Day10/Day10.sw	edit	408 ms
cycle	88	src/Aoc/Year2024/Day10/Day10.sw	undo	250 ms
cycle	89	src/Aoc/Year2024/Day10/Day10.sw	edit	291 ms
cycle	90	src/Aoc/Year2024/Day10/Day10.sw	undo	236 ms
sample	cycle 90	rss_kb 2210880	heap_bytes 371332201
cycle	91	src/Aoc/Year2024/Day10/Day10.sw	edit	298 ms
cycle	92	src/Aoc/Year2024/Day10/Day10.sw	undo	244 ms
cycle	93	src/Aoc/Year2024/Day10/Day10.sw	edit	265 ms
cycle	94	src/Aoc/Year2024/Day10/Day10.sw	undo	326 ms
cycle	95	src/Aoc/Year2024/Day10/Day10.sw	edit	305 ms
cycle	96	src/Aoc/Year2024/Day10/Day10.sw	undo	235 ms
cycle	97	src/Aoc/Year2024/Day10/Day10.sw	edit	279 ms
cycle	98	src/Aoc/Year2024/Day10/Day10.sw	undo	241 ms
cycle	99	src/Aoc/Year2024/Day10/Day10.sw	edit	262 ms
cycle	100	src/Aoc/Year2024/Day10/Day10.sw	undo	308 ms
sample	cycle 100	rss_kb 2243216	heap_bytes 371117339
cycle	101	src/Aoc/Year2024/Day10/Day10.sw	edit	331 ms
cycle	102	src/Aoc/Year2024/Day10/Day10.sw	undo	274 ms
cycle	103	src/Aoc/Year2024/Day10/Day10.sw	edit	264 ms
cycle	104	src/Aoc/Year2024/Day10/Day10.sw	undo	321 ms
cycle	105	src/Aoc/Year2024/Day10/Day10.sw	edit	256 ms
cycle	106	src/Aoc/Year2024/Day10/Day10.sw	undo	299 ms
cycle	107	src/Aoc/Year2024/Day10/Day10.sw	edit	315 ms
cycle	108	src/Aoc/Year2024/Day10/Day10.sw	undo	198 ms
cycle	109	src/Aoc/Year2024/Day10/Day10.sw	edit	230 ms
cycle	110	src/Aoc/Year2024/Day10/Day10.sw	undo	201 ms
sample	cycle 110	rss_kb 2275568	heap_bytes 370510129
cycle	111	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4243 ms
cycle	112	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	2622 ms
cycle	113	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2401 ms
cycle	114	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	256 ms
cycle	115	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2182 ms
cycle	116	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	265 ms
cycle	117	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2367 ms
cycle	118	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	257 ms
cycle	119	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2119 ms
cycle	120	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	275 ms
sample	cycle 120	rss_kb 2085344	heap_bytes 401135532
cycle	121	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2074 ms
cycle	122	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
cycle	123	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1948 ms
cycle	124	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
cycle	125	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2331 ms
cycle	126	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	420 ms
cycle	127	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2676 ms
cycle	128	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	254 ms
cycle	129	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2025 ms
cycle	130	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	263 ms
sample	cycle 130	rss_kb 2055840	heap_bytes 401870657
cycle	131	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2197 ms
cycle	132	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	339 ms
cycle	133	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2205 ms
cycle	134	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	263 ms
cycle	135	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2178 ms
cycle	136	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	305 ms
cycle	137	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2136 ms
cycle	138	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	265 ms
cycle	139	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1987 ms
cycle	140	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	257 ms
sample	cycle 140	rss_kb 1966112	heap_bytes 401882981
cycle	141	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2042 ms
cycle	142	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	268 ms
cycle	143	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2357 ms
cycle	144	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	504 ms
cycle	145	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2243 ms
cycle	146	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	254 ms
cycle	147	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2121 ms
cycle	148	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
cycle	149	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2149 ms
cycle	150	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	252 ms
sample	cycle 150	rss_kb 1954240	heap_bytes 402037692
cycle	151	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2134 ms
cycle	152	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
cycle	153	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2091 ms
cycle	154	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
cycle	155	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2036 ms
cycle	156	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	249 ms
cycle	157	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1920 ms
cycle	158	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
cycle	159	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1869 ms
cycle	160	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
sample	cycle 160	rss_kb 1910784	heap_bytes 401938138
cycle	161	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1894 ms
cycle	162	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	163	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1922 ms
cycle	164	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	165	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1878 ms
cycle	166	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	245 ms
cycle	167	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1880 ms
cycle	168	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	244 ms
cycle	169	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1896 ms
cycle	170	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	245 ms
sample	cycle 170	rss_kb 1935472	heap_bytes 401976628
cycle	171	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1899 ms
cycle	172	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	173	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1883 ms
cycle	174	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	241 ms
cycle	175	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1897 ms
cycle	176	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	177	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1884 ms
cycle	178	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
cycle	179	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1885 ms
cycle	180	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
sample	cycle 180	rss_kb 1851664	heap_bytes 402019129
cycle	181	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1896 ms
cycle	182	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	241 ms
cycle	183	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1883 ms
cycle	184	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
cycle	185	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1892 ms
cycle	186	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	187	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1876 ms
cycle	188	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	189	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1956 ms
cycle	190	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	252 ms
sample	cycle 190	rss_kb 1851744	heap_bytes 402040366
cycle	191	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1963 ms
cycle	192	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
cycle	193	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2000 ms
cycle	194	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	263 ms
cycle	195	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2518 ms
cycle	196	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	259 ms
cycle	197	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1963 ms
cycle	198	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	285 ms
cycle	199	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2138 ms
cycle	200	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	274 ms
sample	cycle 200	rss_kb 1851808	heap_bytes 402093591
cycle	201	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2188 ms
cycle	202	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	281 ms
cycle	203	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2106 ms
cycle	204	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	262 ms
cycle	205	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2170 ms
cycle	206	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	312 ms
cycle	207	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2063 ms
cycle	208	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	209	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1931 ms
cycle	210	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	251 ms
sample	cycle 210	rss_kb 1873424	heap_bytes 402116473
cycle	211	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1989 ms
cycle	212	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	262 ms
cycle	213	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2440 ms
cycle	214	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	253 ms
cycle	215	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1989 ms
cycle	216	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
cycle	217	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2173 ms
cycle	218	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	275 ms
cycle	219	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2225 ms
cycle	220	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	277 ms
sample	cycle 220	rss_kb 1921424	heap_bytes 402495789
cycle	221	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2156 ms
cycle	222	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	274 ms
cycle	223	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2156 ms
cycle	224	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	258 ms
cycle	225	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1964 ms
cycle	226	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	251 ms
cycle	227	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2005 ms
cycle	228	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	251 ms
cycle	229	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2428 ms
cycle	230	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	252 ms
sample	cycle 230	rss_kb 1921504	heap_bytes 402167846
cycle	231	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1978 ms
cycle	232	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
cycle	233	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2040 ms
cycle	234	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	253 ms
cycle	235	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2099 ms
cycle	236	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	285 ms
cycle	237	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2083 ms
cycle	238	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	256 ms
cycle	239	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2140 ms
cycle	240	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	279 ms
sample	cycle 240	rss_kb 1852112	heap_bytes 402231192
cycle	241	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2070 ms
cycle	242	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	250 ms
cycle	243	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1959 ms
cycle	244	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	251 ms
cycle	245	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1965 ms
cycle	246	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	259 ms
cycle	247	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2355 ms
cycle	248	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	250 ms
cycle	249	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1955 ms
cycle	250	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	268 ms
sample	cycle 250	rss_kb 1972000	heap_bytes 402601666
cycle	251	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2118 ms
cycle	252	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	271 ms
cycle	253	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2116 ms
cycle	254	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	266 ms
cycle	255	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2114 ms
cycle	256	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
cycle	257	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2131 ms
cycle	258	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	259	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1933 ms
cycle	260	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
sample	cycle 260	rss_kb 2091872	heap_bytes 402285352
cycle	261	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1883 ms
cycle	262	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	244 ms
cycle	263	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1894 ms
cycle	264	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
cycle	265	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1889 ms
cycle	266	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
cycle	267	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1908 ms
cycle	268	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
cycle	269	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1996 ms
cycle	270	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	251 ms
sample	cycle 270	rss_kb 2211760	heap_bytes 402254494
cycle	271	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1969 ms
cycle	272	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	259 ms
cycle	273	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2002 ms
cycle	274	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	259 ms
cycle	275	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1916 ms
cycle	276	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	245 ms
cycle	277	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1945 ms
cycle	278	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	251 ms
cycle	279	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2013 ms
cycle	280	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	256 ms
sample	cycle 280	rss_kb 2151664	heap_bytes 402335966
cycle	281	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2041 ms
cycle	282	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	253 ms
cycle	283	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2047 ms
cycle	284	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	261 ms
cycle	285	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1964 ms
cycle	286	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	252 ms
cycle	287	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1961 ms
cycle	288	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	256 ms
cycle	289	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2018 ms
cycle	290	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	266 ms
sample	cycle 290	rss_kb 2055856	heap_bytes 402346250
cycle	291	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2092 ms
cycle	292	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	260 ms
cycle	293	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2090 ms
cycle	294	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	256 ms
cycle	295	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2753 ms
cycle	296	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	667 ms
cycle	297	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	5886 ms
cycle	298	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	606 ms
cycle	299	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	6400 ms
cycle	300	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	775 ms
sample	cycle 300	rss_kb 1948080	heap_bytes 404223131
cycle	301	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4302 ms
cycle	302	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	467 ms
cycle	303	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2939 ms
cycle	304	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	356 ms
cycle	305	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3045 ms
cycle	306	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	350 ms
cycle	307	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2806 ms
cycle	308	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	332 ms
cycle	309	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2999 ms
cycle	310	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	320 ms
sample	cycle 310	rss_kb 1960304	heap_bytes 405898203
cycle	311	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3181 ms
cycle	312	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	374 ms
cycle	313	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3072 ms
cycle	314	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	356 ms
cycle	315	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2573 ms
cycle	316	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	619 ms
cycle	317	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4765 ms
cycle	318	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	561 ms
cycle	319	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	6194 ms
cycle	320	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	786 ms
sample	cycle 320	rss_kb 1229568	heap_bytes 405945852
cycle	321	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	7538 ms
cycle	322	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	1124 ms
cycle	323	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	8201 ms
cycle	324	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	856 ms
cycle	325	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	7977 ms
cycle	326	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	1123 ms
cycle	327	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	8605 ms
cycle	328	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	1092 ms
cycle	329	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	5815 ms
cycle	330	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	255 ms
sample	cycle 330	rss_kb 688064	heap_bytes 401839051
cycle	331	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4700 ms
cycle	332	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	650 ms
cycle	333	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	6570 ms
cycle	334	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	913 ms
cycle	335	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	6861 ms
cycle	336	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	707 ms
cycle	337	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	6203 ms
cycle	338	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	940 ms
cycle	339	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	7240 ms
cycle	340	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	874 ms
sample	cycle 340	rss_kb 521136	heap_bytes 405971078
cycle	341	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	5772 ms
cycle	342	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	822 ms
cycle	343	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	5085 ms
cycle	344	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	320 ms
cycle	345	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2290 ms
cycle	346	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	282 ms
cycle	347	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2024 ms
cycle	348	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	349	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1977 ms
cycle	350	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	250 ms
sample	cycle 350	rss_kb 645248	heap_bytes 402444085
cycle	351	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1956 ms
cycle	352	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	249 ms
cycle	353	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1911 ms
cycle	354	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	245 ms
cycle	355	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1924 ms
cycle	356	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	357	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1890 ms
cycle	358	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	241 ms
cycle	359	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1884 ms
cycle	360	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	243 ms
sample	cycle 360	rss_kb 616288	heap_bytes 402497875
cycle	361	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1887 ms
cycle	362	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	242 ms
cycle	363	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1890 ms
cycle	364	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	253 ms
cycle	365	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1893 ms
cycle	366	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	241 ms
cycle	367	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1914 ms
cycle	368	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
cycle	369	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2355 ms
cycle	370	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	327 ms
sample	cycle 370	rss_kb 640320	heap_bytes 403877517
cycle	371	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1957 ms
cycle	372	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	429 ms
cycle	373	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2142 ms
cycle	374	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	254 ms
cycle	375	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1979 ms
cycle	376	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	249 ms
cycle	377	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1949 ms
cycle	378	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	253 ms
cycle	379	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1967 ms
cycle	380	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	253 ms
sample	cycle 380	rss_kb 652016	heap_bytes 402537379
cycle	381	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3520 ms
cycle	382	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	479 ms
cycle	383	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3120 ms
cycle	384	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	462 ms
cycle	385	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3461 ms
cycle	386	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	544 ms
cycle	387	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3850 ms
cycle	388	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	384 ms
cycle	389	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3500 ms
cycle	390	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	610 ms
sample	cycle 390	rss_kb 590512	heap_bytes 402576689
cycle	391	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3305 ms
cycle	392	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	455 ms
cycle	393	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3806 ms
cycle	394	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	456 ms
cycle	395	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2212 ms
cycle	396	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	484 ms
cycle	397	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	3262 ms
cycle	398	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	399	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	4144 ms
cycle	400	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	1104 ms
sample	cycle 400	rss_kb 650480	heap_bytes 401985094
cycle	401	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	2557 ms
cycle	402	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	246 ms
cycle	403	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1930 ms
cycle	404	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	405	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1957 ms
cycle	406	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	247 ms
cycle	407	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1950 ms
cycle	408	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	248 ms
cycle	409	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	1917 ms
cycle	410	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	272 ms
sample	cycle 410	rss_kb 686464	heap_bytes 402821020
final	cycle 410	rss_kb 686496	heap_bytes 407718129
latency	src/Aoc/Common/Range.sw	edit	n 5	median 769 ms	p95 28315 ms
latency	src/Aoc/Common/Range.sw	undo	n 5	median 1070 ms	p95 1592 ms
latency	src/Aoc/Year2024/Day10/Day10.sw	edit	n 50	median 317 ms	p95 422 ms
latency	src/Aoc/Year2024/Day10/Day10.sw	undo	n 50	median 299 ms	p95 393 ms
latency	src/Aoc/Year2025/Day09/Proofs/Part2.sw	edit	n 150	median 2091 ms	p95 6400 ms
latency	src/Aoc/Year2025/Day09/Proofs/Part2.sw	undo	n 150	median 256 ms	p95 874 ms
journal	(no JournalStats before step 6a)
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 35 filtered out; finished in 844.75s

```
load end: 27.95, 25.58, 22.45

## Edit loop: rogue
load start: 27.95, 25.58, 22.45
```
    Finished `release` profile [optimized] target(s) in 0.19s
     Running tests/lsp.rs (target/release/deps/lsp-b85e4aa4dd0e0112)

running 1 test
test state_edit_loop ... first check: 0.0 s (to the last message)
sample	cycle 0	rss_kb 1477696	heap_bytes 224772490
cycle	1	src/Rogue/Model.sw	edit	618 ms
cycle	2	src/Rogue/Model.sw	undo	2439 ms
cycle	3	src/Rogue/Model.sw	edit	2503 ms
cycle	4	src/Rogue/Model.sw	undo	2163 ms
cycle	5	src/Rogue/Model.sw	edit	486 ms
cycle	6	src/Rogue/Model.sw	undo	5136 ms
cycle	7	src/Rogue/Model.sw	edit	1479 ms
cycle	8	src/Rogue/Model.sw	undo	7580 ms
cycle	9	src/Rogue/Model.sw	edit	1477 ms
cycle	10	src/Rogue/Model.sw	undo	536 ms
sample	cycle 10	rss_kb 1736688	heap_bytes 319248361
cycle	11	src/Rogue/Model.sw	edit	1460 ms
cycle	12	src/Rogue/Model.sw	undo	5808 ms
cycle	13	src/Rogue/Model.sw	edit	772 ms
cycle	14	src/Rogue/Model.sw	undo	3443 ms
cycle	15	src/Rogue/Model.sw	edit	699 ms
cycle	16	src/Rogue/Model.sw	undo	3182 ms
cycle	17	src/Rogue/Model.sw	edit	680 ms
cycle	18	src/Rogue/Model.sw	undo	339 ms
cycle	19	src/Rogue/Model.sw	edit	1075 ms
cycle	20	src/Rogue/Model.sw	undo	5328 ms
sample	cycle 20	rss_kb 1654992	heap_bytes 296657199
cycle	21	src/Rogue/Model.sw	edit	994 ms
cycle	22	src/Rogue/Model.sw	undo	4509 ms
cycle	23	src/Rogue/Model.sw	edit	767 ms
cycle	24	src/Rogue/Model.sw	undo	210 ms
cycle	25	src/Rogue/Model.sw	edit	773 ms
cycle	26	src/Rogue/Model.sw	undo	189 ms
cycle	27	src/Rogue/Model.sw	edit	727 ms
cycle	28	src/Rogue/Model.sw	undo	3422 ms
cycle	29	src/Rogue/Model.sw	edit	671 ms
cycle	30	src/Rogue/Model.sw	undo	128 ms
sample	cycle 30	rss_kb 1761008	heap_bytes 317321755
cycle	31	src/Rogue/Model.sw	edit	868 ms
cycle	32	src/Rogue/Model.sw	undo	254 ms
cycle	33	src/Rogue/Model.sw	edit	531 ms
cycle	34	src/Rogue/Model.sw	undo	171 ms
cycle	35	src/Rogue/Model.sw	edit	583 ms
cycle	36	src/Rogue/Model.sw	undo	254 ms
cycle	37	src/Rogue/Model.sw	edit	554 ms
cycle	38	src/Rogue/Model.sw	undo	2983 ms
cycle	39	src/Rogue/Model.sw	edit	1655 ms
cycle	40	src/Rogue/Model.sw	undo	383 ms
sample	cycle 40	rss_kb 1707568	heap_bytes 329917184
cycle	41	src/Rogue/Model.sw	edit	1205 ms
cycle	42	src/Rogue/Model.sw	undo	4010 ms
cycle	43	src/Rogue/Model.sw	edit	775 ms
cycle	44	src/Rogue/Model.sw	undo	3819 ms
cycle	45	src/Rogue/Model.sw	edit	939 ms
cycle	46	src/Rogue/Model.sw	undo	3614 ms
cycle	47	src/Rogue/Model.sw	edit	846 ms
cycle	48	src/Rogue/Model.sw	undo	5214 ms
cycle	49	src/Rogue/Model.sw	edit	1147 ms
cycle	50	src/Rogue/Model.sw	undo	5187 ms
sample	cycle 50	rss_kb 1723888	heap_bytes 326648351
cycle	51	src/Rogue/Proofs/Loop.sw	edit	4878 ms
cycle	52	src/Rogue/Proofs/Loop.sw	undo	461 ms
cycle	53	src/Rogue/Proofs/Loop.sw	edit	8582 ms
cycle	54	src/Rogue/Proofs/Loop.sw	undo	376 ms
cycle	55	src/Rogue/Proofs/Loop.sw	edit	2311 ms
cycle	56	src/Rogue/Proofs/Loop.sw	undo	308 ms
cycle	57	src/Rogue/Proofs/Loop.sw	edit	2291 ms
cycle	58	src/Rogue/Proofs/Loop.sw	undo	303 ms
cycle	59	src/Rogue/Proofs/Loop.sw	edit	2242 ms
cycle	60	src/Rogue/Proofs/Loop.sw	undo	305 ms
sample	cycle 60	rss_kb 1759648	heap_bytes 333523397
cycle	61	src/Rogue/Proofs/Loop.sw	edit	2243 ms
cycle	62	src/Rogue/Proofs/Loop.sw	undo	300 ms
cycle	63	src/Rogue/Proofs/Loop.sw	edit	5730 ms
cycle	64	src/Rogue/Proofs/Loop.sw	undo	868 ms
cycle	65	src/Rogue/Proofs/Loop.sw	edit	7130 ms
cycle	66	src/Rogue/Proofs/Loop.sw	undo	974 ms
cycle	67	src/Rogue/Proofs/Loop.sw	edit	6217 ms
cycle	68	src/Rogue/Proofs/Loop.sw	undo	696 ms
cycle	69	src/Rogue/Proofs/Loop.sw	edit	3703 ms
cycle	70	src/Rogue/Proofs/Loop.sw	undo	428 ms
sample	cycle 70	rss_kb 1801840	heap_bytes 364715644
cycle	71	src/Rogue/Proofs/Loop.sw	edit	3529 ms
cycle	72	src/Rogue/Proofs/Loop.sw	undo	448 ms
cycle	73	src/Rogue/Proofs/Loop.sw	edit	5682 ms
cycle	74	src/Rogue/Proofs/Loop.sw	undo	977 ms
cycle	75	src/Rogue/Proofs/Loop.sw	edit	4826 ms
cycle	76	src/Rogue/Proofs/Loop.sw	undo	498 ms
cycle	77	src/Rogue/Proofs/Loop.sw	edit	3542 ms
cycle	78	src/Rogue/Proofs/Loop.sw	undo	310 ms
cycle	79	src/Rogue/Proofs/Loop.sw	edit	2875 ms
cycle	80	src/Rogue/Proofs/Loop.sw	undo	333 ms
sample	cycle 80	rss_kb 1729744	heap_bytes 361552485
cycle	81	src/Rogue/Proofs/Loop.sw	edit	5750 ms
cycle	82	src/Rogue/Proofs/Loop.sw	undo	487 ms
cycle	83	src/Rogue/Proofs/Loop.sw	edit	3846 ms
cycle	84	src/Rogue/Proofs/Loop.sw	undo	327 ms
cycle	85	src/Rogue/Proofs/Loop.sw	edit	4311 ms
cycle	86	src/Rogue/Proofs/Loop.sw	undo	518 ms
cycle	87	src/Rogue/Proofs/Loop.sw	edit	3923 ms
cycle	88	src/Rogue/Proofs/Loop.sw	undo	563 ms
cycle	89	src/Rogue/Proofs/Loop.sw	edit	4734 ms
cycle	90	src/Rogue/Proofs/Loop.sw	undo	539 ms
sample	cycle 90	rss_kb 1775984	heap_bytes 374954207
cycle	91	src/Rogue/Proofs/Loop.sw	edit	3256 ms
cycle	92	src/Rogue/Proofs/Loop.sw	undo	461 ms
cycle	93	src/Rogue/Proofs/Loop.sw	edit	3397 ms
cycle	94	src/Rogue/Proofs/Loop.sw	undo	483 ms
cycle	95	src/Rogue/Proofs/Loop.sw	edit	3008 ms
cycle	96	src/Rogue/Proofs/Loop.sw	undo	312 ms
cycle	97	src/Rogue/Proofs/Loop.sw	edit	2304 ms
cycle	98	src/Rogue/Proofs/Loop.sw	undo	308 ms
cycle	99	src/Rogue/Proofs/Loop.sw	edit	2266 ms
cycle	100	src/Rogue/Proofs/Loop.sw	undo	294 ms
sample	cycle 100	rss_kb 1836208	heap_bytes 333360899
cycle	101	src/Rogue/Proofs/Loop.sw	edit	2205 ms
cycle	102	src/Rogue/Proofs/Loop.sw	undo	293 ms
cycle	103	src/Rogue/Proofs/Loop.sw	edit	2191 ms
cycle	104	src/Rogue/Proofs/Loop.sw	undo	294 ms
cycle	105	src/Rogue/Proofs/Loop.sw	edit	2235 ms
cycle	106	src/Rogue/Proofs/Loop.sw	undo	294 ms
cycle	107	src/Rogue/Proofs/Loop.sw	edit	2189 ms
cycle	108	src/Rogue/Proofs/Loop.sw	undo	297 ms
cycle	109	src/Rogue/Proofs/Loop.sw	edit	2207 ms
cycle	110	src/Rogue/Proofs/Loop.sw	undo	295 ms
sample	cycle 110	rss_kb 1968656	heap_bytes 333394597
cycle	111	src/Rogue/Proofs/Loop.sw	edit	2188 ms
cycle	112	src/Rogue/Proofs/Loop.sw	undo	295 ms
cycle	113	src/Rogue/Proofs/Loop.sw	edit	2235 ms
cycle	114	src/Rogue/Proofs/Loop.sw	undo	300 ms
cycle	115	src/Rogue/Proofs/Loop.sw	edit	2224 ms
cycle	116	src/Rogue/Proofs/Loop.sw	undo	300 ms
cycle	117	src/Rogue/Proofs/Loop.sw	edit	2223 ms
cycle	118	src/Rogue/Proofs/Loop.sw	undo	300 ms
cycle	119	src/Rogue/Proofs/Loop.sw	edit	2231 ms
cycle	120	src/Rogue/Proofs/Loop.sw	undo	304 ms
sample	cycle 120	rss_kb 2065760	heap_bytes 333423145
cycle	121	src/Rogue/Proofs/Loop.sw	edit	2236 ms
cycle	122	src/Rogue/Proofs/Loop.sw	undo	299 ms
cycle	123	src/Rogue/Proofs/Loop.sw	edit	2231 ms
cycle	124	src/Rogue/Proofs/Loop.sw	undo	302 ms
cycle	125	src/Rogue/Proofs/Loop.sw	edit	2232 ms
cycle	126	src/Rogue/Proofs/Loop.sw	undo	297 ms
cycle	127	src/Rogue/Proofs/Loop.sw	edit	2222 ms
cycle	128	src/Rogue/Proofs/Loop.sw	undo	298 ms
cycle	129	src/Rogue/Proofs/Loop.sw	edit	2231 ms
cycle	130	src/Rogue/Proofs/Loop.sw	undo	300 ms
sample	cycle 130	rss_kb 1909248	heap_bytes 333456315
cycle	131	src/Rogue/Proofs/Loop.sw	edit	2221 ms
cycle	132	src/Rogue/Proofs/Loop.sw	undo	301 ms
cycle	133	src/Rogue/Proofs/Loop.sw	edit	2244 ms
cycle	134	src/Rogue/Proofs/Loop.sw	undo	300 ms
cycle	135	src/Rogue/Proofs/Loop.sw	edit	2261 ms
cycle	136	src/Rogue/Proofs/Loop.sw	undo	307 ms
cycle	137	src/Rogue/Proofs/Loop.sw	edit	2228 ms
cycle	138	src/Rogue/Proofs/Loop.sw	undo	301 ms
cycle	139	src/Rogue/Proofs/Loop.sw	edit	2252 ms
cycle	140	src/Rogue/Proofs/Loop.sw	undo	299 ms
sample	cycle 140	rss_kb 1921056	heap_bytes 333492324
cycle	141	src/Rogue/Proofs/Loop.sw	edit	2226 ms
cycle	142	src/Rogue/Proofs/Loop.sw	undo	301 ms
cycle	143	src/Rogue/Proofs/Loop.sw	edit	2240 ms
cycle	144	src/Rogue/Proofs/Loop.sw	undo	302 ms
cycle	145	src/Rogue/Proofs/Loop.sw	edit	2251 ms
cycle	146	src/Rogue/Proofs/Loop.sw	undo	308 ms
cycle	147	src/Rogue/Proofs/Loop.sw	edit	2252 ms
cycle	148	src/Rogue/Proofs/Loop.sw	undo	302 ms
cycle	149	src/Rogue/Proofs/Loop.sw	edit	2261 ms
cycle	150	src/Rogue/Proofs/Loop.sw	undo	300 ms
sample	cycle 150	rss_kb 1934704	heap_bytes 333524227
cycle	151	src/Rogue/Proofs/Loop.sw	edit	2235 ms
cycle	152	src/Rogue/Proofs/Loop.sw	undo	306 ms
cycle	153	src/Rogue/Proofs/Loop.sw	edit	2259 ms
cycle	154	src/Rogue/Proofs/Loop.sw	undo	307 ms
cycle	155	src/Rogue/Proofs/Loop.sw	edit	2245 ms
cycle	156	src/Rogue/Proofs/Loop.sw	undo	299 ms
cycle	157	src/Rogue/Proofs/Loop.sw	edit	2237 ms
cycle	158	src/Rogue/Proofs/Loop.sw	undo	302 ms
cycle	159	src/Rogue/Proofs/Loop.sw	edit	2232 ms
cycle	160	src/Rogue/Proofs/Loop.sw	undo	300 ms
sample	cycle 160	rss_kb 1995584	heap_bytes 333554771
cycle	161	src/Rogue/Proofs/Loop.sw	edit	2226 ms
cycle	162	src/Rogue/Proofs/Loop.sw	undo	301 ms
cycle	163	src/Rogue/Proofs/Loop.sw	edit	2225 ms
cycle	164	src/Rogue/Proofs/Loop.sw	undo	299 ms
cycle	165	src/Rogue/Proofs/Loop.sw	edit	2228 ms
cycle	166	src/Rogue/Proofs/Loop.sw	undo	303 ms
cycle	167	src/Rogue/Proofs/Loop.sw	edit	2237 ms
cycle	168	src/Rogue/Proofs/Loop.sw	undo	302 ms
cycle	169	src/Rogue/Proofs/Loop.sw	edit	2243 ms
cycle	170	src/Rogue/Proofs/Loop.sw	undo	301 ms
sample	cycle 170	rss_kb 1838736	heap_bytes 333583731
cycle	171	src/Rogue/Proofs/Loop.sw	edit	2264 ms
cycle	172	src/Rogue/Proofs/Loop.sw	undo	307 ms
cycle	173	src/Rogue/Proofs/Loop.sw	edit	2243 ms
cycle	174	src/Rogue/Proofs/Loop.sw	undo	302 ms
cycle	175	src/Rogue/Proofs/Loop.sw	edit	2227 ms
cycle	176	src/Rogue/Proofs/Loop.sw	undo	297 ms
cycle	177	src/Rogue/Proofs/Loop.sw	edit	2210 ms
cycle	178	src/Rogue/Proofs/Loop.sw	undo	293 ms
cycle	179	src/Rogue/Proofs/Loop.sw	edit	2190 ms
cycle	180	src/Rogue/Proofs/Loop.sw	undo	293 ms
sample	cycle 180	rss_kb 1886848	heap_bytes 333613602
cycle	181	src/Rogue/Proofs/Loop.sw	edit	2194 ms
cycle	182	src/Rogue/Proofs/Loop.sw	undo	294 ms
cycle	183	src/Rogue/Proofs/Loop.sw	edit	2183 ms
cycle	184	src/Rogue/Proofs/Loop.sw	undo	292 ms
cycle	185	src/Rogue/Proofs/Loop.sw	edit	2180 ms
cycle	186	src/Rogue/Proofs/Loop.sw	undo	291 ms
cycle	187	src/Rogue/Proofs/Loop.sw	edit	2183 ms
cycle	188	src/Rogue/Proofs/Loop.sw	undo	291 ms
cycle	189	src/Rogue/Proofs/Loop.sw	edit	2210 ms
cycle	190	src/Rogue/Proofs/Loop.sw	undo	306 ms
sample	cycle 190	rss_kb 1947152	heap_bytes 333374868
cycle	191	src/Rogue/Proofs/Loop.sw	edit	2215 ms
cycle	192	src/Rogue/Proofs/Loop.sw	undo	299 ms
cycle	193	src/Rogue/Proofs/Loop.sw	edit	2228 ms
cycle	194	src/Rogue/Proofs/Loop.sw	undo	298 ms
cycle	195	src/Rogue/Proofs/Loop.sw	edit	2244 ms
cycle	196	src/Rogue/Proofs/Loop.sw	undo	298 ms
cycle	197	src/Rogue/Proofs/Loop.sw	edit	2224 ms
cycle	198	src/Rogue/Proofs/Loop.sw	undo	300 ms
cycle	199	src/Rogue/Proofs/Loop.sw	edit	2228 ms
cycle	200	src/Rogue/Proofs/Loop.sw	undo	299 ms
sample	cycle 200	rss_kb 1995824	heap_bytes 333410030
cycle	201	src/Rogue/Tests/PlayThrough.sw	edit	1445 ms
cycle	202	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	203	src/Rogue/Tests/PlayThrough.sw	edit	1313 ms
cycle	204	src/Rogue/Tests/PlayThrough.sw	undo	138 ms
cycle	205	src/Rogue/Tests/PlayThrough.sw	edit	1353 ms
cycle	206	src/Rogue/Tests/PlayThrough.sw	undo	138 ms
cycle	207	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	208	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	209	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	210	src/Rogue/Tests/PlayThrough.sw	undo	140 ms
sample	cycle 210	rss_kb 1936832	heap_bytes 333417861
cycle	211	src/Rogue/Tests/PlayThrough.sw	edit	1327 ms
cycle	212	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	213	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	214	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	215	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	216	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	217	src/Rogue/Tests/PlayThrough.sw	edit	1312 ms
cycle	218	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	219	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	220	src/Rogue/Tests/PlayThrough.sw	undo	138 ms
sample	cycle 220	rss_kb 1862112	heap_bytes 333483092
cycle	221	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	222	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	223	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	224	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	225	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	226	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	227	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	228	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	229	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	230	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 230	rss_kb 1826032	heap_bytes 333551139
cycle	231	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	232	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	233	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	234	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
cycle	235	src/Rogue/Tests/PlayThrough.sw	edit	1329 ms
cycle	236	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	237	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	238	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	239	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	240	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
sample	cycle 240	rss_kb 1947744	heap_bytes 333616626
cycle	241	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	242	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	243	src/Rogue/Tests/PlayThrough.sw	edit	1314 ms
cycle	244	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	245	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	246	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	247	src/Rogue/Tests/PlayThrough.sw	edit	1312 ms
cycle	248	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	249	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	250	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 250	rss_kb 1899232	heap_bytes 333681601
cycle	251	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	252	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	253	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	254	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	255	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	256	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	257	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	258	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	259	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	260	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
sample	cycle 260	rss_kb 1838816	heap_bytes 333746576
cycle	261	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	262	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	263	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	264	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
cycle	265	src/Rogue/Tests/PlayThrough.sw	edit	1321 ms
cycle	266	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	267	src/Rogue/Tests/PlayThrough.sw	edit	1312 ms
cycle	268	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	269	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	270	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 270	rss_kb 1960544	heap_bytes 333812575
cycle	271	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	272	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	273	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	274	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	275	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	276	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	277	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	278	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	279	src/Rogue/Tests/PlayThrough.sw	edit	1315 ms
cycle	280	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 280	rss_kb 1924080	heap_bytes 333877550
cycle	281	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	282	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	283	src/Rogue/Tests/PlayThrough.sw	edit	1321 ms
cycle	284	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	285	src/Rogue/Tests/PlayThrough.sw	edit	1325 ms
cycle	286	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	287	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	288	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	289	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	290	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 290	rss_kb 1875456	heap_bytes 333360808
cycle	291	src/Rogue/Tests/PlayThrough.sw	edit	1321 ms
cycle	292	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	293	src/Rogue/Tests/PlayThrough.sw	edit	1321 ms
cycle	294	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	295	src/Rogue/Tests/PlayThrough.sw	edit	1317 ms
cycle	296	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	297	src/Rogue/Tests/PlayThrough.sw	edit	1312 ms
cycle	298	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	299	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	300	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 300	rss_kb 1826816	heap_bytes 333425783
cycle	301	src/Rogue/Tests/PlayThrough.sw	edit	1320 ms
cycle	302	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	303	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	304	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	305	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	306	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	307	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	308	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	309	src/Rogue/Tests/PlayThrough.sw	edit	1318 ms
cycle	310	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
sample	cycle 310	rss_kb 1948432	heap_bytes 333490763
cycle	311	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	312	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	313	src/Rogue/Tests/PlayThrough.sw	edit	1326 ms
cycle	314	src/Rogue/Tests/PlayThrough.sw	undo	138 ms
cycle	315	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	316	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	317	src/Rogue/Tests/PlayThrough.sw	edit	1321 ms
cycle	318	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
cycle	319	src/Rogue/Tests/PlayThrough.sw	edit	1319 ms
cycle	320	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
sample	cycle 320	rss_kb 1899792	heap_bytes 333555743
cycle	321	src/Rogue/Tests/PlayThrough.sw	edit	1323 ms
cycle	322	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	323	src/Rogue/Tests/PlayThrough.sw	edit	1322 ms
cycle	324	src/Rogue/Tests/PlayThrough.sw	undo	136 ms
cycle	325	src/Rogue/Tests/PlayThrough.sw	edit	1311 ms
cycle	326	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	327	src/Rogue/Tests/PlayThrough.sw	edit	1294 ms
cycle	328	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	329	src/Rogue/Tests/PlayThrough.sw	edit	1289 ms
cycle	330	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
sample	cycle 330	rss_kb 1851152	heap_bytes 333625843
cycle	331	src/Rogue/Tests/PlayThrough.sw	edit	1304 ms
cycle	332	src/Rogue/Tests/PlayThrough.sw	undo	132 ms
cycle	333	src/Rogue/Tests/PlayThrough.sw	edit	1272 ms
cycle	334	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	335	src/Rogue/Tests/PlayThrough.sw	edit	1288 ms
cycle	336	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	337	src/Rogue/Tests/PlayThrough.sw	edit	1316 ms
cycle	338	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	339	src/Rogue/Tests/PlayThrough.sw	edit	1280 ms
cycle	340	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
sample	cycle 340	rss_kb 1972752	heap_bytes 333690823
cycle	341	src/Rogue/Tests/PlayThrough.sw	edit	1275 ms
cycle	342	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	343	src/Rogue/Tests/PlayThrough.sw	edit	1277 ms
cycle	344	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	345	src/Rogue/Tests/PlayThrough.sw	edit	1274 ms
cycle	346	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	347	src/Rogue/Tests/PlayThrough.sw	edit	1277 ms
cycle	348	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	349	src/Rogue/Tests/PlayThrough.sw	edit	1292 ms
cycle	350	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
sample	cycle 350	rss_kb 1911952	heap_bytes 333755803
cycle	351	src/Rogue/Tests/PlayThrough.sw	edit	1275 ms
cycle	352	src/Rogue/Tests/PlayThrough.sw	undo	132 ms
cycle	353	src/Rogue/Tests/PlayThrough.sw	edit	1273 ms
cycle	354	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	355	src/Rogue/Tests/PlayThrough.sw	edit	1276 ms
cycle	356	src/Rogue/Tests/PlayThrough.sw	undo	133 ms
cycle	357	src/Rogue/Tests/PlayThrough.sw	edit	1280 ms
cycle	358	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	359	src/Rogue/Tests/PlayThrough.sw	edit	1277 ms
cycle	360	src/Rogue/Tests/PlayThrough.sw	undo	133 ms
sample	cycle 360	rss_kb 1863328	heap_bytes 333820783
cycle	361	src/Rogue/Tests/PlayThrough.sw	edit	1274 ms
cycle	362	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	363	src/Rogue/Tests/PlayThrough.sw	edit	1275 ms
cycle	364	src/Rogue/Tests/PlayThrough.sw	undo	138 ms
cycle	365	src/Rogue/Tests/PlayThrough.sw	edit	1324 ms
cycle	366	src/Rogue/Tests/PlayThrough.sw	undo	142 ms
cycle	367	src/Rogue/Tests/PlayThrough.sw	edit	1356 ms
cycle	368	src/Rogue/Tests/PlayThrough.sw	undo	140 ms
cycle	369	src/Rogue/Tests/PlayThrough.sw	edit	1360 ms
cycle	370	src/Rogue/Tests/PlayThrough.sw	undo	137 ms
sample	cycle 370	rss_kb 1814688	heap_bytes 333885763
cycle	371	src/Rogue/Tests/PlayThrough.sw	edit	1314 ms
cycle	372	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	373	src/Rogue/Tests/PlayThrough.sw	edit	1354 ms
cycle	374	src/Rogue/Tests/PlayThrough.sw	undo	140 ms
cycle	375	src/Rogue/Tests/PlayThrough.sw	edit	1356 ms
cycle	376	src/Rogue/Tests/PlayThrough.sw	undo	139 ms
cycle	377	src/Rogue/Tests/PlayThrough.sw	edit	1351 ms
cycle	378	src/Rogue/Tests/PlayThrough.sw	undo	139 ms
cycle	379	src/Rogue/Tests/PlayThrough.sw	edit	1336 ms
cycle	380	src/Rogue/Tests/PlayThrough.sw	undo	140 ms
sample	cycle 380	rss_kb 1936400	heap_bytes 333330715
cycle	381	src/Rogue/Tests/PlayThrough.sw	edit	1314 ms
cycle	382	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	383	src/Rogue/Tests/PlayThrough.sw	edit	1302 ms
cycle	384	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	385	src/Rogue/Tests/PlayThrough.sw	edit	1276 ms
cycle	386	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	387	src/Rogue/Tests/PlayThrough.sw	edit	1276 ms
cycle	388	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	389	src/Rogue/Tests/PlayThrough.sw	edit	1276 ms
cycle	390	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
sample	cycle 390	rss_kb 1899920	heap_bytes 333397231
cycle	391	src/Rogue/Tests/PlayThrough.sw	edit	1277 ms
cycle	392	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	393	src/Rogue/Tests/PlayThrough.sw	edit	1275 ms
cycle	394	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	395	src/Rogue/Tests/PlayThrough.sw	edit	1281 ms
cycle	396	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	397	src/Rogue/Tests/PlayThrough.sw	edit	1301 ms
cycle	398	src/Rogue/Tests/PlayThrough.sw	undo	132 ms
cycle	399	src/Rogue/Tests/PlayThrough.sw	edit	1280 ms
cycle	400	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
sample	cycle 400	rss_kb 1851296	heap_bytes 333462211
cycle	401	src/Rogue/Tests/PlayThrough.sw	edit	1302 ms
cycle	402	src/Rogue/Tests/PlayThrough.sw	undo	132 ms
cycle	403	src/Rogue/Tests/PlayThrough.sw	edit	1313 ms
cycle	404	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	405	src/Rogue/Tests/PlayThrough.sw	edit	1312 ms
cycle	406	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	407	src/Rogue/Tests/PlayThrough.sw	edit	1272 ms
cycle	408	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	409	src/Rogue/Tests/PlayThrough.sw	edit	1292 ms
cycle	410	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
sample	cycle 410	rss_kb 1972896	heap_bytes 333527191
cycle	411	src/Rogue/Tests/PlayThrough.sw	edit	1274 ms
cycle	412	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	413	src/Rogue/Tests/PlayThrough.sw	edit	1286 ms
cycle	414	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	415	src/Rogue/Tests/PlayThrough.sw	edit	1270 ms
cycle	416	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	417	src/Rogue/Tests/PlayThrough.sw	edit	1305 ms
cycle	418	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	419	src/Rogue/Tests/PlayThrough.sw	edit	1273 ms
cycle	420	src/Rogue/Tests/PlayThrough.sw	undo	132 ms
sample	cycle 420	rss_kb 1912096	heap_bytes 333595243
cycle	421	src/Rogue/Tests/PlayThrough.sw	edit	1283 ms
cycle	422	src/Rogue/Tests/PlayThrough.sw	undo	135 ms
cycle	423	src/Rogue/Tests/PlayThrough.sw	edit	1285 ms
cycle	424	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	425	src/Rogue/Tests/PlayThrough.sw	edit	1276 ms
cycle	426	src/Rogue/Tests/PlayThrough.sw	undo	133 ms
cycle	427	src/Rogue/Tests/PlayThrough.sw	edit	1291 ms
cycle	428	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	429	src/Rogue/Tests/PlayThrough.sw	edit	1274 ms
cycle	430	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
sample	cycle 430	rss_kb 1863456	heap_bytes 333660223
cycle	431	src/Rogue/Tests/PlayThrough.sw	edit	1275 ms
cycle	432	src/Rogue/Tests/PlayThrough.sw	undo	133 ms
cycle	433	src/Rogue/Tests/PlayThrough.sw	edit	1308 ms
cycle	434	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	435	src/Rogue/Tests/PlayThrough.sw	edit	1291 ms
cycle	436	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	437	src/Rogue/Tests/PlayThrough.sw	edit	1274 ms
cycle	438	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	439	src/Rogue/Tests/PlayThrough.sw	edit	1280 ms
cycle	440	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
sample	cycle 440	rss_kb 1985056	heap_bytes 333725203
cycle	441	src/Rogue/Tests/PlayThrough.sw	edit	1281 ms
cycle	442	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	443	src/Rogue/Tests/PlayThrough.sw	edit	1273 ms
cycle	444	src/Rogue/Tests/PlayThrough.sw	undo	134 ms
cycle	445	src/Rogue/Tests/PlayThrough.sw	edit	1288 ms
cycle	446	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
cycle	447	src/Rogue/Tests/PlayThrough.sw	edit	1274 ms
cycle	448	src/Rogue/Tests/PlayThrough.sw	undo	130 ms
cycle	449	src/Rogue/Tests/PlayThrough.sw	edit	1273 ms
cycle	450	src/Rogue/Tests/PlayThrough.sw	undo	131 ms
sample	cycle 450	rss_kb 1936432	heap_bytes 333790183
final	cycle 450	rss_kb 1936432	heap_bytes 333777218
latency	src/Rogue/Model.sw	edit	n 25	median 775 ms	p95 1655 ms
latency	src/Rogue/Model.sw	undo	n 25	median 3182 ms	p95 5808 ms
latency	src/Rogue/Proofs/Loop.sw	edit	n 75	median 2240 ms	p95 5730 ms
latency	src/Rogue/Proofs/Loop.sw	undo	n 75	median 301 ms	p95 563 ms
latency	src/Rogue/Tests/PlayThrough.sw	edit	n 125	median 1315 ms	p95 1351 ms
latency	src/Rogue/Tests/PlayThrough.sw	undo	n 125	median 135 ms	p95 139 ms
journal	(no JournalStats before step 6a)
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 35 filtered out; finished in 543.86s

```
load end: 4.62, 13.85, 19.20

## Command line: stitchwort check on aoc
load start: 4.62, 13.85, 19.20

| mode | user CPU s | wall s | peak RSS MB |
|---|---|---|---|
| cold --no-cache #1 | 58.52 | 59.20 | 1535 |
| cold --no-cache #2 | 58.42 | 59.04 | 1535 |
| cold, empty cache folder #1 | 59.66 | 60.36 | 1570 |
| cold, empty cache folder #2 | 59.96 | 60.67 | 1569 |
| warm #1 | 2.92 | 3.27 | 669 |
| warm #2 | 2.87 | 3.07 | 669 |
| mixed, Aoc.Year2024.Day10 edited #1 | 3.09 | 3.26 | 671 |
| mixed, Aoc.Year2024.Day10 edited #2 | 3.04 | 3.24 | 671 |
load end: 2.81, 7.25, 14.85

## Mark and rewind on aoc
load start: 2.81, 7.25, 14.85
```
    Finished `release` profile [optimized] target(s) in 0.08s
     Running tests/rewind.rs (target/release/deps/rewind-6b16ef020c039ebc)

running 1 test
test mark_and_rewind_cost_alone ... aoc with navigation: mark 1.05 ms, rewind to it 1.43 ms, rewind to the start 248.24 ms
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 4 filtered out; finished in 91.52s

```
```
    Finished `release` profile [optimized] target(s) in 0.07s
     Running tests/rewind.rs (target/release/deps/rewind-6b16ef020c039ebc)

running 1 test
test mark_and_rewind_cost_alone ... aoc with navigation: mark 1.13 ms, rewind to it 1.32 ms, rewind to the start 241.38 ms
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 4 filtered out; finished in 73.65s

```
load end: 5.11, 7.66, 13.77

load finish: 5.11, 7.66, 13.77
