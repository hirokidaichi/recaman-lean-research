# Arc trace probe: how the deep arcs of the canonical Recaman orbit descend and what stops them

Date: 2026-09-02. Tool: `experiments/arc_trace_probe.cpp` (new file; plain step simulator with the interval-set history of `run_length_recaman_simulator.cpp`). Runs: horizon 3e9 (64 s) and horizon 1e10 (213 s), outputs in `h3e9/` and `h1e10/` of this directory. All numbers below are from the 1e10 run; the 3e9 run produced an identical arc table on the 37 arcs both runs completed.

## 1. Definitions used (exact)

- Orbit: a(0) = 0, history {0}. At clock n >= 1 the candidate is a(n-1) - n; subtract iff a(n-1) > n and the candidate is not in the history, else add n.
- Quotient/residue: a(n) = k(n) * n + r(n) with 0 <= r(n) < n, so r(n) = a(n) mod n. Height h(n) = a(n) - n (signed). k = 0 means a(n) < n (late landing, always a subtraction); k = 1 means 0 <= h < n and h = r; k >= 2 means h >= n.
- Algebra behind the arc detector: a(n) +- (n+1) = (k(n) +- 1)(n+1) + (r(n) - k(n)). Both step types send r to r - k as long as r >= k; when r < k the residue wraps to r - k + n + 1 (an increase). An arc (Chaffin, A393814/A393815) is the stretch between two consecutive increases of r; the wrap clock is the first clock of the next arc. The landing of an arc is its minimum value, the landing index the first clock attaining it. Since r is nonincreasing inside an arc, the landing of every arc containing a k = 0 clock is its last k = 0 clock (verified: landingIndex = lastLateClock for all 39 arcs in `arcs_all.txt`).
- Deep arc: landing value * 10000 < landing index (depth log10(index/value) > 4).
- Late landing: a(n) < n (k = 0). Band landing: a subtraction with a(n) >= n.
- Trace start (a deviation from the literal request, stated exactly): the trace of an arc starts at the first clock of the arc with r(n) * 1000 < n. At k = 1 clocks this is exactly h(n) < n/1000. The literal condition h < n/1000 also holds at every late landing, including those with a(n) ~ n/2: 28 % of all clocks are late landings (sub-diagonal count 2.63e9 of 9e9 clocks in [1e9, 1e10)), and every arc begins with r ~ n and lands values just below the diagonal, so the literal rule would have traced whole arcs (up to 3.5e9 clocks). With the residue rule the trace covers the final descent only, and because r is nonincreasing the trace never stops before the arc ends. "Traced late landings" are exactly the late landings with a(n) < n/1000.
- Trace markers: `UP` = k >= 2 immediately after a record with k <= 1 (the height jumps from below n/1000 to at least n); `POP` = k >= 3 (the orbit has left the k = 1/2 ping-pong band by two consecutive additions).

## 2. Validation

- The first 19 landings reproduce the checkpoint list exactly: 1=1 2=3 4=2 10=11 16=8 31=14 64=26 131=4 222=47 403=92 770=111 1409=181 2652=150 4825=371 9078=361 16773=781 30768=828 56827=366 99734=19 (`summary.txt`: `checkpoint(first 19 landings) PASS`, both runs).
- Chaffin's table lists four landings with value < 1e7 and index in [1e9, 1e10): 2426 at 10^9.21, 2405 at 10^9.45, 89386 at 10^9.69, 110522 at 10^9.93. The probe finds 1610186343=2426 (log10 index 9.20688), 2789149734=2405 (9.44547), 4910724199=89386 (9.69115), 8416516444=110522 (9.92513), and no other landing with value < 1e7 in that range.
- `verify.py` check 3: the 3e9 and 1e10 arc tables are identical on the 37 common arcs.
- State at 1e10: value 16705983634, 105347 intervals, mex 1355 (1355 first appears at index 3.25e11, consistent).

## 3. Deep arcs found (6 of 39 completed arcs up to 1e10)

| arc | clocks of the arc | landing index | landing value | depth log10(i/v) | late landings in the arc (k=0 clocks) | traced late landings (a(n) < n/1000) | traced clocks k=0/1/2/3+ | steps from landing to arc end | how the arc ends |
|---|---|---|---|---|---|---|---|---|---|
| 30 | 32148795..58056875 | 58055311 | 4202 | 4.140 | 7316473 | 21 | 21/11691/11681/6449 | 1564 | residue exhausted in a k=1/2 ping-pong: wrap at k=2, r=0 (a = 2n exactly); next arc starts with a(58056876) = 58056874 = n-2 |
| 35 | 511561221..904036924 | 904032692 | 14804 | 4.786 | 111017793 | 581 | 581/160859/166209/117721 | 4232 | residue exhausted in a k=3/4 ping-pong: wrap at k=4, r=0; next arc starts at k=2 |
| 36 | 904036925..1610187038 | 1610186343 | 2426 | 5.822 | 202844334 | 1343 | 1343/237179/298492/229871 | 695 | residue exhausted in a k=3/4 ping-pong: wrap at k=3, r=1; next arc starts at k=3 |
| 37 | 1610187039..2789150423 | 2789149734 | 2405 | 6.064 | 327754080 | 952 | 952/509793/508923/351370 | 689 | residue exhausted in a k=3/4 ping-pong: wrap at k=3, r=1; next arc starts at k=3 |
| 38 | 2789150424..4910758397 | 4910724199 | 89386 | 4.740 | 602335220 | 3031 | 3031/622929/644396/803560 | 34198 | residue exhausted in a k=2/3 ping-pong: wrap at k=2, r=1; next arc starts at k=2 |
| 39 | 4910758398..8416580354 | 8416516444 | 110522 | 4.882 | 958574394 | 4477 | 4477/1479963/1522841/1089231 | 63910 | residue exhausted in a k=1/2 ping-pong: wrap at k=2, r=1; next arc starts with a(8416580355) = 8416580354 = n-1 |

In all six deep arcs the landing is the last late landing of the arc; the descent of late landings is stopped by the same local event in all six (Section 4c). The arc itself ends 689..63910 steps later, when the residue has been counted down to r < k.

Post-landing structure (`verify.py` check 2; a segment is a maximal stretch of alternating S/A steps, i.e. one ping-pong level; a level change is two consecutive additions or two consecutive subtractions):

| arc landing | steps to wrap | k histogram after the landing | segments after the landing (offset: length, k) | AA / SS pairs after the landing |
|---|---|---|---|---|
| 58055311=4202 | 1564 | k1:317 k2:318 k3:465 k4:464 | +1 k=1; +2 k=2; +3 k=3; +4: 928 steps k=3/4; +932 k=2; +933: 632 steps k=1/2 (to the wrap) | 3 / 2 |
| 904032692=14804 | 4232 | k1:1 k2:1 k3:2115 k4:2115 | +1 k=1; +2 k=2; +3 k=3; +4: 4229 steps k=3/4 (to the wrap) | 3 / 0 |
| 1610186343=2426 | 695 | k1:1 k2:1 k3:347 k4:346 | +1 k=1; +2 k=2; +3 k=3; +4: 692 steps k=3/4 (to the wrap) | 3 / 0 |
| 2789149734=2405 | 689 | k1:1 k2:1 k3:344 k4:343 | +1 k=1; +2 k=2; +3 k=3; +4: 686 steps k=3/4 (to the wrap) | 3 / 0 |
| 4910724199=89386 | 34198 | k1:5635 k2:9518 k3:11464 k4:7581 | +1 k=1; +2 k=2; +3 k=3; +4: 11406 steps k=3/4; +11410 k=2; +11411: 11268 steps k=1/2; +22679 k=3; +22680: 3756 steps k=3/4; +26436: 7763 steps k=2/3 (to the wrap) | 5 / 3 |
| 8416516444=110522 | 63910 | k1:28290 k2:28291 k3:3665 k4:3664 | +1 k=1; +2 k=2; +3 k=3; +4: 7328 steps k=3/4; +7332 k=2; +7333: 56578 steps k=1/2 (to the wrap) | 3 / 2 |

## 4. Answers (counts over the 10405 traced late landings of the 6 deep arcs)

### (a) The next 8 orbit values after a late landing at value v (clock c)

Step-type pattern of clocks c+1..c+8 (A = addition, B = subtraction landing a value >= clock, L = subtraction landing a value < clock = late landing):

| pattern | count | values a(c+1..c+8) in terms of c, v | which are landings (subtractions) |
|---|---|---|---|
| ALALALAL | 10028 | c+v+1, v-1, c+v+2, v-2, c+v+3, v-3, c+v+4, v-4 | late landings at +2,+4,+6,+8 (values v-1..v-4); the additions sit at k=1 with h = v, v-1, v-2, v-3 |
| AAAABABA | 127 | c+v+1, 2c+v+3, 3c+v+6, 4c+v+10, 3c+v+5, 4c+v+11, 3c+v+4, 4c+v+12 | band landings at +5, +7 (k=3); no late landing |
| ALAAAABA | 47 | comb of length 2 (v-1 at +2), then as AAAABABA shifted by two clocks | late at +2; band at +7 |
| AAABBABA | 45 | c+v+1, 2c+v+3, 3c+v+6, 2c+v+2, c+v-3, 2c+v+3 (revisit of a(c+2) by addition), c+v-4, 2c+v+4 | band landings at +4 (k=2), +5 (k=1, h=v-8), +7 (k=1, h=v-11) |
| ALALALAA | 45 | comb of length 4, blocked at +8 | late at +2,+4,+6 |
| ALALAAAA | 36 | comb of length 3, blocked at +6, pop-up | late at +2,+4 |
| AAAAABAB | 31 | pop-up through k=5 (5c+v+15 at +5), then a k=4/5 ping-pong | band at +6, +8 (k=4) |
| ALAAAAAB | 10 | comb of length 2, pop-up through k=5 | late at +2; band at +8 |
| ALALAAAB | 9 | comb of length 3, blocked at +6, pop-up to k=3 at +7, k=3->2 subtraction at +8 | late at +2,+4; band at +8 (k=2) |
| ALAAABAB | 9 | comb of length 2, then a k=2/3 ping-pong | late at +2; band at +6,+8 |
| AAABABAB | 8 | c+v+1, 2c+v+3, 3c+v+6, 2c+v+2, 3c+v+7, 2c+v+1, 3c+v+8, 2c+v | band at +4,+6,+8 (k=2): a k=2/3 ping-pong |
| ALAAABBA | 8 | comb of length 2, then as AAABBABA | late at +2; band at +6,+7 |
| AAABABBA | 1 | k=2/3 ping-pong for two pairs, then k=1 at +7 | band at +4,+6,+7 |
| AAAAAABA | 1 | pop-up through k=6 | band at +7 |

The formulas are the step rule applied to the pattern; they agree with the printed values of the six arc landings (e.g. 2789149734=2405: 2789152140, 5578301876, 8367451613, 11156601351, 8367451612, 11156601352, 8367451611, 11156601353 = c+v+1, 2c+v+3, 3c+v+6, 4c+v+10, 3c+v+5, 4c+v+11, 3c+v+4, 4c+v+12).

The next 8 values after the landing of each deep arc:

| landing | next 8 values | types |
|---|---|---|
| 58055311=4202 | 58059514, 116114827, 174170141, 232225456, 174170140, 232225457, 174170139, 232225458 | AAAABABA |
| 904032692=14804 | 904047497, 1808080191, 2712112886, 3616145582, 2712112885, 3616145583, 2712112884, 3616145584 | AAAABABA |
| 1610186343=2426 | 1610188770, 3220375115, 4830561461, 6440747808, 4830561460, 6440747809, 4830561459, 6440747810 | AAAABABA |
| 2789149734=2405 | 2789152140, 5578301876, 8367451613, 11156601351, 8367451612, 11156601352, 8367451611, 11156601353 | AAAABABA |
| 4910724199=89386 | 4910813586, 9821537787, 14732261989, 19642986192, 14732261988, 19642986193, 14732261987, 19642986194 | AAAABABA |
| 8416516444=110522 | 8416626967, 16833143413, 25249659860, 33666176308, 25249659859, 33666176309, 25249659858, 33666176310 | AAAABABA |

Two exact facts checked on every traced late landing:

- "value-1 is a hole at the landing" <=> "the +2 step is a late landing (the comb continues)": 10405 of 10405 agree (10192 comb continuations, 213 comb ends). This is the step rule: a(c+1) = c+v+1 > c+2 and the candidate at c+2 is v-1.
- At every comb end (late landing v' at clock c' with v'-1 visited; 213 cases): the +3 candidate is 2(c'+2) + v' - 1 - (c'+3) = c' + v' = a(c'-1), the value the orbit left when it landed v'. It is therefore always visited, the +3 step is always an addition, and the orbit always pops to k = 3 (a(c'+3) = 3c'+v'+6). `verify.py` check 1: 213 of 213 comb ends have the +3 step = addition with blocked candidate equal to a(c'-1); 0 violations.

### (b) Is there a later clock in the same arc with 0 < h < v, or does the orbit pop back up?

Height at +2: in 10192 cases the +2 value is the late landing v-1 (h < 0); in 213 cases (all comb ends) a(c+2) = 2(c+2) + v - 1, i.e. h = c + v + 1 (height about the clock, k = 2).

First later clock of the same arc with 0 < h < v:

| when | h there | count |
|---|---|---|
| +3 | v-1 | 10192 (the comb continued at +2; the forced addition at +3 sits at height v-1) |
| +5 | v-8 | 45 (comb end; the k=3->2 candidate 2c+v+2 was fresh at +4 and the k=2->1 candidate c+v-3 was fresh at +5: pattern AAABB...) |
| +7 .. +261313 | v-13 .. (drops up to tens of thousands) | 165 (comb end followed by a pop-up to k >= 3 at +3 and a stay at k >= 2 through at least +6; the orbit returned to a k = 1 clock with h < v only at offset >= 7; smallest offsets: +7 (h=v-13), +15 (v-33), +49 (v-118), +59 (v-143, 2 cases), +71 (v-303); largest: +261313) |
| never (arc ended first) | - | 3 (the landings of arcs 35, 36, 37: the arc ended inside the k=3/4 ping-pong) |

Total: found 10402, none 3. After a traced late landing the descent continues at small heights within 5 clocks in 10237 of 10405 cases; in 165 cases only at offset >= 7 after a pop-up to k >= 3; in 3 cases never. For the six arc landings themselves none continued within 5 clocks (all six are comb ends followed by AAAA, i.e. the k=3->2 candidate 2c+v+2 was also visited); three returned to k = 1 later, three never:

| arc landing (clock=value) | value-1 hole? | first later clock of the arc with 0<h<v | h there |
|---|---|---|---|
| 58055311=4202 | visited | 58056244 (+933) | 946 = v-3256 |
| 904032692=14804 | visited | never | - |
| 1610186343=2426 | visited | never | - |
| 2789149734=2405 | visited | never | - |
| 4910724199=89386 | visited | 4910735610 (+11411) | 49457 = v-39929 |
| 8416516444=110522 | visited | 8416523777 (+7333) | 84866 = v-25656 |

### (c) How each deep arc ends

Terminal event of the descent (identical in 6 of 6 deep arcs): the landing v at clock c is a comb end (v-1 visited: 6/6); the forced addition at +1 gives c+v+1; the addition at +2 gives 2c+v+3; the band candidate at +3 equals a(c-1) = c+v and is blocked (6/6, forced by the identity above); the orbit pops to k = 3 (3c+v+6); the k=3->2 candidate 2c+v+2 at +4 is also blocked (6/6); the orbit enters a k=3/4 ping-pong (lower values 3c+v+5, 3c+v+4, ... descending, upper values 4c+v+11, 4c+v+12, ... ascending, r decreasing by 7 per pair). In the task's vocabulary this is "a late landing followed by a pop-up" in 6/6 cases, the pop-up being two additions in a row at +2, +3 (and a third at +4). No deep arc ends by a band-value block inside a k=1/2 ping-pong right after the landing (that would be the pattern AAABB... at the landing; it occurred at 45 of the 213 comb ends, at none of the 6 arc landings).

Formal end of the arc (residue wrap, r < k): 689..63910 steps after the landing, with no further late landing. Where the wrap happened: inside the k=3/4 ping-pong entered at +4 (arcs 35, 36, 37: 3 arcs; wraps at k=4 r=0, k=3 r=1, k=3 r=1); inside a k=1/2 ping-pong after coming back down (arcs 30, 39: 2 arcs; wraps at k=2 r=0 and k=2 r=1); inside a k=2/3 ping-pong (arc 38: 1 arc; wrap at k=2 r=1). The last subtraction of every deep arc is a fresh band landing; the last 16 records of each deep arc are in `h1e10/deep_arcs.txt`. Two-additions-in-a-row events after the landing: 3 (arcs 30, 35, 36, 37, 39) or 5 (arc 38); two-subtractions-in-a-row events: 0 (arcs 35, 36, 37), 2 (arcs 30, 39), 3 (arc 38).

### (d) The late-landing values inside each deep arc, with residues mod 3

The 10405 traced late landings of the six deep arcs fall into 213 comb runs (a run = values decreasing by 1 every 2 clocks; a run continues exactly while value-1 is a hole). Run lengths: 139 runs of length 1, 29 of length 2, 45 runs of length 4..2411 (longest: 2411 in arc 39, 898 in arc 36, 739 in arc 38, 724 and 582 in arc 39, 537 in arc 38, 434 in arc 38, 402 in arc 35). Values mod 3 over all 10405: 0: 3462, 1: 3461, 2: 3482. First value of a run mod 3: 0: 67, 1: 65, 2: 81. Difference between consecutive run-first values mod 3: 0: 69, 1: 80, 2: 58. The six landing values mod 3: 4202 -> 2, 14804 -> 2, 2426 -> 2, 2405 -> 2, 89386 -> 1, 110522 -> 2. The complete per-arc run tables (clocks, values, count, value mod 3 of the first and last value of the run, whether value-1 was a hole at the first landing of the run):


**arc landing 58055311=4202: 21 traced late landings in 5 comb runs (a run = values decreasing by 1 every 2 clocks)**

| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |
|---|---|---|---|---|---|
| 1 | 58030879 | 51032 | 1 | 2 | visited |
| 2 | 58031939 | 49442 | 1 | 2 | visited |
| 3 | 58032091..58032121 | 49214..49199 | 16 | 2..2 | hole |
| 4 | 58047425..58047427 | 26233..26232 | 2 | 1..0 | hole |
| 5 | 58055311 | 4202 | 1 | 2 | visited |

Run-first values mod 3: 2,2,2,1,2
Differences between consecutive run-first values mod 3: 0,0,1,2
Mod-3 distribution of all traced late-landing values: {2: 9, 1: 6, 0: 6}
below-hole at traced late landings: {'visited': 5, 'hole': 16}

**arc landing 904032692=14804: 581 traced late landings in 18 comb runs (a run = values decreasing by 1 every 2 clocks)**

| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |
|---|---|---|---|---|---|
| 1 | 903615832..903615930 | 867176..867127 | 50 | 2..1 | hole |
| 2 | 903739884 | 613492 | 1 | 1 | visited |
| 3 | 903755518 | 568573 | 1 | 1 | visited |
| 4 | 903774658 | 527673 | 1 | 0 | visited |
| 5 | 903809014..903809016 | 475171..475170 | 2 | 1..0 | hole |
| 6 | 903842440 | 397202 | 1 | 2 | visited |
| 7 | 903878266 | 334747 | 1 | 1 | visited |
| 8 | 903897118..903897178 | 282725..282695 | 31 | 2..2 | hole |
| 9 | 903935484..903935486 | 221380..221379 | 2 | 1..0 | hole |
| 10 | 903954316 | 168874 | 1 | 1 | visited |
| 11 | 903962212..903963014 | 152562..152161 | 402 | 0..1 | hole |
| 12 | 903974216 | 129978 | 1 | 0 | visited |
| 13 | 903982818 | 111399 | 1 | 0 | visited |
| 14 | 903988010 | 99767 | 1 | 2 | visited |
| 15 | 903991636..903991798 | 92144..92063 | 82 | 2..2 | hole |
| 16 | 903993146 | 88025 | 1 | 2 | visited |
| 17 | 904012796 | 57520 | 1 | 1 | visited |
| 18 | 904032692 | 14804 | 1 | 2 | visited |

Run-first values mod 3: 2,1,1,0,1,2,1,2,1,1,0,0,0,2,2,2,1,2
Differences between consecutive run-first values mod 3: 1,0,1,2,2,1,2,1,0,1,0,0,1,0,0,1,2
Mod-3 distribution of all traced late-landing values: {2: 194, 1: 195, 0: 192}
below-hole at traced late landings: {'hole': 563, 'visited': 18}

**arc landing 1610186343=2426: 1343 traced late landings in 33 comb runs (a run = values decreasing by 1 every 2 clocks)**

| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |
|---|---|---|---|---|---|
| 1 | 1609443239 | 1574792 | 1 | 2 | visited |
| 2 | 1609550543..1609552337 | 1381884..1380987 | 898 | 0..0 | hole |
| 3 | 1609657181 | 1159245 | 1 | 0 | visited |
| 4 | 1609692505 | 1057851 | 1 | 0 | visited |
| 5 | 1609727061..1609727481 | 969193..968983 | 211 | 1..1 | hole |
| 6 | 1609728903..1609728985 | 965046..965005 | 42 | 0..1 | hole |
| 7 | 1609729485..1609729625 | 963743..963673 | 71 | 2..1 | hole |
| 8 | 1609729853..1609729931 | 962887..962848 | 40 | 1..1 | hole |
| 9 | 1609734783 | 955406 | 1 | 2 | visited |
| 10 | 1609840991..1609841075 | 697072..697030 | 43 | 1..1 | hole |
| 11 | 1609892815 | 613396 | 1 | 1 | visited |
| 12 | 1609916737..1609916739 | 545025..545024 | 2 | 0..2 | hole |
| 13 | 1609925071 | 527402 | 1 | 2 | visited |
| 14 | 1609928513 | 518391 | 1 | 0 | visited |
| 15 | 1609957287..1609957289 | 474214..474213 | 2 | 1..0 | hole |
| 16 | 1609982119..1609982135 | 418116..418108 | 9 | 0..1 | hole |
| 17 | 1609990087 | 395876 | 1 | 2 | visited |
| 18 | 1609991401 | 392037 | 1 | 0 | visited |
| 19 | 1610023797 | 343187 | 1 | 2 | visited |
| 20 | 1610039709 | 297803 | 1 | 2 | visited |
| 21 | 1610047467 | 282726 | 1 | 0 | visited |
| 22 | 1610076605 | 221601 | 1 | 0 | visited |
| 23 | 1610077893..1610077895 | 218621..218620 | 2 | 2..1 | hole |
| 24 | 1610095223 | 192628 | 1 | 1 | visited |
| 25 | 1610104013 | 167887 | 1 | 1 | visited |
| 26 | 1610105431 | 163124 | 1 | 2 | visited |
| 27 | 1610112195 | 152674 | 1 | 1 | visited |
| 28 | 1610129373 | 122463 | 1 | 0 | visited |
| 29 | 1610142937 | 92145 | 1 | 0 | visited |
| 30 | 1610166969 | 50377 | 1 | 1 | visited |
| 31 | 1610175617 | 23289 | 1 | 0 | visited |
| 32 | 1610178287 | 14510 | 1 | 2 | visited |
| 33 | 1610186343 | 2426 | 1 | 2 | visited |

Run-first values mod 3: 2,0,0,0,1,0,2,1,2,1,1,0,2,0,1,0,2,0,2,2,0,0,2,1,1,2,1,0,0,1,0,2,2
Differences between consecutive run-first values mod 3: 2,0,0,2,1,1,1,2,1,0,1,1,2,2,1,1,2,1,0,2,0,1,1,0,2,1,1,0,2,1,1,0
Mod-3 distribution of all traced late-landing values: {2: 448, 0: 448, 1: 447}
below-hole at traced late landings: {'visited': 33, 'hole': 1310}

**arc landing 2789149734=2405: 952 traced late landings in 44 comb runs (a run = values decreasing by 1 every 2 clocks)**

| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |
|---|---|---|---|---|---|
| 1 | 2787920370 | 2552293 | 1 | 1 | visited |
| 2 | 2787990060 | 2359098 | 1 | 0 | visited |
| 3 | 2788001202 | 2325477 | 1 | 0 | visited |
| 4 | 2788019876 | 2289398 | 1 | 2 | visited |
| 5 | 2788174444..2788174446 | 2043796..2043795 | 2 | 1..0 | hole |
| 6 | 2788224406..2788224408 | 1869055..1869054 | 2 | 1..0 | hole |
| 7 | 2788247504 | 1834214 | 1 | 2 | visited |
| 8 | 2788287988..2788288230 | 1758132..1758011 | 122 | 0..2 | hole |
| 9 | 2788325640 | 1679540 | 1 | 2 | visited |
| 10 | 2788347668 | 1629006 | 1 | 0 | visited |
| 11 | 2788508168..2788508250 | 1379400..1379359 | 42 | 0..1 | hole |
| 12 | 2788585590..2788585708 | 1159133..1159074 | 60 | 2..0 | hole |
| 13 | 2788669126 | 1016887 | 1 | 1 | visited |
| 14 | 2788694276 | 929234 | 1 | 2 | visited |
| 15 | 2788700624 | 919150 | 1 | 1 | visited |
| 16 | 2788713776 | 880938 | 1 | 0 | visited |
| 17 | 2788714084 | 880476 | 1 | 0 | visited |
| 18 | 2788716254 | 877221 | 1 | 0 | visited |
| 19 | 2788716830 | 876357 | 1 | 0 | visited |
| 20 | 2788717458 | 875415 | 1 | 0 | visited |
| 21 | 2788722950 | 867177 | 1 | 0 | visited |
| 22 | 2788725664 | 863106 | 1 | 0 | visited |
| 23 | 2788732632 | 852654 | 1 | 0 | visited |
| 24 | 2788794596..2788794792 | 755060..754962 | 99 | 2..0 | hole |
| 25 | 2788862008 | 612178 | 1 | 1 | visited |
| 26 | 2788883288 | 545354 | 1 | 2 | visited |
| 27 | 2788887652..2788887658 | 527320..527317 | 4 | 1..1 | hole |
| 28 | 2788887794..2788887796 | 527111..527110 | 2 | 2..1 | hole |
| 29 | 2788923244..2788923346 | 473938..473887 | 52 | 1..1 | hole |
| 30 | 2788944520 | 418286 | 1 | 2 | visited |
| 31 | 2788955454..2788955676 | 395713..395602 | 112 | 1..1 | hole |
| 32 | 2788967810 | 371637 | 1 | 0 | visited |
| 33 | 2788982926 | 342791 | 1 | 2 | visited |
| 34 | 2788999720 | 309576 | 1 | 0 | visited |
| 35 | 2789003988..2789004018 | 294650..294635 | 16 | 2..2 | hole |
| 36 | 2789004508..2789005098 | 293496..293201 | 296 | 0..2 | hole |
| 37 | 2789064242 | 192049 | 1 | 1 | visited |
| 38 | 2789086212 | 123374 | 1 | 2 | visited |
| 39 | 2789098808 | 92146 | 1 | 1 | visited |
| 40 | 2789098874..2789099096 | 92047..91936 | 112 | 1..1 | hole |
| 41 | 2789100522 | 89723 | 1 | 2 | visited |
| 42 | 2789105306 | 82547 | 1 | 2 | visited |
| 43 | 2789120768 | 59354 | 1 | 2 | visited |
| 44 | 2789149734 | 2405 | 1 | 2 | visited |

Run-first values mod 3: 1,0,0,2,1,1,2,0,2,0,0,2,1,2,1,0,0,0,0,0,0,0,0,2,1,2,1,2,1,2,1,0,2,0,2,0,1,2,1,1,2,2,2,2
Differences between consecutive run-first values mod 3: 1,0,1,1,0,2,2,1,2,0,1,1,2,1,1,0,0,0,0,0,0,0,1,1,2,1,2,1,2,1,1,1,2,1,2,2,2,1,0,2,0,0,0
Mod-3 distribution of all traced late-landing values: {1: 315, 0: 319, 2: 318}
below-hole at traced late landings: {'visited': 44, 'hole': 908}

**arc landing 4910724199=89386: 3031 traced late landings in 47 comb runs (a run = values decreasing by 1 every 2 clocks)**

| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |
|---|---|---|---|---|---|
| 1 | 4908711669..4908711921 | 4861669..4861543 | 127 | 1..1 | hole |
| 2 | 4908972613 | 4453341 | 1 | 0 | visited |
| 3 | 4909080573 | 4109141 | 1 | 2 | visited |
| 4 | 4909121537 | 4004293 | 1 | 1 | visited |
| 5 | 4909127301..4909127467 | 3995647..3995564 | 84 | 1..2 | hole |
| 6 | 4909127527..4909127659 | 3995420..3995354 | 67 | 2..2 | hole |
| 7 | 4909211131..4909211133 | 3870102..3870101 | 2 | 0..2 | hole |
| 8 | 4909301251 | 3615194 | 1 | 2 | visited |
| 9 | 4909302293..4909303739 | 3613631..3612908 | 724 | 2..2 | hole |
| 10 | 4909305259..4909305423 | 3610146..3610064 | 83 | 0..2 | hole |
| 11 | 4909305511..4909306583 | 3609878..3609342 | 537 | 2..0 | hole |
| 12 | 4909464491..4909464493 | 3372124..3372123 | 2 | 1..0 | hole |
| 13 | 4909517361 | 3187781 | 1 | 2 | visited |
| 14 | 4909526461..4909526607 | 3173083..3173010 | 74 | 1..0 | hole |
| 15 | 4909827127 | 2179110 | 1 | 0 | visited |
| 16 | 4909863393..4909863395 | 2030081..2030080 | 2 | 2..1 | hole |
| 17 | 4909863655..4909864315 | 2029690..2029360 | 331 | 1..1 | hole |
| 18 | 4909864641 | 2028651 | 1 | 0 | visited |
| 19 | 4909931137 | 1887913 | 1 | 1 | visited |
| 20 | 4909932463 | 1885924 | 1 | 1 | visited |
| 21 | 4909933985 | 1883641 | 1 | 1 | visited |
| 22 | 4909937429 | 1878475 | 1 | 1 | visited |
| 23 | 4909939133..4909939135 | 1875919..1875918 | 2 | 1..0 | hole |
| 24 | 4909940569 | 1873767 | 1 | 0 | visited |
| 25 | 4910123873 | 1299333 | 1 | 0 | visited |
| 26 | 4910124859 | 1297854 | 1 | 0 | visited |
| 27 | 4910139533..4910139535 | 1275843..1275842 | 2 | 0..2 | hole |
| 28 | 4910175029 | 1222601 | 1 | 2 | visited |
| 29 | 4910177507 | 1218884 | 1 | 2 | visited |
| 30 | 4910217523..4910217675 | 1158860..1158784 | 77 | 2..1 | hole |
| 31 | 4910239495 | 1099070 | 1 | 2 | visited |
| 32 | 4910289483 | 1016884 | 1 | 1 | visited |
| 33 | 4910319991..4910319993 | 916534..916533 | 2 | 1..0 | hole |
| 34 | 4910355651..4910355773 | 852188..852127 | 62 | 2..1 | hole |
| 35 | 4910405873 | 754849 | 1 | 1 | visited |
| 36 | 4910445341 | 643947 | 1 | 0 | visited |
| 37 | 4910462465 | 609181 | 1 | 1 | visited |
| 38 | 4910499651..4910499653 | 545010..545009 | 2 | 0..2 | hole |
| 39 | 4910532411..4910532573 | 473872..473791 | 82 | 1..1 | hole |
| 40 | 4910574819..4910576295 | 395590..394852 | 739 | 1..1 | hole |
| 41 | 4910592945 | 343701 | 1 | 0 | visited |
| 42 | 4910609685 | 307901 | 1 | 2 | visited |
| 43 | 4910616643 | 297464 | 1 | 2 | visited |
| 44 | 4910635379..4910635381 | 264720..264719 | 2 | 0..2 | hole |
| 45 | 4910671531 | 190762 | 1 | 1 | visited |
| 46 | 4910687559..4910687561 | 149196..149195 | 2 | 0..2 | hole |
| 47 | 4910724199 | 89386 | 1 | 1 | visited |

Run-first values mod 3: 1,0,2,1,1,2,0,2,2,0,2,1,2,1,0,2,1,0,1,1,1,1,1,0,0,0,0,2,2,2,2,1,1,2,1,0,1,0,1,1,0,2,2,0,1,0,1
Differences between consecutive run-first values mod 3: 1,1,1,0,2,2,1,0,2,1,1,2,1,1,1,1,1,2,0,0,0,0,1,0,0,0,1,0,0,0,1,0,2,1,1,2,1,2,0,1,1,0,2,2,1,2
Mod-3 distribution of all traced late-landing values: {1: 1012, 0: 1009, 2: 1010}
below-hole at traced late landings: {'hole': 2984, 'visited': 47}

**arc landing 8416516444=110522: 4477 traced late landings in 66 comb runs (a run = values decreasing by 1 every 2 clocks)**

| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |
|---|---|---|---|---|---|
| 1 | 8412507382..8412512202 | 8377175..8374765 | 2411 | 2..1 | hole |
| 2 | 8412753504 | 7960196 | 1 | 2 | visited |
| 3 | 8413195820 | 7153390 | 1 | 1 | visited |
| 4 | 8413509160 | 6319930 | 1 | 1 | visited |
| 5 | 8413514284..8413514286 | 6312244..6312243 | 2 | 1..0 | hole |
| 6 | 8413546604 | 6263766 | 1 | 0 | visited |
| 7 | 8413559968 | 6243720 | 1 | 0 | visited |
| 8 | 8413600362 | 6174217 | 1 | 1 | visited |
| 9 | 8413634408 | 6077644 | 1 | 1 | visited |
| 10 | 8413645240 | 6053864 | 1 | 2 | visited |
| 11 | 8413665972..8413666014 | 6018054..6018033 | 22 | 0..0 | hole |
| 12 | 8413722176 | 5843222 | 1 | 2 | visited |
| 13 | 8413951636 | 5426900 | 1 | 2 | visited |
| 14 | 8414001758..8414001760 | 5258649..5258648 | 2 | 0..2 | hole |
| 15 | 8414056664 | 5165512 | 1 | 1 | visited |
| 16 | 8414126128 | 5027108 | 1 | 2 | visited |
| 17 | 8414154328..8414154330 | 4949900..4949899 | 2 | 2..1 | hole |
| 18 | 8414169102 | 4920569 | 1 | 2 | visited |
| 19 | 8414194306 | 4875303 | 1 | 0 | visited |
| 20 | 8414401226..8414401228 | 4454957..4454956 | 2 | 2..1 | hole |
| 21 | 8414484504..8414484506 | 4304616..4304615 | 2 | 0..2 | hole |
| 22 | 8414650138 | 4006295 | 1 | 2 | visited |
| 23 | 8414812362..8414813228 | 3669159..3668726 | 434 | 0..2 | hole |
| 24 | 8414958668..8414958670 | 3371950..3371949 | 2 | 1..0 | hole |
| 25 | 8414998894 | 3240853 | 1 | 1 | visited |
| 26 | 8415007298..8415007300 | 3213711..3213710 | 2 | 0..2 | hole |
| 27 | 8415033652 | 3174182 | 1 | 2 | visited |
| 28 | 8415069828..8415069894 | 3102346..3102313 | 34 | 1..1 | hole |
| 29 | 8415125764 | 2966660 | 1 | 2 | visited |
| 30 | 8415130574..8415130766 | 2949837..2949741 | 97 | 0..0 | hole |
| 31 | 8415158842 | 2906645 | 1 | 2 | visited |
| 32 | 8415179294..8415179738 | 2857467..2857245 | 223 | 0..0 | hole |
| 33 | 8415184688..8415184736 | 2841460..2841436 | 25 | 1..1 | hole |
| 34 | 8415350088 | 2538492 | 1 | 0 | visited |
| 35 | 8415438054 | 2359099 | 1 | 1 | visited |
| 36 | 8415462352..8415463514 | 2279820..2279239 | 582 | 0..1 | hole |
| 37 | 8415608408 | 2047434 | 1 | 0 | visited |
| 38 | 8415657716 | 1880088 | 1 | 0 | visited |
| 39 | 8415683454 | 1833629 | 1 | 2 | visited |
| 40 | 8415723902..8415724468 | 1757541..1757258 | 284 | 0..2 | hole |
| 41 | 8415738454 | 1713319 | 1 | 1 | visited |
| 42 | 8415769564..8415769714 | 1659132..1659057 | 76 | 0..0 | hole |
| 43 | 8416091100..8416091544 | 1015972..1015750 | 223 | 1..1 | hole |
| 44 | 8416229088 | 754850 | 1 | 2 | visited |
| 45 | 8416278312..8416278314 | 607510..607509 | 2 | 1..0 | hole |
| 46 | 8416294766..8416294768 | 544953..544952 | 2 | 0..2 | hole |
| 47 | 8416294828 | 544862 | 1 | 2 | visited |
| 48 | 8416306522 | 527321 | 1 | 2 | visited |
| 49 | 8416310354 | 521573 | 1 | 2 | visited |
| 50 | 8416312984 | 517628 | 1 | 2 | visited |
| 51 | 8416317374 | 511043 | 1 | 2 | visited |
| 52 | 8416322706 | 503045 | 1 | 2 | visited |
| 53 | 8416329256 | 493220 | 1 | 2 | visited |
| 54 | 8416332734 | 488003 | 1 | 2 | visited |
| 55 | 8416332766 | 487955 | 1 | 2 | visited |
| 56 | 8416332934 | 487703 | 1 | 2 | visited |
| 57 | 8416341046 | 475535 | 1 | 2 | visited |
| 58 | 8416342110 | 473939 | 1 | 2 | visited |
| 59 | 8416396236 | 392038 | 1 | 1 | visited |
| 60 | 8416418430 | 317359 | 1 | 1 | visited |
| 61 | 8416426938 | 297413 | 1 | 2 | visited |
| 62 | 8416446680 | 247326 | 1 | 0 | visited |
| 63 | 8416474224..8416474226 | 197742..197741 | 2 | 0..2 | hole |
| 64 | 8416483062 | 168875 | 1 | 2 | visited |
| 65 | 8416491874 | 152563 | 1 | 1 | visited |
| 66 | 8416516442..8416516444 | 110523..110522 | 2 | 0..2 | hole |

Run-first values mod 3: 2,2,1,1,1,0,0,1,1,2,0,2,2,0,1,2,2,2,0,2,0,2,0,1,1,0,2,1,2,0,2,0,1,0,1,0,0,0,2,0,1,0,1,2,1,0,2,2,2,2,2,2,2,2,2,2,2,2,1,1,2,0,0,2,1,0
Differences between consecutive run-first values mod 3: 0,1,0,0,1,0,2,0,2,2,1,0,2,2,2,0,0,2,1,2,1,2,2,0,1,1,1,2,2,1,2,2,1,2,1,0,0,1,2,2,1,2,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,1,0,2,2,0,1,1,1
Mod-3 distribution of all traced late-landing values: {2: 1503, 1: 1486, 0: 1488}
below-hole at traced late landings: {'hole': 4411, 'visited': 66}

## 5. Example traces: the three deepest arcs (at most 80 lines each)

Columns: `clock a h k r step cand candState class [mod3= below=] [UP] [POP]`; k = floor(a/clock), r = a mod clock, h = a - clock; `cand` = a(clock-1) - clock (or `-` when a(clock-1) <= clock); candState = fresh (landed) / blocked (visited) / none; class = band (subtraction to a value >= clock) / late (subtraction to a value < clock); for late landings the value mod 3 and whether value-1 is a hole right after the landing; UP = k >= 2 after a record with k <= 1; POP = k >= 3. Full traces: `h1e10/trace_<index>.txt`.

### arc 37, landing 2789149734=2405, depth 6.064

```
# arc 37 clocks 1610187039..2789150423 landing 2789149734=2405 depth 6.06436 traceFrom 2787779386
# clock a h k r step cand candState class [mod3= below=] [UP] [POP]
2787779386 11153905323 8366125937 4 2787779 S 11153905323 fresh band POP
2787779387 13941684710 11153905323 5 2787775 A 8366125936 blocked - POP
2787779388 11153905322 8366125934 4 2787770 S 11153905322 fresh band POP
2787779389 13941684711 11153905322 5 2787766 A 8366125933 blocked - POP
2787779390 11153905321 8366125931 4 2787761 S 11153905321 fresh band POP
... 1370319 records omitted ...
2789149710 5578301861 2789152151 2 2441 A 2441 blocked - UP
2789149711 2789152150 2439 1 2439 S 2789152150 fresh band
2789149712 5578301862 2789152150 2 2438 A 2438 blocked - UP
2789149713 2789152149 2436 1 2436 S 2789152149 fresh band
2789149714 5578301863 2789152149 2 2435 A 2435 blocked - UP
2789149715 2789152148 2433 1 2433 S 2789152148 fresh band
2789149716 5578301864 2789152148 2 2432 A 2432 blocked - UP
2789149717 2789152147 2430 1 2430 S 2789152147 fresh band
2789149718 5578301865 2789152147 2 2429 A 2429 blocked - UP
2789149719 2789152146 2427 1 2427 S 2789152146 fresh band
2789149720 5578301866 2789152146 2 2426 A 2426 blocked - UP
2789149721 2789152145 2424 1 2424 S 2789152145 fresh band
2789149722 5578301867 2789152145 2 2423 A 2423 blocked - UP
2789149723 2789152144 2421 1 2421 S 2789152144 fresh band
2789149724 5578301868 2789152144 2 2420 A 2420 blocked - UP
2789149725 2789152143 2418 1 2418 S 2789152143 fresh band
2789149726 5578301869 2789152143 2 2417 A 2417 blocked - UP
2789149727 2789152142 2415 1 2415 S 2789152142 fresh band
2789149728 5578301870 2789152142 2 2414 A 2414 blocked - UP
2789149729 2789152141 2412 1 2412 S 2789152141 fresh band
2789149730 5578301871 2789152141 2 2411 A 2411 blocked - UP
2789149731 2789152140 2409 1 2409 S 2789152140 fresh band
2789149732 5578301872 2789152140 2 2408 A 2408 blocked - UP
2789149733 2789152139 2406 1 2406 S 2789152139 fresh band
2789149734 2405 -2789147329 0 2405 S 2405 fresh late mod3=2 below=visited
2789149735 2789152140 2405 1 2405 A - none -
2789149736 5578301876 2789152140 2 2404 A 2404 blocked - UP
2789149737 8367451613 5578301876 3 2402 A 2789152139 blocked - POP
2789149738 11156601351 8367451613 4 2399 A 5578301875 blocked - POP
2789149739 8367451612 5578301873 3 2395 S 8367451612 fresh band POP
2789149740 11156601352 8367451612 4 2392 A 5578301872 blocked - POP
2789149741 8367451611 5578301870 3 2388 S 8367451611 fresh band POP
2789149742 11156601353 8367451611 4 2385 A 5578301869 blocked - POP
2789149743 8367451610 5578301867 3 2381 S 8367451610 fresh band POP
2789149744 11156601354 8367451610 4 2378 A 5578301866 blocked - POP
2789149745 8367451609 5578301864 3 2374 S 8367451609 fresh band POP
2789149746 11156601355 8367451609 4 2371 A 5578301863 blocked - POP
2789149747 8367451608 5578301861 3 2367 S 8367451608 fresh band POP
2789149748 11156601356 8367451608 4 2364 A 5578301860 blocked - POP
2789149749 8367451607 5578301858 3 2360 S 8367451607 fresh band POP
2789149750 11156601357 8367451607 4 2357 A 5578301857 blocked - POP
2789149751 8367451606 5578301855 3 2353 S 8367451606 fresh band POP
2789149752 11156601358 8367451606 4 2350 A 5578301854 blocked - POP
2789149753 8367451605 5578301852 3 2346 S 8367451605 fresh band POP
2789149754 11156601359 8367451605 4 2343 A 5578301851 blocked - POP
2789149755 8367451604 5578301849 3 2339 S 8367451604 fresh band POP
2789149756 11156601360 8367451604 4 2336 A 5578301848 blocked - POP
2789149757 8367451603 5578301846 3 2332 S 8367451603 fresh band POP
2789149758 11156601361 8367451603 4 2329 A 5578301845 blocked - POP
2789149759 8367451602 5578301843 3 2325 S 8367451602 fresh band POP
2789149760 11156601362 8367451602 4 2322 A 5578301842 blocked - POP
2789149761 8367451601 5578301840 3 2318 S 8367451601 fresh band POP
2789149762 11156601363 8367451601 4 2315 A 5578301839 blocked - POP
2789149763 8367451600 5578301837 3 2311 S 8367451600 fresh band POP
2789149764 11156601364 8367451600 4 2308 A 5578301836 blocked - POP
... 645 records omitted ...
2789150410 11156601687 8367451277 4 47 A 5578300867 blocked - POP
2789150411 8367451276 5578300865 3 43 S 8367451276 fresh band POP
2789150412 11156601688 8367451276 4 40 A 5578300864 blocked - POP
2789150413 8367451275 5578300862 3 36 S 8367451275 fresh band POP
2789150414 11156601689 8367451275 4 33 A 5578300861 blocked - POP
2789150415 8367451274 5578300859 3 29 S 8367451274 fresh band POP
2789150416 11156601690 8367451274 4 26 A 5578300858 blocked - POP
2789150417 8367451273 5578300856 3 22 S 8367451273 fresh band POP
2789150418 11156601691 8367451273 4 19 A 5578300855 blocked - POP
2789150419 8367451272 5578300853 3 15 S 8367451272 fresh band POP
2789150420 11156601692 8367451272 4 12 A 5578300852 blocked - POP
2789150421 8367451271 5578300850 3 8 S 8367451271 fresh band POP
2789150422 11156601693 8367451271 4 5 A 5578300849 blocked - POP
2789150423 8367451270 5578300847 3 1 S 8367451270 fresh band POP
# next arc starts: 2789150424 11156601694 8367451270 3 2789150422 A 5578300846 blocked - POP
```

### arc 36, landing 1610186343=2426, depth 5.822

```
# arc 36 clocks 904036925..1610187038 landing 1610186343=2426 depth 5.82199 traceFrom 1609420154
# clock a h k r step cand candState class [mod3= below=] [UP] [POP]
1609420154 1611029573 1609419 1 1609419 S 1611029573 fresh band
1609420155 3220449728 1611029573 2 1609418 A 1609418 blocked - UP
1609420156 1611029572 1609416 1 1609416 S 1611029572 fresh band
1609420157 3220449729 1611029572 2 1609415 A 1609415 blocked - UP
1609420158 1611029571 1609413 1 1609413 S 1611029571 fresh band
... 766160 records omitted ...
1610186319 3220375100 1610188781 2 2462 A 2462 blocked - UP
1610186320 1610188780 2460 1 2460 S 1610188780 fresh band
1610186321 3220375101 1610188780 2 2459 A 2459 blocked - UP
1610186322 1610188779 2457 1 2457 S 1610188779 fresh band
1610186323 3220375102 1610188779 2 2456 A 2456 blocked - UP
1610186324 1610188778 2454 1 2454 S 1610188778 fresh band
1610186325 3220375103 1610188778 2 2453 A 2453 blocked - UP
1610186326 1610188777 2451 1 2451 S 1610188777 fresh band
1610186327 3220375104 1610188777 2 2450 A 2450 blocked - UP
1610186328 1610188776 2448 1 2448 S 1610188776 fresh band
1610186329 3220375105 1610188776 2 2447 A 2447 blocked - UP
1610186330 1610188775 2445 1 2445 S 1610188775 fresh band
1610186331 3220375106 1610188775 2 2444 A 2444 blocked - UP
1610186332 1610188774 2442 1 2442 S 1610188774 fresh band
1610186333 3220375107 1610188774 2 2441 A 2441 blocked - UP
1610186334 1610188773 2439 1 2439 S 1610188773 fresh band
1610186335 3220375108 1610188773 2 2438 A 2438 blocked - UP
1610186336 1610188772 2436 1 2436 S 1610188772 fresh band
1610186337 3220375109 1610188772 2 2435 A 2435 blocked - UP
1610186338 1610188771 2433 1 2433 S 1610188771 fresh band
1610186339 3220375110 1610188771 2 2432 A 2432 blocked - UP
1610186340 1610188770 2430 1 2430 S 1610188770 fresh band
1610186341 3220375111 1610188770 2 2429 A 2429 blocked - UP
1610186342 1610188769 2427 1 2427 S 1610188769 fresh band
1610186343 2426 -1610183917 0 2426 S 2426 fresh late mod3=2 below=visited
1610186344 1610188770 2426 1 2426 A - none -
1610186345 3220375115 1610188770 2 2425 A 2425 blocked - UP
1610186346 4830561461 3220375115 3 2423 A 1610188769 blocked - POP
1610186347 6440747808 4830561461 4 2420 A 3220375114 blocked - POP
1610186348 4830561460 3220375112 3 2416 S 4830561460 fresh band POP
1610186349 6440747809 4830561460 4 2413 A 3220375111 blocked - POP
1610186350 4830561459 3220375109 3 2409 S 4830561459 fresh band POP
1610186351 6440747810 4830561459 4 2406 A 3220375108 blocked - POP
1610186352 4830561458 3220375106 3 2402 S 4830561458 fresh band POP
1610186353 6440747811 4830561458 4 2399 A 3220375105 blocked - POP
1610186354 4830561457 3220375103 3 2395 S 4830561457 fresh band POP
1610186355 6440747812 4830561457 4 2392 A 3220375102 blocked - POP
1610186356 4830561456 3220375100 3 2388 S 4830561456 fresh band POP
1610186357 6440747813 4830561456 4 2385 A 3220375099 blocked - POP
1610186358 4830561455 3220375097 3 2381 S 4830561455 fresh band POP
1610186359 6440747814 4830561455 4 2378 A 3220375096 blocked - POP
1610186360 4830561454 3220375094 3 2374 S 4830561454 fresh band POP
1610186361 6440747815 4830561454 4 2371 A 3220375093 blocked - POP
1610186362 4830561453 3220375091 3 2367 S 4830561453 fresh band POP
1610186363 6440747816 4830561453 4 2364 A 3220375090 blocked - POP
1610186364 4830561452 3220375088 3 2360 S 4830561452 fresh band POP
1610186365 6440747817 4830561452 4 2357 A 3220375087 blocked - POP
1610186366 4830561451 3220375085 3 2353 S 4830561451 fresh band POP
1610186367 6440747818 4830561451 4 2350 A 3220375084 blocked - POP
1610186368 4830561450 3220375082 3 2346 S 4830561450 fresh band POP
1610186369 6440747819 4830561450 4 2343 A 3220375081 blocked - POP
1610186370 4830561449 3220375079 3 2339 S 4830561449 fresh band POP
1610186371 6440747820 4830561449 4 2336 A 3220375078 blocked - POP
1610186372 4830561448 3220375076 3 2332 S 4830561448 fresh band POP
1610186373 6440747821 4830561448 4 2329 A 3220375075 blocked - POP
... 651 records omitted ...
1610187025 6440748147 4830561122 4 47 A 3220374097 blocked - POP
1610187026 4830561121 3220374095 3 43 S 4830561121 fresh band POP
1610187027 6440748148 4830561121 4 40 A 3220374094 blocked - POP
1610187028 4830561120 3220374092 3 36 S 4830561120 fresh band POP
1610187029 6440748149 4830561120 4 33 A 3220374091 blocked - POP
1610187030 4830561119 3220374089 3 29 S 4830561119 fresh band POP
1610187031 6440748150 4830561119 4 26 A 3220374088 blocked - POP
1610187032 4830561118 3220374086 3 22 S 4830561118 fresh band POP
1610187033 6440748151 4830561118 4 19 A 3220374085 blocked - POP
1610187034 4830561117 3220374083 3 15 S 4830561117 fresh band POP
1610187035 6440748152 4830561117 4 12 A 3220374082 blocked - POP
1610187036 4830561116 3220374080 3 8 S 4830561116 fresh band POP
1610187037 6440748153 4830561116 4 5 A 3220374079 blocked - POP
1610187038 4830561115 3220374077 3 1 S 4830561115 fresh band POP
# next arc starts: 1610187039 6440748154 4830561115 3 1610187037 A 3220374076 blocked - POP
```

### arc 39, landing 8416516444=110522, depth 4.882

```
# arc 39 clocks 4910758398..8416580354 landing 8416516444=110522 depth 4.88168 traceFrom 8412483843
# clock a h k r step cand candState class [mod3= below=] [UP] [POP]
8412483843 8420896326 8412483 1 8412483 S 8420896326 fresh band
8412483844 16833380170 8420896326 2 8412482 A 8412482 blocked - UP
8412483845 8420896325 8412480 1 8412480 S 8420896325 fresh band
8412483846 16833380171 8420896325 2 8412479 A 8412479 blocked - UP
8412483847 8420896324 8412477 1 8412477 S 8420896324 fresh band
... 4032572 records omitted ...
8416516420 16833143396 8416626976 2 110556 A 110556 blocked - UP
8416516421 8416626975 110554 1 110554 S 8416626975 fresh band
8416516422 16833143397 8416626975 2 110553 A 110553 blocked - UP
8416516423 8416626974 110551 1 110551 S 8416626974 fresh band
8416516424 16833143398 8416626974 2 110550 A 110550 blocked - UP
8416516425 8416626973 110548 1 110548 S 8416626973 fresh band
8416516426 16833143399 8416626973 2 110547 A 110547 blocked - UP
8416516427 8416626972 110545 1 110545 S 8416626972 fresh band
8416516428 16833143400 8416626972 2 110544 A 110544 blocked - UP
8416516429 8416626971 110542 1 110542 S 8416626971 fresh band
8416516430 16833143401 8416626971 2 110541 A 110541 blocked - UP
8416516431 8416626970 110539 1 110539 S 8416626970 fresh band
8416516432 16833143402 8416626970 2 110538 A 110538 blocked - UP
8416516433 8416626969 110536 1 110536 S 8416626969 fresh band
8416516434 16833143403 8416626969 2 110535 A 110535 blocked - UP
8416516435 8416626968 110533 1 110533 S 8416626968 fresh band
8416516436 16833143404 8416626968 2 110532 A 110532 blocked - UP
8416516437 8416626967 110530 1 110530 S 8416626967 fresh band
8416516438 16833143405 8416626967 2 110529 A 110529 blocked - UP
8416516439 8416626966 110527 1 110527 S 8416626966 fresh band
8416516440 16833143406 8416626966 2 110526 A 110526 blocked - UP
8416516441 8416626965 110524 1 110524 S 8416626965 fresh band
8416516442 110523 -8416405919 0 110523 S 110523 fresh late mod3=0 below=hole
8416516443 8416626966 110523 1 110523 A - none -
8416516444 110522 -8416405922 0 110522 S 110522 fresh late mod3=2 below=visited
8416516445 8416626967 110522 1 110522 A - none -
8416516446 16833143413 8416626967 2 110521 A 110521 blocked - UP
8416516447 25249659860 16833143413 3 110519 A 8416626966 blocked - POP
8416516448 33666176308 25249659860 4 110516 A 16833143412 blocked - POP
8416516449 25249659859 16833143410 3 110512 S 25249659859 fresh band POP
8416516450 33666176309 25249659859 4 110509 A 16833143409 blocked - POP
8416516451 25249659858 16833143407 3 110505 S 25249659858 fresh band POP
8416516452 33666176310 25249659858 4 110502 A 16833143406 blocked - POP
8416516453 25249659857 16833143404 3 110498 S 25249659857 fresh band POP
8416516454 33666176311 25249659857 4 110495 A 16833143403 blocked - POP
8416516455 25249659856 16833143401 3 110491 S 25249659856 fresh band POP
8416516456 33666176312 25249659856 4 110488 A 16833143400 blocked - POP
8416516457 25249659855 16833143398 3 110484 S 25249659855 fresh band POP
8416516458 33666176313 25249659855 4 110481 A 16833143397 blocked - POP
8416516459 25249659854 16833143395 3 110477 S 25249659854 fresh band POP
8416516460 33666176314 25249659854 4 110474 A 16833143394 blocked - POP
8416516461 25249659853 16833143392 3 110470 S 25249659853 fresh band POP
8416516462 33666176315 25249659853 4 110467 A 16833143391 blocked - POP
8416516463 25249659852 16833143389 3 110463 S 25249659852 fresh band POP
8416516464 33666176316 25249659852 4 110460 A 16833143388 blocked - POP
8416516465 25249659851 16833143386 3 110456 S 25249659851 fresh band POP
8416516466 33666176317 25249659851 4 110453 A 16833143385 blocked - POP
8416516467 25249659850 16833143383 3 110449 S 25249659850 fresh band POP
8416516468 33666176318 25249659850 4 110446 A 16833143382 blocked - POP
8416516469 25249659849 16833143380 3 110442 S 25249659849 fresh band POP
8416516470 33666176319 25249659849 4 110439 A 16833143379 blocked - POP
8416516471 25249659848 16833143377 3 110435 S 25249659848 fresh band POP
8416516472 33666176320 25249659848 4 110432 A 16833143376 blocked - POP
8416516473 25249659847 16833143374 3 110428 S 25249659847 fresh band POP
8416516474 33666176321 25249659847 4 110425 A 16833143373 blocked - POP
... 63866 records omitted ...
8416580341 8416580361 20 1 20 S 8416580361 fresh band
8416580342 16833160703 8416580361 2 19 A 19 blocked - UP
8416580343 8416580360 17 1 17 S 8416580360 fresh band
8416580344 16833160704 8416580360 2 16 A 16 blocked - UP
8416580345 8416580359 14 1 14 S 8416580359 fresh band
8416580346 16833160705 8416580359 2 13 A 13 blocked - UP
8416580347 8416580358 11 1 11 S 8416580358 fresh band
8416580348 16833160706 8416580358 2 10 A 10 blocked - UP
8416580349 8416580357 8 1 8 S 8416580357 fresh band
8416580350 16833160707 8416580357 2 7 A 7 blocked - UP
8416580351 8416580356 5 1 5 S 8416580356 fresh band
8416580352 16833160708 8416580356 2 4 A 4 blocked - UP
8416580353 8416580355 2 1 2 S 8416580355 fresh band
8416580354 16833160709 8416580355 2 1 A 1 blocked - UP
# next arc starts: 8416580355 8416580354 -1 0 8416580354 S 8416580354 fresh late mod3=2 below=hole
```


## 6. Appendix: all 39 completed arcs up to 1e10

Columns: ordinal, start clock, end clock, a(start), landing index, landing value, depth, late landings in the arc, traced late landings, last late clock, last late value, trace-from clock, traced clocks, traced k=0/1/2/3+, a(next arc start), deep flag.

```
# ordinal startClock endClock startValue landingIndex landingValue depth lateTotal lateDeep lastLateClock lastLateValue traceFrom traceLen k0 k1 k2 k3+ nextArcValue deep?
1 1 1 1 1 1 0 0 0 0 0 1 1 0 1 0 0 3 -
2 2 3 3 2 3 -0.176091 0 0 0 0 3 1 0 0 1 0 2 -
3 4 6 2 4 2 0.30103 1 0 4 2 0 0 0 0 0 0 20 -
4 7 11 20 10 11 -0.0413927 0 0 0 0 11 1 0 0 1 0 10 -
5 12 21 10 16 8 0.30103 3 0 16 8 21 1 0 0 0 1 41 -
6 22 39 41 31 14 0.345234 5 0 31 14 39 1 0 0 1 0 38 -
7 40 76 38 64 26 0.391207 13 0 64 26 76 1 0 0 1 0 75 -
8 77 134 75 131 4 1.51521 15 0 131 4 0 0 0 0 0 0 268 -
9 135 248 268 222 47 0.674255 32 0 222 47 248 1 0 0 1 0 247 -
10 249 453 247 403 92 0.641517 54 0 403 92 0 0 0 0 0 0 1361 -
11 454 844 1361 770 111 0.841168 109 0 770 111 844 1 0 0 1 0 2533 -
12 845 1520 2533 1409 181 0.891232 182 0 1409 181 1520 1 0 1 0 0 3041 -
13 1521 2752 3041 2652 150 1.24748 322 0 2652 150 2751 2 0 1 1 0 2751 -
14 2753 5045 2751 4825 371 1.11412 665 0 4825 371 5044 2 0 0 0 2 15135 -
15 5046 9317 15135 9078 361 1.40048 1203 0 9078 361 9311 7 0 4 3 0 18635 -
16 9318 17223 18635 16773 781 1.33196 2318 0 16773 781 17218 6 0 0 0 6 51668 -
17 17224 31221 51668 30768 828 1.57007 3905 0 30768 828 31201 21 0 11 10 0 62443 -
18 31222 57071 62443 56827 366 2.19107 7470 0 56827 366 57033 39 0 19 20 0 57070 -
19 57072 99741 57070 99734 19 3.72009 11308 1 99734 19 99694 48 1 11 21 15 398963 -
20 99742 181693 398963 181653 61 3.47391 22832 3 181653 61 181573 121 3 57 58 3 181693 -
21 181694 328255 181693 328002 879 2.57189 41894 0 328002 879 328162 94 0 0 0 94 1313022 -
22 328256 589932 1313022 588583 4802 2.08839 75128 0 588583 4802 589764 169 0 0 0 169 2359729 -
23 589933 1034838 2359729 1032996 3378 2.48544 119469 0 1032996 3378 1034149 690 0 345 345 0 1034838 -
24 1034839 1788537 1034838 1787013 5329 2.52548 203276 0 1787013 5329 1788027 511 0 0 0 511 5365613 -
25 1788538 3225918 5365613 3220128 9462 2.53189 403064 0 3220128 9462 3223770 2149 0 1074 1075 0 3225918 -
26 3225919 5784585 3225918 5771203 32102 2.25473 718529 0 5771203 32102 5783078 1508 0 0 330 1178 17353757 -
27 5784586 10212210 17353757 10201340 18954 2.73096 1270213 0 10201340 18954 10205407 6804 0 3402 3402 0 10212210 -
28 10212211 18399784 10212210 18394609 18107 3.00684 2318984 1 18394609 18107 18394418 5367 1 97 96 5173 73599139 -
29 18399785 32148794 73599139 32144188 16114 3.2999 3842572 2 32144188 16114 32133507 15288 2 5342 5340 4604 96446382 -
30 32148795 58056875 96446382 58055311 4202 4.14039 7316473 21 58055311 4202 58027034 29842 21 11691 11681 6449 58056874 DEEP
31 58056876 101769229 58056874 101762018 25231 3.60565 11965236 5 101762018 25231 101720206 49024 5 18173 18173 12673 407076917 -
32 101769230 173395919 407076917 173367175 60240 3.45908 19105500 443 173367175 60240 173309962 85958 443 31638 31268 22609 520187758 -
33 173395920 302890748 520187758 302844912 92404 3.51553 35599428 442 302844912 92404 302734424 156325 442 60914 60490 34479 908672243 -
34 302890749 511561220 908672243 511518279 92188 3.74419 55979450 1121 511518279 92188 511300236 260985 1121 100184 99282 60398 2046244881 -
35 511561221 904036924 2046244881 904032692 14804 4.78581 111017793 581 904032692 14804 903591555 445370 581 160859 166209 117721 2712110771 DEEP
36 904036925 1610187038 2712110771 1610186343 2426 5.82199 202844334 1343 1610186343 2426 1609420154 766885 1343 237179 298492 229871 6440748154 DEEP
37 1610187039 2789150423 6440748154 2789149734 2405 6.06436 327754080 952 2789149734 2405 2787779386 1371038 952 509793 508923 351370 11156601694 DEEP
38 2789150424 4910758397 11156601694 4910724199 89386 4.73988 602335220 3031 4910724199 89386 4908684482 2073916 3031 622929 644396 803560 14732275193 DEEP
39 4910758398 8416580354 14732275193 8416516444 110522 4.88168 958574394 4477 8416516444 110522 8412483843 4096512 4477 1479963 1522841 1089231 8416580354 DEEP
```

## 7. Files

- `experiments/arc_trace_probe.cpp` (repository, uncommitted): the probe. Build: `c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/arc_trace_probe.cpp -o arctrace`; run: `arctrace HORIZON OUTDIR [RING_LOG2]`.
- `h1e10/` and `h3e9/`: `summary.txt`, `arcs_all.txt`, `deep_arcs.txt` (last 16 records of each deep arc), `trace_<index>.txt` (full traced part of each deep arc: 29842 .. 4096512 records, none truncated), `lates_<index>.txt` (every traced late landing with next-8 values, first later clock with 0<h<v, next late landing), `aggregate.md`.
- `aggregate.py`, `verify.py`: the scripts that produced Sections 3-5.
