# EventualHighCorridorBirth

**役割:** 回廊内のforced additionの候補値について、その初出（birth）が回廊内部にあることと、birthステップが「取られた減算」か「加算出力」のどちらかであることを分類する。

## このモジュールの役割

`EventualHighCorridorSupply` の供給者定理は、pre-cutoffの値の棚 `upperTri cutoff` を超える候補値の
供給者（同じ値を運ぶ時刻）が回廊内部にあることまでを示した。本モジュールはこれを二段階で精密化する。
第一に、供給者は候補値の**初出時刻**（birth、その値が数列に初めて現れた時刻）に取り直せる。
第二に、正の時計での初出は実際のステップが産むので、birthは「減算が取られた」か「加算出力」かに
無条件で二分される。合成すると、回廊の遅いforced additionの候補値は、回廊内部のより早い時計で
(i) その時計自身の減算候補が実際に取られて生まれたか、(ii) 加算出力として生まれたか、のどちらかである。

## 定理と証明

### `corridor_forcedAddition_birth` (L38)

**主張:** 回廊指標 `cutoff` に対し `cutoff + 1 ≤ n`、時刻 `n+1` がforced addition、候補値
`c = a(n) − (n+1)` が `upperTri cutoff < c` を満たすなら、ある時刻 `t` があって
`cutoff < t ≤ n`、`t` は `c` の初出、`t + 1 + target < c`、かつ `c ≤ upperTri t`。

**証明:** `corridor_forcedAddition_candidate_seen` により `c` は時刻 `n` までの履歴に属するので、
`history_member_has_firstAt` が初出時刻 `f ≤ n` を与える。`f ≤ cutoff` と仮定すると
`c = a(f) ≤ upperTri f ≤ upperTri cutoff` となり仮定 `upperTri cutoff < c` に矛盾するから
`cutoff < f`。すると回廊のvalue law（`corridor_value_law`）が時刻 `f` に適用でき
`f + 1 + target < a(f) = c`、また `a_le_upperTri` から `c ≤ upperTri f`。

### `firstAt_succ_birth_dichotomy` (L66)

**主張:** 値 `v` の初出時刻が `t + 1`（正の時計）なら、(i) 時刻 `t+1` のステップは減算で
`v = a(t) − (t+1)`（＝時刻 `t` の減算候補）、または (ii) ステップは加算で
`v = a(t) + (t+1)` かつ `t + 1 ≤ v`。

**証明:** ステップの二択そのもの。減算なら着地値は定義により時刻 `t` の減算候補であり、
加算なら着地値は `a(t) + (t+1) ≥ t + 1` で自分の時計を上回る。

### `corridor_forcedAddition_birth_classified` (L89)

**主張:** 上の仮定の下で、ある `t` があって `cutoff ≤ t`、`t + 1 ≤ n`、
`t + 2 + target < c`、かつ「時刻 `t+1` は減算で `c` は時刻 `t` の減算候補に等しい」または
「時刻 `t+1` は加算で `c = a(t) + (t+1)`」。

**証明:** birth定理の初出時刻 `b` は `cutoff < b` なので `b = t + 1` と書け、
初出をbirth二分法に渡すだけである。cone不等式は `b + 1 + target < c` の書き換え。

## 全体の中での位置づけ

`SharpResidualKernel` のA枝（`SharpCorridor`）の供給窓を初出レベルまで precision を上げた
モジュールであり、generation-vs-reuse chronology 路線の第2のレンガである。減算birth枝では
候補値が「より早い時計自身の候補」なので、分類は原理的に反復でき、candidate ancestry chain が
回廊を後方へ歩く。chainの出口は加算birthか有限pre-cutoff hullに限られる。この反復の形式化が
次の研究対象である。
