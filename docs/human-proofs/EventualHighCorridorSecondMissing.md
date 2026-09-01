# EventualHighCorridorSecondMissing

**役割:** A枝corridorを持つ仮想反例は、targetより上に**第二の永久欠損値**を強制する。計数段(履歴は1時刻1値)は無条件に自由であり、非自由な段はcorridor value lawによる窓全体の凍結である。

## このモジュールの役割

仮想反例(missing permanent tail: 最小の未出targetが恒久的に軌道の下に取り残される
状態、`MissingPermanentAboveTail`)がA枝、すなわちeventual high-candidate corridor
(あるcutoff以後すべての減算候補がtargetを厳密に超える回廊、
`EventualHighCandidateTail`)を持つとき、未出の値はtargetの一個では済まないことを
示す。証明は二段からなる。計数段は完全に自由である: 履歴リストは1時刻に1値しか
記録しないので、有限の窓 `[0, cutoff + target + 2]` にはtarget以外の未訪問値が必ず
残る。非自由な段はcorridorのvalue law(cutoff以後の全軌道値は `target + clock + 1`
を超える)そのものであり、これが窓内の値への将来の着地を一括で排除する(凍結)。
仕上げに、permanent tailの証明書がtarget未満の値をすべて既出にしているため、
残った未訪問値はtargetの真上に押し上げられる。

## 定理と証明

### `valuesThrough_length` (L28)

**主張:** 履歴リスト `valuesThrough n` の長さは、重複を込めてちょうど `n + 1`
である。

**証明:** `n` に関する帰納法。一歩の展開則 `valuesThrough (n+1) = a (n+1) ::
valuesThrough n`(`valuesThrough_succ`)から直ちに従う。補助補題だが、
「軌道は1時刻に1値しか生産できない」という計数段の全根拠である。

### `EventualHighCandidateTail.exists_second_missing` (L38)

**主張(第二欠損値):** `MissingPermanentAboveTail target tailStart` と
`EventualHighCandidateTail target tailStart` のもとで、

`∃ u, target < u ∧ ∀ time, a time ≠ u`。

すなわちA枝corridorの上では、targetより真に大きく、どの時刻にも訪問されない値
`u` が存在する。

**証明:** corridorの定義から `tailStart ≤ cutoff` なるcutoffとcorridor条件
「∀ n ≥ cutoff, target < nextSubtractionCandidate (n+1)」を取り出す。

*(1) 計数段: 窓内にfreshな値が残る。* 窓 `[0, cutoff + target + 2]` は
`cutoff + target + 3` 個の数を含む。主張: この窓の中に、target以外で履歴
`valuesThrough (cutoff + 1)` に属さない値 `u` が存在する。存在しないと仮定すると、
窓内のすべての数は `target` であるか履歴に属するので、重複のないリスト
`range (cutoff + target + 3)` は `target :: valuesThrough (cutoff + 1)` の
部分集合になる。Nodupリストの部分集合則により長さを比較すると、左辺は
`cutoff + target + 3`、右辺は `valuesThrough_length` より
`1 + (cutoff + 2) = cutoff + 3`。よって `target ≤ 0` となり、証明書の
`target_positive`(`0 < target`)に矛盾する。この段は鳩ノ巣論法だけで閉じており、
corridor仮定を一切使わない。

*(2) `u` はtargetより上にある。* もし `u < target` なら、証明書の
`below_covered` により `u` は `valuesThrough tailStart` に属し、
`tailStart ≤ cutoff + 1` なので履歴の単調性(`mem_valuesThrough_iff` で出現時刻を
移す)から `u ∈ valuesThrough (cutoff + 1)`。これは(1)のfresh性に矛盾する。
`u ≠ target` は(1)で選んであるので、残るのは `target < u` だけである。

*(3) 凍結段: `u` は将来も訪問されない。* `a time = u` となる時刻があったとする。
`time ≤ cutoff + 1` なら `u` は履歴 `valuesThrough (cutoff + 1)` に属し、(1)に
矛盾。`time > cutoff + 1` ならvalue law(`corridor_value_law`)が適用でき

`target + (time + 1) < a time = u`。

一方 `u` は窓に入っているので `u ≤ cutoff + target + 2 < target + time + 1`
(∵ `cutoff + 1 < time`)。両不等式は両立しない。∎

計数は証人 `u` の構成のみに使われ、矛盾の導出には使われていない。矛盾を生むのは
value lawによる「窓内の値には将来の着地機会が存在しない」という凍結であり、
これがこの定理の非自由な内容である。加算着地は自分のclock以上、corridor内の
減算着地はcone `target + clock` の上、というvalue lawの帰結が、固定された有限窓を
まるごと軌道の射程外に置く。

### `EventualHighCandidateTail.missing_not_unique` (L89)

**主張:** 同じ仮定のもとで `∃ u, target < u ∧ ¬ ∃ time, a time = u`。

**証明:** 前定理の結論を、証明書の `target_missing` fieldと同形の否定存在
`¬ ∃ time, a time = u` へ包み直すだけである。「targetは唯一の永久欠損値ではない」
という読み方を、下流が証明書と同じ形で受け取れるようにする包装定理。

## 全体の中での位置づけ

入力は三つ: `PermanentAboveTail` の仮想反例証明書
`MissingPermanentAboveTail`、`TargetTailResidualKernel` のA枝
`EventualHighCandidateTail`、そして `EventualHighCorridorSupply` の
`corridor_value_law` である。2026-09-01午後のsharp-kernelスプリント(Round 4、
docs/PARALLEL_SPRINT_2026-09-01_AFTERNOON.md §6.2, §7b)の成果であり、
A枝をSharpCorridor証明書(value law・無限fresh着地・自給自足供給窓・birth分類)へ
精密化した上に載る最初の大域的帰結である: A枝が生き残るなら、全射性の破れは
一点ではなく少なくとも二点になる。

紙上分析(docs/CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md)では、この第二欠損値 `u` に
相対化した候補規律を経由して、A枝は「candidate walkの発散」∨「最小再訪候補での
rigid recurrence」へ縮約されている。後者のrecurrence側をLean化したのが姉妹
モジュール `EventualHighCorridorRecurrence` である。証明地図では
docs/PROOF_MAP.md のRound 3b/4追補の節に対応する。
