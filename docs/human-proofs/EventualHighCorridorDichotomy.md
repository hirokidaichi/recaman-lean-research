# EventualHighCorridorDichotomy

**役割:** A枝（eventual-high回廊）を「candidate walkの発散」または「最小再訪候補でのrigid event stream」へ無条件に二分する、本スプリントのA枝側capstone。

## このモジュールの役割

回廊のcandidate walk `d(m) = a(m) − (m+1)` は、任意の限界を最終的に超え続ける（発散）か、
ある値へ非有界に戻り続けるかのどちらかである。後者の場合、`EventualHighCorridorRecurrence` の
rigid event（対角freshな減算入り・forced addition出・後続値の既訪問強制）が、最小の再訪値 `c` の
すべての遅いuse clockで発動することを示す。これにより、A枝の残余は「発散残余の排除」と
「rigid event streamの需要 `c + m ∈ 履歴` の供給解析」の二つへ正確に分かれる。

## 定理と証明

### `exists_least_recurring_candidate` (L34)

**主張:** ある値 `c₀` が候補として任意に遅い時計で再訪するなら、再訪する値のうち最小の `c` が存在する。

**証明:** `c₀` に関する強帰納法。より小さい再訪値があればそこへ降り、なければ `c₀` 自身が最小である。
`Nat.find` を使わないリポジトリ標準の有界最小元構成である。

### `exists_uniform_bound_of_no_recurrence` (L63)

**主張:** 帯 `(target, c)` のどの値も非有界には再訪しないなら、ある `M₀` 以後の時計では
帯内のどの値も候補にならない。

**証明:** `c` に関する帰納法。各値 `v` の「再訪しない」から古典的な場合分けで
「ある時刻以後は現れない」を取り出し、帯全体の回避境界を合成する。補助補題。

### `EventualHighCandidateTail.candidate_diverges_or_recurrence` (L102)

**主張:** 回廊では、`∀ K` についていずれ `d > K` が恒久化する（発散）か、
`target < c` なる値 `c` と時刻 `M₁` があって、`M₁` 以後は `c ≤ d(k)`（床）かつ
`c` は任意に遅い時計で候補として再訪する。

**証明:** 発散でないとすると、ある `K` の下へ無限に戻るので、`corridor_candidate_bounded_recurrence`
により単一の再訪値 `c₀ ≤ K` が取れ、最小再訪値 `c` に取り直す。回廊の高候補則から `target < c`。
最小性より帯 `(target, c)` の各値は再訪せず、一様回避境界 `M₀` が得られる。`M₀ + cutoff + 1` 以後の
時計では候補は `target` 超かつ帯を回避するので `c` 以上、すなわち床が成立する。

### `EventualHighCandidateTail.diverges_or_rigidEventStream` (L166)

**主張:** 回廊では、発散するか、`target < c` なる値 `c` があって任意に遅いuse clock `m` で
完全なrigid eventが起きる: `d(m) = c`、時刻 `m` への入りは合法減算で `a(m) = c + m + 1` はfresh初出、
時刻 `m+1` はforced additionで `a(m+1) = c + 2m + 2`、そして後続値 `c + m` は時刻 `m+1` までに既訪問。

**証明:** 前定理の右枝の床と再訪から、十分遅いuse clockを選んで
`corridor_recurringCandidate_event` を適用するだけである。

## 全体の中での位置づけ

`SharpResidualKernel` のA枝は本定理により「発散残余」と「rigid event stream」へ分岐した。
発散残余 `a(m) − m → ∞` は自由事実ではない（実軌道は `a(99734) = 19` のような低値の遅い着地を持つ）。
event stream側のper-use需要 `c + m ∈ 履歴` は、`docs/CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md` の
supply/demand解析が示すとおり、倍化clock格子上の自己供給しか残されていない。次の研究対象は
この需要の供給injectivityである。
