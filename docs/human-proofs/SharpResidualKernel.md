# SharpResidualKernel

**役割:** 仮想反例(missing permanent tail)の残余kernelの両枝を `SharpCorridor` / `SharpResetStream` という2つの受け渡し証明書に束ね、二択定理 `sharpResidualKernel` で仮想反例を必ずどちらかへ送る。

## このモジュールの役割

`TargetTailResidualKernel.lean` は仮想反例をA枝「eventual-high candidate corridor」とB枝「固定root付きunbounded right-terminal stream」に二分した。その後、両枝は独立な複数のモジュールで精密化された: A枝には回廊の値法則・fresh着地列・強制加算の再発・自給自足供給窓(`EventualHighCorridorStructure.lean` / `EventualHighCorridorSupply.lean`)、B枝にはblocker床・blocker非有界・upward blocker reset(`TargetStreamBlockerUnbounded.lean` / `TargetStreamUpwardResets.lean`)が加わった。本モジュールはこれらの成果を、A枝は一つの明示的cutoff、B枝は一つの明示的rootにおいて束ね、以後の研究が枝ごとに単一の証明書だけを消費すればよい形にする。

## 主要な定義

### `SharpCorridor` (L27)

`SharpCorridor target tailStart cutoff` は、eventual-high回廊について現在知られていることをcutoff一点で束ねたProp構造体で、次の6フィールドを持つ。以下 `nextSubtractionCandidate n = a n − (n + 1)` は時刻 `n + 1` の減算候補、`upperTri t = t(t+1)/2` は上三角数で、普遍軌道上界 `a t ≤ upperTri t` が常に成り立つことに注意する。

- `tail_le`: `tailStart ≤ cutoff`。cutoffはtail開始以後にある。
- `candidate_high`: `cutoff ≤ n` なる全時刻で `target < nextSubtractionCandidate (n + 1)`。回廊の定義条項である。
- `value_law`(回廊値法則): `cutoff < n` なる全時刻で `target + (n + 1) < a n`。回廊内の軌道値はtargetに自分のclockを足した量よりさらに上に浮く。
- `fresh_landings`: 任意の `M` に対し `M ≤ n` で、`target + (n + 2) < a (n + 1)` かつ `a (n + 1)` が時刻 `n + 1` での初出となる着地が存在する。回廊は任意に遅いfresh着地を無限個生む。
- `forced_additions`: 任意の `M` に対し `M ≤ n` で強制加算(`¬ CanSubtract (n+1)`)が起きる。回廊は強制加算を無限回再発させる。
- `self_fueled`(供給窓): `cutoff + 1 ≤ n` の強制加算で候補が事前hull `upperTri cutoff` を超えるなら、供給者時刻 `t` が `cutoff < t ≤ n` に存在して `a t = nextSubtractionCandidate n`、`t + 1 + target < nextSubtractionCandidate n`、かつ `nextSubtractionCandidate n ≤ upperTri t` を満たす。すなわち大きな候補を塞ぐ既出値は回廊内部の着地に限られ、無限回廊は有限seedを除いて自給自足系である。

### `SharpResetStream` (L44)

`SharpResetStream target tailStart root rootFirstTime` は、固定root付きright-terminal streamについて現在知られていることをroot一点で束ねたProp構造体で、次の7フィールドを持つ。comb(櫛状区間)`HistoryTerminatedComb start length blocker` とmacro対 `TargetMacroSuccessor` の語彙は `TargetStreamBlockerUnbounded.md` / `TargetStreamUpwardResets.md` を参照。

- `target_lt_root`: `target < root`。
- `root_first` / `root_preTail`: rootは時刻 `rootFirstTime ≤ tailStart` で初出する。分離rootは有限pre-tail接頭辞の中の実在の値である。
- `stream`: `UnboundedRightTerminalStream target tailStart root`。tail内の全combのentryはroot以上で、任意に遅いtarget-low完了combが存在する。
- `blocker_floor`: tail真内部の全完了combで `root ≤ blocker`。
- `blockers_unbounded`: 任意の天井 `B` に対し、tail真内部・target-lowの完了combで `B < blocker` を満たすものが存在する。
- `upward_resets`: 任意のcutoffに対し、cutoff後に始まる連続macro対で `blocker₁ < blocker₂`(upward reset)かつ `a s₁ ≤ blocker₂`(第一fresh区間全体が新blockerの左側)を満たすものが存在する。

## 定理と証明

### `MissingPermanentAboveTail.sharpResidualKernel` (L67)

**主張:** 仮想反例 `MissingPermanentAboveTail target tailStart` のもとで、

`∃ cutoff, SharpCorridor target tailStart cutoff`　または　`∃ root rootFirstTime, SharpResetStream target tailStart root rootFirstTime`

が成り立つ。すなわちすべての仮想反例はsharp回廊証明書かsharp reset-stream証明書のどちらかを持つ。

**証明:** 既存の二分法 `eventualHigh_or_unboundedRightTerminal` で場合分けし、各枝で既にコミット済みの精密化定理をフィールドに詰めるだけである。新しい解析は行わない。

**A枝。** 二分法から `tailStart ≤ cutoff` と `candidate_high` が直接得られる。残りのフィールドは次の定理で埋める。

- `value_law` ← `corridor_value_law`: `candidate_high` を時刻 `n − 1` に適用すると `target < nextSubtractionCandidate n = a n − (n + 1)`、すなわち `target + (n + 1) < a n`。
- `fresh_landings` ← `EventualHighCandidateTail.infinitely_many_high_fresh_landings`: 無条件定理「強制加算の永久ray(区間)は存在しない」により任意に遅い合法減算があり、回廊内の減算着地は値法則からclock超のfresh値になる。
- `forced_additions` ← `corridor_infinitely_many_forcedAdditions`: cutoff後に合法減算が永続すると値は毎歩2以上下がり続けるが、値法則が全post-cutoff値を正に保つので、十分長く走らせると矛盾する。
- `self_fueled` ← `corridor_forcedAddition_supplier`: 回廊内では値法則により `CanSubtract` のclock条項が常に満たされるので、強制加算の理由は履歴条項、すなわち候補が既出であることに限られる。その既出の出現時刻 `t` が供給者である。候補が `upperTri cutoff` を超え、かつ `a t ≤ upperTri t` なので、hullの単調性から `t > cutoff` が従い、時刻 `t` の値法則が `t + 1 + target < 候補` を与える。

**B枝。** 二分法から `root`・`rootFirstTime`・`target < root`・初出証明・pre-tail条件・streamが得られる。残りは

- `blocker_floor` ← `UnboundedRightTerminalStream.blocker_floor`(`TargetStreamBlockerUnbounded.lean`)、
- `blockers_unbounded` ← `UnboundedRightTerminalStream.exists_blocker_gt`(同上)、
- `upward_resets` ← `UnboundedRightTerminalStream.exists_upwardReset_entry_le_after`(`TargetStreamUpwardResets.lean`)

をそれぞれ引数を合わせて詰める。∎

### `SharpResetStream.exists_blocker_in_band` (L101)

**主張:** sharp reset-streamでは、任意の天井 `B` に対し、tail真内部・target-lowの完了combで `root ≤ blocker` かつ `B < blocker` を**同一のcombで**満たすものが存在する。

**証明:** `blockers_unbounded` の証人combに `blocker_floor` を適用して床の不等式を付け加える。blocker床とblocker脱出が一つのcombで合成されることを明示する利用者向け補題である。∎

## 全体の中での位置づけ

2026-09-01の5系統並列精密化の合流点であり、証明地図(docs/PROOF_MAP.md)の「2026-09-01 午後: sharp residual kernel(A/B両枝の並列精密化)」の受け渡しkernelに対応する。入力は、基盤となる二分法の `TargetTailResidualKernel.lean`、B枝の `TargetStreamBlockerUnbounded.lean`・`TargetStreamUpwardResets.lean`、A枝の `EventualHighCorridorStructure.lean`・`EventualHighCorridorSupply.lean` である。

以後の研究は仮想反例を直接扱う代わりに、`SharpCorridor` / `SharpResetStream` の2構造体だけを消費すればよい。残る数学的義務は枝ごとに一つずつである: A枝ではsharp回廊(自給自足の無限系)からcanonical high不変量ないし矛盾を構成すること、B枝では無限個のupward resetの返済(reset repayment、docs/RESET_REPAYMENT_AUDIT_2026-09-01.md で `STOPPED` 中の予想)を新しい大域不変量で排除することである。
