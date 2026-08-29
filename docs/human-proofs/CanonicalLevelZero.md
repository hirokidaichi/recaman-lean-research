# CanonicalLevelZero

**役割:** canonical開始点のポテンシャル水準 0 の残余を、後継境界 `a(target) = target + 1` へ縮約し、さらにその境界では二歩以内に目標が必ず出現することを示して水準 0 を完全に消去する。

## このモジュールの役割

`CanonicalOracle` はcanonical開始点(目標 `m` に紐づく標準的な探索開始ノード)の未解決部分をポテンシャル水準 0, 1, 2 の帯に絞った。本モジュールはそのうち水準 0 を扱う。通常の非負ファネル(非負ポテンシャル帯での商下降定理)を適用すると、水準 0 の状態は被覆・より小さい意味的 normal anchor・または「時刻がちょうど `target` で座標が `(1,1)`、すなわち `a(target) = target + 1`」という一点の後継境界のいずれかに落ちる。最後にこの後継境界では、実軌道を二歩追跡するだけで目標が出現することを直接証明する。したがって水準 0 は残余として残らない。

## 主要な定義

### `CanonicalLowLevelResidual.IsZero` (L16)

低水準残余 `CanonicalLowLevelResidual` の水準が 0 である場合の証明相当(proof-relevant)な精密化である。残余は `Prop` 値なので自然数の証人を計算的に射影できない。そのため構成子はすべての証拠(時刻、座標、証明書、初出、`potential q r = 0` など)を改めて保持し、`source_eq` で元の残余がその証拠から作られた `low` に一致することを記録する。

### `CanonicalSuccessorResidual` (L39)

水準 0 の解析後に残る最小の未解決形である。時刻は目標そのもの(`parent = targetStartNode target`)、座標は `CoordinatesAt target 1 1`、すなわち `a(target) = target + 1` に固定される。証明書と現在値の初出時刻も保持する。

## 定理と証明

### `canonicalLowLevel_zero_phaseSemanticStep_or_successor` (L55)

**主張:** 水準 0 の canonical 残余は、(1) 目標の出現、(2) 位相探索ランクを厳密に下げる意味的子ノード、(3) 後継境界 `CanonicalSuccessorResidual` のいずれかに帰着する。

**証明:** 残余から時刻 `n`、座標 `(q,r)`、`potential q r = 0` を取り出す。非負ファネルの定理 `nonnegative_epoch_lowQuotient_or_coverage_with_value` を適用すると、将来時刻 `t ≥ n` と座標 `(k,s)` が得られ、ポテンシャルは保存され(よって `potential k s = 0`)、「低商到達」か「被覆」のどちらかが成り立つ。

*低商枝。* まず `k = 0` はあり得ない: `k = 0` とポテンシャル 0 から `s = 0` となり `a(t) = 0` になるが、正の時刻の軌道値は正である。よって `k = 1`、そしてポテンシャル 0 (`s − upperTri(1) = s − 1 = 0`) から `s = 1`。このとき定理は「時刻が変わらない(`t = n`)」か「値が厳密に下がった」かの二者択一も返す。

  - `t = n` の場合、商保存から `q = 1`、ポテンシャル 0 から `r = 1`、座標方程式から `a(n) = n + 1` が従う。さらに証明書の `near_target` は `n = target − 1` または `n = target` を言うが、前者だと `a(n) = target` となり `target < a(n)` に反する。よって `n = target` であり、保持していた証拠一式をそのまま詰めて後継境界 (3) を構成する。
  - 値が厳密に下がった場合、`a(t)` は `k = 1, s = 1` から `a(t) = t + 1 ≥ target` を満たす(証明書の `time_ready` による)。履歴から `a(t)` の初出時刻を取り、子 `⟨t, a t, normal, a t⟩` を作る。horizon は前進し anchor は厳密に下がるのでランク下降 (2) が成り立つ。重要な注意として、得られた初出は必ず自分自身の horizon `t` で証明されており、古い canonical horizon で証明されることはない。

*被覆枝。* `CanonicalOracle` の `canonicalCoverage_phaseSemantic` により (1) または (2) に落ちる。

### `canonicalSuccessorResidual_two` (L146)

**主張:** 後継境界は実在する: 目標 2 では `a(2) = 3 = 2 + 1` が成り立ち、`CanonicalSuccessorResidual 2 (targetStartNode 2)` が構成できる。

**証明:** `a(2) = 3` の初出が時刻 2 であることを有限検査(`decide`)で確認し、座標 `(1,1)` と証明書を具体的に与える。

### `CanonicalSuccessorResidual.target_occurs` (L168)

**主張:** 後継境界は実は「失敗」ではなく、二歩以内に目標が出現する。すなわち正の目標 `target` に対し `CanonicalSuccessorResidual target parent` ならば `∃ witness, a(witness) = target`。

**証明:** 仮定から `a(target) = target + 1` である。時刻 `target + 1` での減算候補は `a(target) − (target + 1) = 0` だが、`0 = a(0)` はすでに履歴にあるので減算は不可能(blocked)であり、強制加算により

```text
a(target + 1) = (target + 1) + (target + 1) = 2·target + 2
```

となる。次の時刻 `target + 2` での減算候補は `2·target + 2 − (target + 2) = target` である。

  - 減算が合法なら `a(target + 2) = target` となり、目標が時刻 `target + 2` に出現する。
  - 減算が阻止されるなら、候補 `target` は正なので阻止の理由は「既出」しかない。すなわち `target ∈ valuesThrough(target + 1)` であり、履歴の成員は出現時刻を持つから、目標はすでにどこかの時刻で出現している。

どちらの場合も目標の出現証人が得られる。

## 全体の中での位置づけ

証明地図の「canonical開始 — 局所閉包」の一角を成す。`CanonicalOracle` の低水準残余のうち水準 0 を担当し、`CanonicalComplete` の統合定理 `targetStartInvariant_phaseSemanticStep_or_forced` では本モジュールの二定理(縮約と `target_occurs`)を続けて使うことで、水準 0 の枝が「目標出現」へ完全に吸収される。残る水準 1・2 はそれぞれ `CanonicalLevelOne`・`CanonicalLevelTwo` が扱う。
