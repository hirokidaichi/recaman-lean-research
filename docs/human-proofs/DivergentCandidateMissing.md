# DivergentCandidateMissing

**役割:** candidate walkの永続的な床は下の値窓を丸ごと凍結するので、発散するcandidate walkは任意の限界を超える永久欠損値を残す。A枝capstoneは「欠損値非有界 ∨ rigid event stream」になる。

## このモジュールの役割

`EventualHighCorridorDichotomy` はA枝を「candidate walkの発散」と「再訪候補でのrigid event stream」に
二分した。本モジュールは発散側の逃げ道に値段をつける。candidateが恒久的に `K` を超えるとき、
軌道値は毎時刻 `K + clock + 1` を超えるため、窓 `[0, N + B + 3]` には将来の着地機会がない。
履歴は1時刻1値なので窓の上部 `(B, N + B + 3]` に未訪問値が必ず残り、それは永久欠損である。
発散はこの床を任意の `K` について与えるから、**欠損値は任意の限界の上に存在する**。

## 定理と証明

### `candidateFloor_forces_missing_above` (L34)

**主張:** `∀ m ≥ N, K < a(m) − (m+1)` かつ `B + 2 ≤ K` なら、`B < u` で軌道が一度も
訪れない値 `u` が存在する。

**証明:** 床から値法則 `K + m + 1 < a(m)`（`m ≥ N`）。窓 `(B, N + B + 3]` の値がすべて
時刻 `N` までに訪問済みなら、`List.range (N+B+4) ⊆ List.range (B+1) ++ valuesThrough N` の
Nodup部分集合長から `N + B + 4 ≤ N + B + 2` となり矛盾。未訪問の `u` について、時刻 `N` 以前の
訪問は未訪問性に反し、時刻 `N + 1` 以後は値法則により `a(t) > B + t + 3 ≥ B + N + 4 > u`。

### `divergent_candidates_missing_unbounded` (L79)

**主張:** candidate walkが発散する（`∀ K ∃ N ∀ m ≥ N, K < candidate`）なら、
任意の `B` の上に永久欠損値がある。

**証明:** 発散を `K := B + 2` で具体化して前定理を適用する。

### `EventualHighCandidateTail.missingUnbounded_or_rigidEventStream` (L93)

**主張:** eventual-high回廊では、欠損値が非有界に存在するか、ある `c > target` の
任意に遅いuse clockで完全なrigid eventが起きる。

**証明:** `diverges_or_rigidEventStream` の左枝に前定理を合成する。

## 全体の中での位置づけ

A枝（`SharpCorridor`）の最終形である。仮想反例のA枝は、「欠損値集合が非有界」という
大きな代償を払うか、`EventualHighCorridorRecurrence` のrigid event streamの需要
`c + m ∈ 履歴` を無限に供給し続けるかのどちらかしかない。第二欠損値定理
（`EventualHighCorridorSecondMissing`）の計数＋凍結法をレベル `K` に一般化した形であり、
次の研究対象はevent stream側の供給injectivityである。
