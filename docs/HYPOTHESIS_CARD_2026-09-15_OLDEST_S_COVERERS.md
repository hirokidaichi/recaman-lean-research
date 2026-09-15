# Hypothesis card: who can cover the oldest subtraction of an SS=2 lag-11 donor?

- ID: `H-20260915-19`
- Created: 2026-09-15 17:20 JST
- Status: `COMPUTED`（E-347）。Lean 化した局所分類は E-348 を参照（別 commit）
- Research branch: issue #73、E-345 の次 gate G2「ss=2 donor の最古 S は lag∈{3,7} の緊密回避 B に被覆されない」の前段
- Probes: `experiments/issue73_20260915/lag7_cover_configs.py`（bit-level、周期性なし、2^11×2^7 の直接列挙）、
  `experiments/issue73_20260915/oldest_s_coverers.cpp`（E-345 の census に診断列を追加、E-179 と語数一致）
- Output: `docs/data/issue73_20260915/lag7_cover_configs.txt`、`docs/data/issue73_20260915/oldest_s_coverers.txt`

## Exact statement

E-345 と同じ設定。donor `u0` は最小 P2 窓の長さ（lag）11・`ssCount = 2` の供給 phase。長さ 11 の最小 ss=2 P2 語はちょうど 7 個
（newest-first：d1=AAASSSASASA, d2=ASAAASSSASA, d3=ASASAAASSSA, d4=ASSAAAASSAS, d5=ASSAAASAASS, d6=SAAASAASSSA, d7=SAAASSAAASS）。
**最古 S の offset は d1,d2,d3,d6 で 10、d4,d5,d7 で 11**（窓の最古位置が S とは限らない。Lean の `oldestSubtractionPhase = endpointPhase p u d` は
offset d の phase を指すので、d1 型では `endpointPhase` は A の位置になる。E-345 の census は最古 S を正しく取っている。§Q3 参照）。
`s*(u0)` = 最古 S の phase。問い：

```text
Q1 (bit-level)  最小 lag-7 窓（w1=SAAAASS, w2=ASAASAS）が s*(u0) を被覆できる配置（donor 語, u−u0, 窓内 offset）は何通りか
Q2 (census)     p≤22 の周期語で、s*(u0) を被覆する他の供給 phase u の lag の分布は。lag-7 の被覆者は緊密回避 B の要素になるか
Q3 (Lean 側)    既存 Lean の Gate T6 文は s* を `oldestSubtractionPhase p u0 (lag u0)` = offset 11 の phase としている。
                offset 10 型の donor（d1,d2,d3,d6）では Lean の「供出 S」は実際の最古 S と異なる。整合を確認する
```

## Results

- **Q1**: 3 通りだけ。全て **w1 で、s* が窓の newest bit（offset 1）**、すなわち `u = s* + 1` で、lag-7 窓は donor 窓と s* だけを共有し残りは donor より古い側にある。
  donor は d1, d2, d4 に限る（条件は「s* の一つ新しい bit が A」）。d3, d5, d6, d7 では不可能。lag-3 の被覆は既存 Lean 補題
  `ss2_lag_lt_fifteen_disjoint_from_aas` が排除済み。
- **Q2**（ss=2 lag-11 donor、p=22：4,470 donor）: s* の被覆者は lag 7 が 68、lag 11 が 126、lag 15 が 105、lag 19 が 274、lag 23 が 212、… と
  **lag ≥ 11 の長い窓が大半**。lag-7 被覆者 68 のうち 53 は N([u]) に「U∖{u0} の他の窓が被覆しない private phase」を持つが 15 は持たない。
  被覆者が緊密回避 B の要素になった例は 0（E-345 と同じ）。
- **Q3**: 7 語のうち 4 語で窓の最古位置が A。Lean の Gate T6 文（`oldestSubtractionPhase`）が実際に供出しているのは offset 11 の phase で、
  d1 型では**減算ではない phase** を「供出」していることになる。`oldest_is_subtraction` は `hS : e (u − d) = false` を仮定に持つので矛盾はしないが、
  一般 p の Gate T6 を Lean で述べるときは「最古 S」を語ごとに正しく定義し直す必要がある（次の Lean unit の前提）。

## Decision

- G2 は「窓ごと」には証明できない：lag ≥ 11 の窓が s* を被覆する周期語は多数ある。**G1（緊密回避 B の lag は {3,7}）が本質**で、
  G2 は G1 の下で lag-7 の 3 配置だけを扱えばよい。lag-7 の 3 配置では被覆窓が donor より古い側に全体が乗るので、
  その窓の他の 2 phase（s*−5, s*−6）を B の他の要素がどう被覆するかが緊密性の焦点になる（w1 は常に lag-3 の兄弟 u−3 を伴い、
  u−3 は phase u−6 を被覆する）。
- Lean 化（E-348）：Q1 の分類を実際の符号語 `e` 上で述べる。緊密部分集合には触れない。
- private-phase 論法は 15/68 で破綻するので G2 の証明には使えない。

## Stop conditions

- G1 が p ≤ 31 の網羅で破れたら（lag ≥ 11 の要素を持つ緊密回避 B）、Gate T6 の一般形は最古 S 以外の供出則へ移る。
