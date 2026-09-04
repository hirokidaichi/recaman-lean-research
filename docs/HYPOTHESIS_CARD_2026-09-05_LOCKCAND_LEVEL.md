# Hypothesis card: lockcand の level 下界は provenance を使うか

- ID: `H-20260905-01`
- Owner: AI research epoch 2026-09-05（30分 bounded unit）
- Created: 2026-09-05
- Status: `PROVED-LEAN`
- Research branch: 非全射方向。landing floor の blocker provenance

## Exact statement

任意の `i v k n : Nat` について、comb 末端の着地 clock を `c = i + 1`、固定 pair を `k` とする。
初訪問 clock が comb 末端より前で、固定が pair `k` まで residue wrap を起こさないための予算を持つなら、

```text
n < i + 1  and  13 + 7k <= v
  -> 2n + 14 + 4k <= 2(i+1) + v - 1 - 3k.
```

右辺は `lockcand` の値 `w = 2c+v-1-3k` である。従って `0 < n` なら

```text
2 <= w / n.
```

Lean declarations は `popup_lock_candidate_margin`、
`popup_lock_candidate_gt_twice_earlier`、`popup_lock_candidate_level_ge_two`。

probe との対応では `k = i_gen`。`lockcand` は pair `i_gen` の候補が既訪問で固定がさらに続いた事象なので、
その pair より前に residue wrap はなく、`13+7*i_gen <= v` である。初訪問は既訪問判定より前であり、
probe の stronger check として `n < c` を使う。

## Why it would matter

- Frontier obligation discharged: `E-041` 後続命題 (A') の非自明と考えられていた `lockcand` 部分を判定する。
- Stronger than an existing identity or equivalent reformulation because: exact な sharp margin
  `2n+14+4k <= w` を与え、単なる観測 `w/n >= 2` より定数項まで強い。
- Smallest useful consequence: canonical blocker provenance を一切使わずに `lockcand` の初訪問 level が2以上と分かる。
  したがって (A') は landing floor を進める causal input ではない。

## Provenance and dependencies

- Definitions used: `lockcand` 値 `2c+v-1-3k`、`LockResidue` の no-wrap budget `13+7k<=v`。
- Lean theorems used: 算術核には `omega` のみ。`popup_lock_residues` が同じ budget の意味を与える。
- Unverified mathematical assumptions: probe event から budget への対応は C++ の arc detector と
  `E-037` の residue law に依存する。今回の Lean statement 自体には実軌道仮定がない。
- Literature source or analogy: Chaffin の ping-pong arc の residue 非増加区間。

## Falsification plan

- Small and boundary cases: `n=i`, `v=13+7k` で margin が等号になることを確認する。
- Adversarial or weakened-history model: 実軌道・history を全て除いて算術だけで証明できるか試す。
- Discovery range: `blocker_provenance_probe` の `c < 10^9` の全 `lockcand`。
- Frozen holdout range: 同じ凍結済み run の `10^9 <= c < 10^10`。
- Maximum one permitted repair: なし。sharp margin が偽なら level 下界だけへ弱めず `REFUTED` とする。
- Stop condition: data で budget/time/margin の違反が1件、または Lean で exact margin が証明不能。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-05 | `PROVED-LEAN` | `lake env lean Recaman/LockResidue.lean` | sharp margin と quotient 下界を実軌道仮定なしで証明。 |
| 2026-09-05 | `COMPUTED` | revision `d47bc31`; `blocker_provenance_probe 10000000000`、`sh docs/data/provenance/post.sh records.txt` | discovery 237件・holdout 372件。budget/time/formula/margin/level 違反は各0。最小 margin slack は discovery 89,148、holdout 72,228。既存 summary は実行時間以外を再現。 |

## Semantic audit

- Informal statement implies formal statement: no-wrap budget と `n<c=i+1` をそのまま仮定にしている。
- Formal statement implies intended consequence: positive な初訪問 clock で `2<=w/n` が直接従う。
- Counterfactual examples that should make the statement false: budget を `v=3k-2` まで弱めると
  `n=i` で margin は破れる。時刻順序を `n=c` まで弱めても sharp 定数14は失われる。
- Could the theorem be proved from weaker or vacuous assumptions?: 実軌道・freshness・same-arc provenance は不要。
  これは意図した no-go 結論であり、(A') が causal 情報を持たないことを示す。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: time order と no-wrap budget だけを
  意図的に残した。実際の event への bridge は計算監査し、一般の event structure は新設しない。

## Decision

- Continue / formalize / refute / stop: exact inequality は `PROVED-LEAN`。`lockcand` level 下界を provenance
  仮説として追う枝は `STOPPED`。
- Reason: proposed (A') の `lockcand` 部分は actual-orbit ancestry ではなく、no-wrap residue budget の
  sharp な算術的帰結だった。
- Reopen only if: level ではなく、同じ弧のどの run が候補値を初出させたかを指定する exact causal statement が得られた場合。
