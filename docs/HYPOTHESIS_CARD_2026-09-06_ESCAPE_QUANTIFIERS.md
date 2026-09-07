# Hypothesis card: eventual landing floor の量化子監査

- ID: `H-20260906-03`
- Owner: Codex（proposer / falsifier / formalizer / auditor を順に分離）
- Created: 2026-09-06
- Status: `PROVED-LEAN`
- Research branch: 戦略地図の意味監査。`E-028` の自由な cutoff と固定 prefix の接続
- Source revision: `8a4314d7f65c728d5c6fe6584e1469de4e08332d`

## Exact statement

今回の bounded question は「自由な cutoff を持つ eventual floor は、未訪問値の永久欠損を
証明する新しい入力なのか、それとも既存の no-late-revisit の無条件な帰結か」である。

canonical `a : Nat → Nat` について、次を先に凍結する。

```text
(Q1) ∀ v s t, s < t → a(s) = v → a(t) = v → t ≤ v.
(Q2) ∀ B, ∃ N, ∀ n, N ≤ n → B < a(n).
(Q3) ∃ m H, m ∉ valuesThrough(H)
              ∧ (∃ N, ∀ n, N ≤ n → m < a(n))
              ∧ (∃ t, H < t ∧ a(t) = m).
```

Q2 は全時刻の floor であり、どんな arc-bottom predicate に制限しても成立する。
Q3 の凍結した具体例は `m=4, H=4, t=131`。Q2 から得た `N` を `H` 以下と仮定してはならない。

比較対象として有効な十分条件を分離する。

```text
(Q4) ∀ m H, m ∉ valuesThrough(H)
      → (∀ n, H < n → m < a(n)) → ∀ n, a(n) ≠ m.
```

Q4 は証明接続の仕様であり、新しい研究 invariant として数えない。arc 版を使うなら、cutoff を跨ぐ
arc を含めた全将来着地の被覆を別途示す必要がある。未知 cutoff の存在だけでは Q4 の入力にならない。

## Why it would matter

- Frontier obligation discharged: `E-028` の「eventual floor だけで非全射」の読みに対する判定。
- Stronger than an existing identity or equivalent reformulation because: Q2 は missing-target 仮定を外す。
  研究上の成果は elementary な Q2 自体の新規性ではなく、十分条件とされていた Q2 が無条件で
  成立すると示し、cutoff に関する未証明 edge を露出させること。
- Smallest useful consequence: Q2 を単独の非全射攻略目標から外し、prefix と同じ cutoff の
  forward exclusion、およびそれを供給する independently testable history inequality を要求する。

## Provenance and dependencies

- Definitions used: `Basic.a`, `CanSubtract`, `valuesThrough`。
- Lean theorems used: `recurrence`, `mem_valuesThrough_iff`。既存
  `a_succ_ne_of_seen`（`PermanentAboveCorridorNineteenElimination`）は同じ機構の one-step 版。
- Unverified mathematical assumptions: なしを目指す。Q2 の cutoff は非定量的である。
- Literature source or analogy: 有限値集合の各値が有限回しか出なければ列は無限大へ逃げるという初等論法。

## Falsification plan

- Small and boundary cases: `v=0`、`t=v` の等号、実際の重複42、遅い初出4（clock 131）。
- Adversarial or weakened-history model: subtraction の freshness を外す variant で Q1 が破れるか検査。
  また全射な `b(n)=n` にも rising floor があるため、成長だけから穴の存在を出す論理を拒否する。
- Discovery range: canonical clocks `0..1000`。
- Frozen holdout range: canonical clocks `1001..200000`。Q1 の全repeatを exact replay で照合。
  horizon は Q2 の証明に使わない。
- Maximum one permitted repair: なし。Q1/Q2 が失敗すれば原因を記録して停止。
- Stop condition: Q1 の反例、Q2 の証明に occurrence/coverage 仮定の混入、または Q3 の固定例が
  失敗した時点で停止。成立時は cutoff 接続の修正と戦略地図・issue を作成して閉じる。

## Informal dependency chain before Lean

1. clock `t` の減算出力は直前履歴にない。加算出力は `t` 以上。
2. 従って時刻 `s<t` と同じ値 `v` に再訪するなら `t≤v`（Q1）。
3. 値 `v` が一度も現れなければ初めから避ける。現れたなら一つの出現時刻 `s` を取り、
   `max(s,v)+1` 以降では Q1 により避ける。
4. 有限集合 `0..B` の各 avoidance cutoff の最大を取る（Nat induction）と Q2。
5. Q2 と `4∉valuesThrough 4`, `a 131=4` を合成して Q3。
6. Q4 は `n≤H` と `H<n` の場合分け。この同じ `H` を供給する数学が本当の未解決入力。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `CONJECTURED` | card frozen before implementation at source revision above | Q1–Q4 と反証 protocol を固定。 |

## Semantic audit

- Informal statement implies formal statement: missing target、surjectivity、arc completion を Q1/Q2 の仮定に置かない。
- Formal statement implies intended consequence: Q2 は任意 predicate で選んだ時刻の eventual floor も含意する。
- Counterfactual examples that should make the statement false: freshness を外した late repeat は Q1 を破る。
- Could the theorem be proved from weaker or vacuous assumptions?: Q2 は標準軌道の full provenance を使わない。
  それ自体が今回調べる free-route である。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: Q1/Q3 は実軌道 `a`。
  Q4 の prefix cutoff と future cutoff は同じ変数に束縛する。

## Final evidence

| Date | Label | Reproduction | Result |
|---|---|---|---|
| 2026-09-06 | `PROVED-LEAN` | [exact outputs](data/strategy_2026-09-06/README.md) / [監査と論証](STRATEGY_AUDIT_2026-09-06.md) | Q1–Q4とrising-floor比較例の7定理を `Recaman/EventualEscape.lean` で認証。discovery/holdoutのrepeat検査も違反0。 |

## Decision

- Continue / formalize / refute / stop: 完了。E-028の自由cutoff routeをSTOPPEDにし、同じcutoffの接続へ修正。
- Reason: 現在の優先目標に非定量的な恒真命題が混入している可能性がある。
- Reopen only if: このunitはQ1–Q4と戦略修正の判定まで。survival比の新しい定数探索は行わない。
