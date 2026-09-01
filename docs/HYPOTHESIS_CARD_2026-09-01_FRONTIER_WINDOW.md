# Hypothesis card: `descent-window frontier invariant`

- ID: `H-20260901-02`
- Owner: sharp-kernel sprint
- Created: 2026-09-01
- Status: `CONJECTURED`
- Research branch: canonical-prefix不変量（step語センサスのforced-S族の共通機構）

## Exact statement

canonical軌道（`a 0 = 0` からの実軌道）について: AASSA窓（forced addition 2回、
合法減算2回で `a+n` と `a−4` にfresh着地、forced addition 1回）が時刻 `n` の値 `a` から
始まるとき、値 `a−5` は時刻 `n+5` の時点で未訪問である（従って次stepは合法減算で `a−5` に着地）。

一般形（予想）: canonical軌道のSS二連降下のfresh着地対 `(v, v−(n+2))` の直下の値は、
その時点の「未訪問低値フロンティア」に属する——すなわち窓の3つの減算着地
`a+n, a−4, a−5` は連続するfirst occurrenceである。

## Why it would matter

- Frontier obligation discharged: センサスの残る全forced-S禁止因子（`AASSAA`, `SAAASAA`,
  `SSSSSAA`族など）の統一的説明。canonical reachabilityを本質的に使う初の局所不変量になる。
- Stronger than an existing identity because: seeded exact反例（value 6, seen {6,5,1,0}, clock 4）
  により**局所法則ではない**ことが証明済み。成立するならcanonical提供の大域情報そのもの。
- Smallest useful consequence: right-record則（診断用に降格中）と同じ「canonical固有経験則」群に
  初の証明が入れば、A枝・B枝両方のcanonical入力ゲートが開く。

## Provenance and dependencies

- Definitions used: `valuesThrough`, `FirstAt`, mex/hole構造
- Lean theorems used: `NoDoubleAdditionRun`（SAAS禁止、文脈の前提がAであること）、
  `LoopClosingSubtraction`
- Unverified mathematical assumptions: なし
- Literature source or analogy: `LeastTailLedgerProvenance`のhole-provenance機構、
  right-record計算監査（`RIGHT_RECORD_COMPUTATIONAL_AUDIT_2026-08-31.md`）

## Falsification plan

- Small and boundary cases: canonical 1e7の全251出現で `a−5` の初出がちょうど `n+6`（違反0）。
- Adversarial or weakened-history model: seeded反例は既知（局所形は死んでいる）。
  攻撃対象はcanonical不変量のみ。
- Discovery range: 1e9センサス（AASSA 1,476回、違反0）。
- Frozen holdout range: 1e9〜4e9で実施済み（違反0）。次のholdoutは4e9以降とする。
- Maximum one permitted repair: 「a−5」を「窓直下の最初の未訪問値」に置換する弱形1回。
- Stop condition: holdoutで違反が出る、または不変量の証明義務が
  「フロンティア値の将来出現」（＝全射性の再符号化）と同値になったとき。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-01 | `OBSERVED` | step_word_census_probe 1e9 | AASSA→S 1,476/1,476 |
| 2026-09-01 | `REFUTED-LOCALLY` | aassaa_seed.py | seeded exact反例（3-blocker seed） |
| 2026-09-01 | `OBSERVED` | canonical_check.py 1e7 | 251出現全てで a−5 初出 = n+6 |
| 2026-09-01 | `OBSERVED` | aassa_holdout (1e9, 4e9] frozen | AASSA 698回・違反0、SAAASA 9,650回・違反0、SSAAAAS 686回でS継続0（定理と一致） |

## Semantic audit

- Informal statement implies formal statement: 「フロンティアに乗る」は
  「3着地が連続first occurrence」として正確に形式化可能。
- Counterfactual examples: 「a−5 visited かつ a−4 unvisited」のhole配置がcanonicalに
  到達可能なら偽。hole-provenance機構で排除できるかが核心。
- Could it be proved from weaker assumptions?: 局所仮定からは不可能（seeded反例により証明済み）。
- Omitted provenance risk: canonical reachabilityの使用は本質的であり、省略すると偽になる。

## Decision

- Continue / formalize / refute / stop: `CONTINUE`（holdout監査→hole-provenance経由の紙上攻撃）
- Reason: canonical固有不変量の最小の実例であり、right-record則より局所的で証明可能性が高い。
- Reopen only if: —
