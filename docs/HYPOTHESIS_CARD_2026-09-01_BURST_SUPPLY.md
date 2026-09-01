# Hypothesis card: `burst-stream supply injectivity`

- ID: `H-20260901-01`
- Owner: sharp-kernel sprint
- Created: 2026-09-01
- Status: `CONJECTURED`
- Research branch: A枝（eventual-high corridor）、rigid event stream側

## Exact statement

`SharpCorridor`のrecurrence枝（`missingUnbounded_or_burstStream`の右disjunct）を仮定する:
値 `c > target` があり、任意に遅いuse clock `m` で `d(m) = c`、対角fresh減算入り
`a(m) = c + m + 1`、加算3連burst、および需要 `c + m ∈ valuesThrough (m+1)` が成立する。

予想: この需要の供給は無限には維持できない。正確には、use clock列 `m₁ < m₂ < …` について
需要値 `c + mᵢ`（すべて相異なる）の初出時刻 `jᵢ ≤ mᵢ + 1` への割り当ては単射であり
（1時刻1初出）、供給源は (i) 有限pre-corridor履歴、(ii) 他のuse clockのburst出力
`c + 2m′ + 2, c + 3m′ + 4, c + 4m′ + 7`（それぞれ `m = 2m′+2, 3m′+4, 4m′+7` の格子上のみ）、
(iii) use間の一般corridor着地（値 > clock + target）に限られる。導出すべき矛盾は、
(iii) の一般着地が需要値 `c + mᵢ` をちょうど無限回踏み続けること自体が新たな再訪構造
（`c` とは別の再訪candidate列）を要求し、well-founded な再帰に落ちるか、あるいは
供給時計の密度が需要時計の密度を賄えない、のいずれかである。

## Why it would matter

- Frontier obligation discharged: A枝のrecurrence枝の排除。A枝残余は「欠損値非有界」のみになる。
- Stronger than an existing identity because: ledger恒等式は望遠和で個別need/supplyを結べない。
  需要値の相異性と1時刻1初出の単射性は既存のreuse-balance（停止済み）と異なり多重度問題がない。
- Smallest useful consequence: 需要供給が有限horizon内で枯渇する定量下界が一つでも出れば、
  seeded no-goと違いcanonical軌道固有の入力になる。

## Provenance and dependencies

- Definitions used: `SharpCorridor`, `EventualHighCandidateTail`, `nextSubtractionCandidate`
- Lean theorems used: `missingUnbounded_or_burstStream`, `corridor_recurringCandidate_event`,
  `recurringCandidate_addition_burst`, `corridor_forcedAddition_birth_classified`
- Unverified mathematical assumptions: なし（分岐仮定のみ）
- Literature source or analogy: `docs/CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md` §1.2

## Falsification plan

- Small and boundary cases: 実測（`candidate_reuse_probe.cpp`, 1e8）では後続需要の充足率は
  decade 7で0.036%・m^(−1/2)減衰であり、burst streamの要求（100%）と3000倍乖離。
  ただしこれは反証ではなく分岐の非現実性の示唆にとどまる。
- Adversarial or weakened-history model: seeded有限corridorは需要を有限個までpreloadで
  満たせる（SeededHighCorridorNoGo）。無限版の自己供給スケジュール（(ii)格子＋(iii)一般着地の
  無限整合）を抽象モデルで構成できれば本予想の現行形は死ぬ——最初にこれを試すこと。
- Discovery range: 1e8 reuse probe済み。holdout: 1e9以降の同型測定。
- Maximum one permitted repair: 供給クラス(iii)の細分（着地のfresh性・cone分類による絞り）1回。
- Stop condition: 抽象自己供給スケジュールが構成でき、かつcanonical固有の障害が
  一つも特定できないとき。または供給/需要が同オーダーで無strict driftのとき（reset repaymentと同型）。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-01 | `OBSERVED` | candidate_reuse_probe 1e8 | 需要充足率0.036%@d7、m^(−1/2)減衰、格子比率10-14%のみ |
| 2026-09-01 | `PROVED-LEAN` | RecurringCandidateBurst | burst 3連・需要は`c+m`1個/use |

## Semantic audit

- Informal statement implies formal statement: burst streamの需要はLean化済みの正確な形。
- Counterfactual examples: 抽象自己供給スケジュール（構成できれば反証）。
- Could it be proved from weaker assumptions?: 「いずれw超え」型の結論を含まないこと（自由事実の罠）。
- Omitted provenance risk: (iii)の一般着地は`d`-walkが`c+m`を踏むことと同値であり、
  「別の値の再訪」への再帰として定式化しないと循環する。

## Decision

- Continue / formalize / refute / stop: `CONTINUE`（次エポックの最優先紙上課題）
- Reason: A枝の残余2点のうち唯一、構造が完全にLean化済みで攻撃面が確定している。
- Reopen only if: —
