# Hypothesis card: `burst-stream supply injectivity`

- ID: `H-20260901-01`
- Owner: sharp-kernel sprint
- Created: 2026-09-01
- Status: `STOPPED`（命題自体は`CONJECTURED`）
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
| 2026-09-01 | `OBSERVED` | `periodic_nogo_check.py`の記録のみ | eventually-periodic no-goはexact statementと検査scriptがrepositoryになく再現不能。Lean-ready / `PROVED-PAPER`の判定を取り下げ |
| 2026-09-01 | `REFUTED` | `SeededUseGapCounterexample`, `USE_GAP_AUDIT_2026-09-01.md` | **local use-gap読みは偽**: exact `Basic.step` seedで`m=120`, `n=141`, 中間candidateは全てclockより上、両useは3-addition burstを持つが`21² < 6·120` |
| 2026-09-01 | `PROVED-PAPER` | `USE_GAP_AUDIT_2026-09-01.md` | 反例族`m=q²+2q`, word `A^(q+1)S^q`, gap `2q+1`は`gap²/m → 4`。`sqrt(6m)`に必要だったのは未仮定の「addition run長≤3」 |
| 2026-09-01 | `COMPUTED` | `use_gap_counterexample 3 100`; `101 10000` | discovery 98例・holdout 9,900例がexact greedy continuationを通過。最終比`gap²/m=3.999600090` |
| 2026-09-01 | `OBSERVED` | 未収録の`burst_schedule_sim.py`等5scriptによる旧記録 | 稠密seed・mod-3 ladder・混合格子の構成失敗は再現artifactがないため観測扱いに限定 |
| 2026-09-01 | `PROVED-LEAN` | `RecurringCandidateDemandBirth` | rigid需要`c+m`の初出をlegal subtraction birth／addition birthへ分類。late addition枝は`target+2(t+1)<c+m`のstrict contractionを持つ |
| 2026-09-01 | `PROVED-LEAN` | `PeriodicCandidateNoGo` | balanced周期の全cyclic phase drift総和は`-p²`、従って負drift phaseが存在 |
| 2026-09-01 | `PROVED-PAPER` | `PERIODIC_CANDIDATE_NOGO_2026-09-01.md` | lower floorを保つeventually-periodic候補walkは正sign-sumとなり全phaseで発散。非周期scheduleは未排除 |
| 2026-09-01 | `PROVED-LEAN` | `SupplyAncestryCounterexample` | subtraction-born forced use `42`はbirthでlegalへ反転し、相異なる子`151,135`は同じparent `261`へmergeする |
| 2026-09-01 | `REFUTED` | `SUPPLY_ANCESTRY_AUDIT_2026-09-01.md` | forced supplier ancestryはbranch polarityで非閉包。generic parent ancestryも非単射で、interval支払は既存ledgerへ退化 |
| 2026-09-01 | `COMPUTED` | `fixed_seed_supply_falsifier 2000000 4096` | 同一seed fingerprint `14161494152507716643`が内部供給されたcandidate 20のcounted useを`94,286,862`の3回まで実現。4回目なし |

## Closed refinement round

1. **単一有限seedの大域自己供給deficit**は`H-20260901-02`としてexact化したが、許可した一回の
   subtraction-source分解は非閉包・非単射・no-strict-driftで停止条件に到達した。
2. **periodic no-go**は再現script・紙上証明・Lean有限核を収録した。これは非周期的な
   drift-and-reset scheduleを排除しない。
3. local `sqrt(6m)` use-gapもfixed-seed ancestry/driftも`STOPPED`。同じpayloadの再包装は行わない。

## Semantic audit

- Informal statement implies formal statement: burst streamの需要はLean化済みの正確な形。
- Counterfactual examples: 抽象自己供給スケジュール（構成できれば反証）。
- Could it be proved from weaker assumptions?: 「いずれw超え」型の結論を含まないこと（自由事実の罠）。
- Omitted provenance risk: (iii)の一般着地は`d`-walkが`c+m`を踏むことと同値であり、
  「別の値の再訪」への再帰として定式化しないと循環する。
- Failed semantic implication: `recurringCandidate_addition_burst`は「少なくとも3連」であり
  「ちょうど3連」ではない。`sqrt(6m)`の導出はこの逆を暗黙に使っていた。

## Decision

- Continue / formalize / refute / stop: この研究カードは`STOPPED`。main supply命題そのものは
  反証されず`CONJECTURED`のまま。
- Reason: 許可した唯一の修理であるsource splitはaddition枝にstrict contractionを与えたが、
  subtraction枝はforced supplier classを保存せず、generic ancestryはmergeし、use streamには
  密度下界がない。従って需要・供給は同じ線形orderのままである。
- Reopen only if: target occurrence、future return、canonical reachabilityを仮定せず、
  external blocker debt `E` と必要fresh subtraction `S`の間にcutoff-independentなstrict deficit、
  またはreuse intervalの非merge質量を与える独立不変量が得られたとき。
