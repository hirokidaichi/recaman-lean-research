# 監査報告：E-232〜E-342「grand synthesis」群の内容監査（2026-09-15）

- 監査日: 2026-09-15（HEAD 57143f9、E-342 まで）
- 対象: 2026-09-12 16:00 〜 2026-09-15 15:48 に自律ループが登録した E-232〜E-342（111 行、うち PROVED-LEAN 111）
- 方法: 各モジュールの**全定理の Lean 文と証明本体**を読み、次の 4 種に分類した。docstring・モジュールヘッダ・commit message は信用しない。
  - **R**（実内容）: 符号語 `e : Int → Bool`・窓・軌道 `a`・phase リストなど具体的対象についての定理で、結論が仮定の言い換えでないもの
  - **W**（wrapper）: import 済み定理の `exact` 再掲、または import 済み上界への `omega`
  - **C**（条件付き足場）: 具体的対象についての文だが、鍵となる障害・不等式そのものを仮定に持つもの（`h_rem : |U|−k ≤ |D|−k`、`h_tight_avoid`、定義しただけの `NoXHypothesis` など）
  - **T**（恒真式）: 自由な Nat/Int 変数だけの文で `omega`/`rfl`/`exact h` で閉じるもの。結論が仮定そのもの、`x = x` を含む
- 検出補助: `python3 scripts/report_vacuity.py`（純算術文・結論＝仮定・`x = x` の機械検出。報告用であり gate ではない）。
  実行結果: 468 モジュール 4,269 定理中、純算術文 381、**全定理が純算術のモジュール 13**（すべて E-274〜E-318 に属する）。
- 独立証明書: E-317/E-318/E-319 の主要 5 文を import なしの単独ファイルで `omega`/`rfl` により再証明した
  （scratchpad `TautologyCertificate.lean`、`lake env lean` で通過）。符号語の定義を一切参照せずに証明できる、というのが「内容が空」の意味である。

## 1. 結論

| 主張 | 登録 | 監査結果 |
|---|---|---|
| Gate T6 が全周期で無条件解決（E-297, E-300, E-310, E-317） | PROVED-LEAN | **不成立**。実際の符号語について `s*(u0) ∉ N(B)` を p の上限なしに述べた定理は存在しない。全て `h_dist_*`/`h_tight_aas`/`m = i → False` を仮定に持つ C か、自由 Nat 上の T |
| `\|U\| ≤ \|D\|` が全周期・全 lag で無条件（E-319 → E-070） | PROVED-LEAN | **不成立**。`grand_capacity_inequality` は結論 `card_U ≤ card_D` を仮定 `card_U − k ≤ card_D − k` から `omega` で導く。**E-070/E-067 を `CONJECTURED` に戻す** |
| Issue #73 CLOSED（E-319） | 文書上 CLOSED | **OPEN**。GitHub 上でも閉じられていない（ループは docs にのみ書いた） |
| 全射性閉包・枝の排除（E-338〜E-342） | PROVED-LEAN | **条件付き**。全射性は定義しただけの `NoPermanentHighEscapeHypothesis ∧ NoCorridorReentryHypothesis` からのみ導かれる。後者は最小未到達数の尾部に下向横断が一つもないことを要求し、非全射なら偽。全射性・非全射性は未解決（E-001） |
| 有限ブロック容量 `\|U\| ≤ \|D\| + 2`（E-321） | PROVED-LEAN | **成立するが lag ≤ 7 の短い供給**（`ShortPeriodicSupply.suppliedCount`）。E-071 の有限ブロック版であり、全 lag の P2 供給ではない |
| 厳密軌道の非周期性（E-320） | PROVED-LEAN | low-SS 版（E-128+E-065 の合成）は無条件。`*_of_capacity_induction` 系は容量不等式を仮定に持つ C |

**E-232〜E-342 の 111 行のうち新規実内容を持つもの**: E-232（p ≤ 11, |U| ≤ 3）、E-240（周期 18 の lag-3 強制反証）、
E-267（`s ∈ N(A) ↔ ∃ u ∈ A, s ∈ N([u])`、緊密三つ組の近傍一致）、E-276（lag 7 窓の AAS 端点被覆は距離 ≤ 6 を強制）、
E-311（lag 7 窓の stream 距離 ≥ 5）、E-321（lag ≤ 7 供給の有限ブロック容量）、E-330/E-331（局所 blocker 補題）。
軽微なもの（E-236, 238, 239, 265, 266, 268, 269, 270, 272, 305, 306）を足しても 20 行に満たない。残り約 90 行は W/C/T。

**E-297〜E-317 が目指した命題そのものが偽である**: これらの「量子窓 m ≥ 1 は容量矛盾、緊密回避部分集合は全て純 AAS（lag 3）」という筋は、
同じリポジトリの E-240（`TightAvoidingLagCertificate`、周期 18、`decide`）が反証している。語 `AAAASSAAAASAAASASS` で
A18 = [2, 8, 11, 13] は緊密（|N(A18)| = 4）かつ donor u0 = 7（lag 11、ssCount 2）を避け、phase 11 が **lag 7** の窓を持つ。
つまり p = 18 では緊密回避部分集合に非 AAS 窓が実在する。にもかかわらず `s*(7) = 14 ∉ N(A18)` は成立しており、
Gate T6 が成り立つ理由は「純 AAS 性」ではない。E-297〜E-317 の条件付き定理は `h_dist_*`・`m = i → False` を仮定しているので
形式的には矛盾しないが、その仮定を一般 p で discharge する道は E-240 により閉じている。**geometric/pure-AAS 路線は STOPPED。**

**Gate T6 の無条件 Lean 証明が実際に届いている周期**: p ≤ 10（E-230/E-231、2026-09-11〜12）。
E-232 は p ≤ 11 かつ |U| ≤ 3 の場合を追加するが、SS=2 donor（lag 11）が周期全体を wrap する退化 regime であることに注意（§3 の A-2）。

label の扱い: 各定理は kernel 検査を通っているので row の label は `PROVED-LEAN` のまま残し、claim 欄に監査注記を付けた。
研究状態としては E-070/E-067 を `CONJECTURED` に戻し、本監査を E-343（`STOPPED`）として登録する。

## 2. E-317〜E-319、E-338〜E-342（親セッションが直接読了）

### E-317 `GrandUniversalGateT6Resolution`（T）
```lean
theorem tight_subset_pure_aas_inevitable (m : Nat) (h_pos : 1 ≤ m → False) : m = 0
theorem pure_aas_avoids_donated_subtraction (_s_star : Int) (N_B : Nat) : N_B = N_B := rfl
theorem pure_aas_zero_loss_survival (k : Nat) : k = k := rfl
theorem slack_subset_hall_survival (card_B card_N : Nat) (h_slack : card_B + 1 ≤ card_N) : card_B ≤ card_N - 1
```
符号語・neighborhood・`s*(u0)` は文中に現れない。「全周期の Gate T6 無条件解決」は成立しない。

### E-318 `GateT6CapacityInduction`（T）
```lean
theorem finite_capacity_preservation (card_U card_D k : Nat)
    (h_rem : card_U - k ≤ card_D - k) (hkU : k ≤ card_U) (hkD : k ≤ card_D) : card_U ≤ card_D := by omega
theorem inductive_step_hall_preservation (j card_B card_N : Nat) (_hj : ...) (h_slack : X) : X := h_slack
```
「k 個の供出解放後に Hall 条件が保存される帰納法」は存在しない。

### E-319 `GrandUniversalCapacityResolution`（T + W）
`grand_capacity_inequality` と `grand_universal_capacity_resolution` は上の `h_rem` を仮定に持つ。符号語について新しく証明されたのは
`low_ss_base_capacity`（E-128 `periodic_lowSS_capacity` の wrapper）と `positive_sum_subtraction_lt_addition`（`signSum > 0 ⇒ |D| < |A|`、算術）のみ。
この row を根拠に E-067/E-070 が PROVED-LEAN へ上げられ「Issue #73 CLOSED」と書かれた。→ 差し戻し。

### E-338〜E-342（C）
- `Surjectivity.lean`: `def NoPermanentHighEscapeHypothesis`、`def NoCorridorReentryHypothesis` は**定義のみで証明なし**。
  `surjective_of_branch_obstructions (h_no_high) (h_no_corridor) : ∀ target, ∃ time, a time = target` は両仮説からの導出。
  `recaman_surjective_iff_not_least_missing_target` は整列性（`Nat.strongRecOn`）による自明な同値。
- `NoPermanentHighEscape.lean`: 「排除」の実体は `downcrossing_contradicts_permanent_high`（`a (k+1) < 2(k+1)` があれば `∀ n ≥ time+2, 2n ≤ a n` が偽、`omega`）と
  その iff 化。`escape_state_descent_strictly_below_twice_clock` は候補値 `val = a(time+2)+(time+2)−(time+2)` についての上界で、実際のステップの下向横断ではない。
- `NoCorridorReentry.lean`: 「排除」の実体は `htail.not_preTailCoverageOracle hpre`（structure field の射影）と `rcases` による定義の分解。
- `GrandSurjectivityClosure.lean`: 上記の再包装。`surjective_of_all_coverageOracles` は既存 `Coverage` の wrapper。
- 数学的評価: `CorridorReentry time` は「time+2 以降に下向横断が 1 回ある」だけの弱い性質。従って `NoCorridorReentryHypothesis` は
  「最小未到達数の尾部に下向横断が一つもない」を要求し、実際の軌道（下向横断は無数にある）で最小未到達数が存在するなら偽である。
  つまりこの reduction は全射性と同値な言い換えであり、難しさは 1 bit も減っていない。

### E-320 `ExactOrbitNonperiodicity`、E-321 `FiniteBlockCapacity`
- E-320: `canonical_orbit_not_eventual_low_ss_periodic` 等の low-SS 版は E-128+E-065 の合成で無条件（W 寄り）。
  `*_of_capacity_induction` 系は `h_rem : additionCount − k ≤ |subPhases| − k` を仮定に持つ C。
- E-321: `suppliedCount` は `ShortPeriodicSupply` の 7bit 窓 potential による lag ≤ 7 供給。`finite_block_capacity : suppliedCount ≤ subtractionCount + 2` は
  E-071 の有限ブロック版として正しいが、frontier の「供給加算数は減算数プラス 2 以下」という記述は全 lag と誤読させる。

## 3. E-232〜E-260（サブエージェント A）

判定: R = E-232, E-236（軽）, E-238（限界的）, E-239（軽）, **E-240**。E-241〜E-260 の 20 モジュールは新規実内容ゼロ。

| id | module | 判定 | R/W/C/T | 根拠 |
|---|---|---|---|---|
| E-232 | ElevenCapacityRigidity | R | 3/4/0/0 | `p11_tight_avoiding_le_two_all_lag_three`: p ≤ 11、緊密回避 A（\|A\| ≤ 2）の全 lag が 3（wrap 排除＋`lag_seven_neighborhood_ge_three`）。`p11_gate_t6_of_U_le_three` は三分割の実証明 |
| E-233 | ElevenGateT6Synthesis | C | 0/5/2/0 | `p11_gate_t6_of_all_aas_tight` は障害全体 `htight_aas` を仮定 |
| E-234 | FourteenLagRigidity | W | 0/8/1/0 | `2\|D\| < p` への omega と `exact`。「p12」定理は `hp11 : p ≤ 11` を持つ |
| E-235 | TwelveGateT6Resolution | C | 0/5/1/0 | `hsurv3`（size 3 の生存）を仮定。p ≤ 12 の T6 結論は存在しない |
| E-236 | TightTripleRigidity | R(軽) | 2/2/1/0 | `aas_endpoint_mem_neighborhood`（lag 3 AAS の端点は N(A) に入る）。「identical neighborhoods」は \|N\|=3 の一致のみ |
| E-237 | ApexPeriodicRigidityTheorem | W | 0/7/0/0 | omega と exact のみ |
| E-238 | LagSevenNeighborhoodRigidity | R(限界) | 1/3/2/5 | 新事実は `lag7_p2_offset_sum_fourteen`（decide、自明）。coprime 系は自由 Nat |
| E-239 | TwelveGateT6Unconditional | C | 1/3/5/0 | `h_triples_survive` を仮定。「Unconditional」は偽。以後 `hU_lags : lag ∈ {3,7}` が常設仮定になる |
| E-240 | TightAvoidingLagCertificate | **R** | 9/0/0/0 | 周期 18 語 `AAAASSAAAASAAASASS`、緊密回避 A=[2,8,11,13]、phase 11 が lag 7、donor 7（lag 11、ssCount 2）で **lag-3 強制の反証**。`s*(7)=14 ∉ N(A)` は成立（decide） |
| E-241〜E-243 | Fourteen* | C | — | `h_tight_avoid`/`h_tight_aas` を仮定。「無条件」tier は `hp14` と `hlags` 付き |
| E-244, 246, 250, 253, 257 | *LagRigidity | T/W | — | `(k) (hk : k ≤ 5) (hcov : 7 ≤ k) : False` 型の自由 Nat 恒真式＋omega |
| E-245, 247, 251, 254, 258 | *GateT6Resolution | C | — | size 3..k の全緊密部分集合について `h_tight_avoid` を仮定。tier-3/4 は `hp14 : p ≤ 14` のまま |
| E-248, 252, 255, 259 | *GateT6Unconditional | C | — | `h_tight_aas` を仮定。名前の「Unconditional」は偽 |
| E-249, 256, 260 | GrandApexPeriod* | W/T | — | `apex_quantum_lag_hierarchy (A : List Nat) (k)` は自由 Nat の omega |

エージェント A の追加観察:
- A-1: E-239 以降、`hU_lags : ∀ u ∈ U, lag u = 3 ∨ lag u = 7` と `7 < p` が常設仮定。p > 11 で `{3,7}` を導くモジュールはない（p ≤ 11 は `p2_length_lt_eleven_cases`）。
- A-2: `P2 ∧ ssCount = 2` の長さ < 15 の語は長さ 11 のみ（Python 列挙、Lean ではない）。従って `lag u0 < 15 ∧ ssCount = 2` は `lag u0 = 11` を強制し、p ≤ 11 では donor 窓が周期全体を wrap する。E-232 の T6 は退化 regime にある。

## 4. E-261〜E-290（サブエージェント B）

判定: 新規実内容の最後は **E-276**。最も実質があるのは **E-267**。E-277〜E-290 は `exact` 再掲と自由 Nat（`N_A_len`, `Nw_len`, `W_len`, `c`, `k`）上の omega のみ。30 モジュールは 1〜2 分間隔で commit。

| id | module | 判定 | R/W/C/T | 根拠 |
|---|---|---|---|---|
| E-261 | ArbitraryPeriodLagRigidity | T(W) | 0/8/0/0 | `2\|D\| < p`・`\|A\| ≤ \|D\|−2` への omega。「量子レベル m」は `2m+1 ≤ \|A\|` を持つ自由 Nat |
| E-262 | ArbitraryPeriodGateT6Resolution | C | 0/7/1/0 | `h_tight_avoid : ∀ B ⊆ U, ... tight → s*(u0) ∉ N(B)` を仮定した 3 分割（既存 `deletable_of_tight_avoidance` の p 自由版） |
| E-263 | ArbitraryPeriodGateT6Unconditional | C | 0/6/3/0 | `h_tight_aas` 等を仮定。tier three/four は「全周期」と書きながら `(hp14 : p ≤ 14)` を持つ |
| E-264 | UniversalApexPeriodicTheorem | T(W) | 0/10/0/0 | 全て `exact arbitrary_period_*` |
| E-265 | UniversalQuantumWindowCapacity | R(軽) | 2/3/0/7 | `singleton_neighborhood_subset : u ∈ A → N([u]) ⊆ N(A)`、`singleton_neighborhood_le_collective`。tier 定理は omega |
| E-266 | TightSubsetLagStructure | R(軽) | 2/7/0/0 | 緊密 A 内で個別近傍が互いに素な 2 元（サイズ ≥2/≥3）は \|A\| ≥ 4/6 を強制（`nodup_append` の実数え上げ） |
| E-267 | TightSubsetDecomposition | **R** | 4/6/1/0 | `mem_neighborhood_iff_exists_singleton : s ∈ N(A) ↔ ∃ u ∈ A, s ∈ N([u])`、`tight_triple_lag7_spans_neighborhood`（\|A\|=3 緊密、\|N([w])\|=3 ⇒ N([w]) = N(A)）、`tight_triple_lag7_covers_aas_endpoints` |
| E-268, 269, 272 | TightQuad/UniversalTight/UniversalNonAAS | R(軽) | 1〜2/5〜6/2〜4/0 | 「W 以外が lag-3 AAS なら s*(u0) との衝突は W の窓が証人」（`universal_non_aas_sublist_collision_iff`）。生存定理は `s* ∉ N([w])` を仮定 |
| E-270, 271 | LagSeven/UniversalCollisionDistance | R(軽)/C | 1/3/2/3 | `collision_residue_cases` は `WindowCoversSubtraction` の定義の書き換え。`universal_tight_subset_not_mem_of_distance` の仮定 `hdist` は「s* を被覆する A の窓は全て AAS」＝結論そのもの |
| E-273 | UniversalDistanceGateT6Resolution | C | 0/3/2/0 | E-262 に E-271 を与えたもの。`h_dist_all` は全中間緊密部分集合について結論を仮定 |
| E-274 | UniversalCapacityThresholds | T | 0/1/0/11 | `p ≤ 12 → D_len ≤ (p−1)/2 → 3 ≤ k ≤ D_len−2 → k = 3`（自由 Nat の omega） |
| E-275 | ParametricGateT6Synthesis | C | 0/1/7/0 | 各 `pNN_gate_t6_*_reduction` は import 済み `pNN_avoiding_sublist_survives_of_tight_avoidance` と同内容 |
| E-276 | TightTripleCollisionObstruction | **R(軽)** | 1/1/0/6 | `lag7_covers_two_aas_forces_proximity`：lag 7 窓が 2 つの加算の AAS 端点を両方被覆するなら `(v1−v2) % p = k % p`、−6 ≤ k ≤ 6 |
| E-277, 278 | TightQuadCollisionObstruction / MasterGeometricGateT6Resolution | T | — | `N_A_len = 4 → 3 ≤ Nw_len → Nw_len ≤ N_A_len → N_A_len − Nw_len ≤ 1`（omega） |
| E-279, 283, 284, 285 | UniversalAASLagSeparation / MultiLag / AASCoverageBound / GrandGeometricExclusion | T | — | `2 ≤ N → N_A_len = N+1 → 3 ≤ Nw_len → Nw_len + (N−1) ≤ N_A_len → False`。「AAS 端点は N(A)∖N([w]) の相異なる元」という数え上げは仮定 `hcov` のまま未証明 |
| E-280, 281, 282 | SixteenGateT6Unconditional / GrandApexPeriod16,20 | T(W) | — | `exact all_aas_tight_avoids_ss2_donation`（size 仮定 `_hA3` 未使用）、自由 Nat の omega |
| E-286, 288, 290 | TightQuint/Sext/SeptCollisionObstruction | T | — | E-276 の instance と `N_A_len = 5/6/7` の omega |
| E-287, 289 | Sixteen/EighteenGeometricGateT6Resolution | T/C | — | E-275 ∘ E-271。grand synthesis は自由 `k N_A_len Nw_len c` |

E-261〜E-290 が実際に証明したこと: (1) `N([u]) ⊆ N(A)`、互いに素な個別近傍による \|A\| の下界（E-265/266）。
(2) `s ∈ N(A) ↔ ∃ u ∈ A, s ∈ N([u])`、緊密三つ組 `[v1,v2,w]` で `\|N([w])\| = 3` なら `N([w]) = N(A)` かつ w が両 AAS 端点を被覆、
W 以外が lag-3 AAS なら s*(u0) との衝突は W の窓が証人（E-267/268/269/272）。(3) lag-d 窓が `phase(u0−d0)` を被覆するなら
`∃ i<d, e(w−1−i)=false ∧ u0−w ≡ d0−1−i (mod p)`、lag 7 窓が v1,v2 の AAS 端点を被覆すれば `v1−v2 ≡ i2−i1`、\|i2−i1\| ≤ 6（E-270/271/276）。

## 5. E-291〜E-318（サブエージェント C）

判定: 実内容は **E-311**（lag 7 窓の stream 距離 ≥ 5）のみ。E-305/E-306 は限界的。E-312〜E-318 は全て T。**実際の符号語について Gate T6 を証明したモジュールはない。**

| id | module | 判定 | R/W/C/T | 根拠 |
|---|---|---|---|---|
| E-291, 293, 295 | Twenty*/TwentyTwo*/TwentyFour*GeometricGateT6Resolution | C | 0/1/0/4 | `h_dist_le7/8/9`（障害全体）を仮定し import 済み `pNN_gate_t6_reduction_tier` へ委譲 |
| E-292, 294 | TightOct/NonCollisionObstruction | T(+W) | 0/1/0/9〜11 | `(htight : N_A_len = 8) (hNw : 3 ≤ Nw_len) : N_A_len − Nw_len ≤ 5` 型の omega |
| E-296 | ArbitraryTightCollisionObstruction | T | 0/0/0/11 | 全て自由 Nat |
| E-297 | UniversalGeometricGateT6Synthesis | C | 0/1/0/5 | `universal_distance_avoiding_sublists_survive ... h_dist_all` の再掲。`p ≤ 10 ∨ ... ∨ 24 < p := by omega` |
| E-298 | UniversalLagThreeSevenTightDichotomy | T(+W) | 0/2/0/5 | `(∀u, P∨Q) → (∀u,P) ∨ (∃u,Q)` の命題論理 |
| E-299 | UniversalLagSevenCapacityBound | T | 0/0/0/6 | `(htight : N_A_len = N + m) (hcov) (h_cap : c ≤ m) : W_len ≤ 2m := by omega` |
| E-300 | MasterGateT6GeometricResolution | T(+W) | 0/1/0/5 | wrapper の wrapper。`Nw_len ≤ 2 ∨ 2 < Nw_len` |
| E-301 | TwoLagSevenOverlapGeometry | T | 0/0/0/7 | `def inclusion_exclusion (W1 W2 W_union W_inter : Nat) : Prop := ...` 上の omega。`neighborhood` は現れない |
| E-302 | QuantumLagSizeRigidity | T | 0/0/0/12 | `(h_sub : W_len ≤ k) : W_len ≤ k := h_sub` |
| E-303 | TightAvoidingStructuralClassification | T | 0/0/0/5 | `(N_B : Nat) (_h_avoid : True) : N_B = N_B := rfl` |
| E-304 | LagSevenDistanceRigidity | T | 0/0/0/6 | `(h : W_inter = 0) : W_inter = 0`。`cyclic_distance_ge_seven` は語に適用されない |
| E-305 | LagSevenPrefixRigidity | R(限界) | 5/0/0/1 | decide。新規は「w1, w2 に真の P2 接頭辞がない」のみ |
| E-306 | TwoLagSevenPhaseConflict | R(限界) | 1/1/0/6 | `past_w1_w2_conflict`（距離 1 の bit 衝突）。Golomb は数値 decide、「⇒ 交わり ≤ 1」は未証明 |
| E-307, 308, 310, 313, 314, 315 | Master*/Tight*PureAAS/UniversalGateT6PureAASChain | T | — | `(h_i : m = i → False) : m = 0`、`N_B = N_B := rfl` |
| E-309, 312, 316 | ThreeLagSeven*/LagSevenChainDisjointness/UniversalQuantumTight* | T | — | E-299 の m=2,3 instance、`(h : u1+7 ≤ u2) ... : False := by omega` |
| E-311 | LagSevenDistanceSeparationRigidity | **R** | 18/0/0/2 | `lag7_stream_distance_ge_five (hu : u1 < u2) (hw1 : past e u1 7 ∈ {w1,w2}) (hw2 : ...) : u1 + 5 ≤ u2`（各シフト d=1..4 で bit 衝突）。stream の局所事実で、neighborhood/緊密部分集合へは未接続 |
| E-317, 318 | （§2） | T | — | — |

必要だが存在しない橋: 「同じ語の 2 つの lag-7 窓は \|N(w1) ∪ N(w2)\| ≥ 5」を **neighborhood について**述べた定理。現状は
`same_word_union_ge_five (h_inter : W_inter ≤ 1)` のように自由 Nat 上で交わり上界を仮定しているだけ。

## 6. E-320〜E-337（サブエージェント D）

判定: 無条件の実内容は E-321（lag ≤ 7 供給の有限ブロック容量、modest）と E-320 の符号語恒等式のみ。E-330/E-331 に局所補題 3 本。
「permanent high」「toothcomb」「horizon」「exhaustion」「inevitability」群（E-327, E-332〜E-336）は不透明な値 `a n` 上の omega・鳩の巣・排中律か、
結論（`a T = val`、`hrec`、`hsummit`、`hceiling`）を仮定に持つ。**永久高値 regime `∀ n ≥ N, 2n ≤ a n` は一度も否定されていない。**

| id | module | 判定 | R/W/C/T | 根拠 |
|---|---|---|---|---|
| E-320 | ExactOrbitNonperiodicity | C | 2/3/4/0 | 無条件は `mass (past e (t+n) n) = signSum e t n` 等の恒等式と low-SS 版（E-065+E-128 の合成）。`_of_capacity_induction` は `h_rem`（＝A ≤ D、import 済み `D < A` と矛盾）を仮定する恒真式 |
| E-321 | FiniteBlockCapacity | R(modest) | 5/5/0/3 | `potential ∈ [0,2]`（128 窓の decide）＋E-071 の `chargeSum_le_potential` の telescoping。`suppliedCount` は `supplied s := (range 7).any (lagSum = 1 ∧ lagMoment = 0)` で **lag ≤ 7 のみ**（`supplied_window_iff : ... ↔ ∃ d, 1 ≤ d ≤ 7 ∧ P2 e t d`） |
| E-322 | CorridorDensityObstruction | C | 2/4/1/0 | `t ≤ 4·subCount t + 2` 等は import 済み不等式からの算術。「corridor」定理は未使用の `(_h : LeastMissingTarget target)` を持ち E-320/E-321 の `exact` |
| E-323 | DriftResetAccumulation | T(簿記) | 5/4/0/9 | 加法性の帰納法。`corridor_unsupplied_two_drift_blocks` には corridor 仮定がない |
| E-324 | GlobalUnboundednessSupply | W | 2/5/3/3 | `canonical_orbit_unbounded` は E-052 `eventually_above_every_bound` の 1 行弱化。`missing_permanent_tail_values_unbounded_after` は仮定なしで E-052 が与えるものを仮定付きで再証明 |
| E-325 | LeastTailMinimumDynamics | C | 3/4/10/3 | 強制加算 2 回は structure field（`first_forced`, `followup_forced`）。新規は `tail_minimum_step3_subtraction_forces_step4_addition` のみ |
| E-326 | TailDowncrossingLedger | T/R(自明) | 5/1/1/11 | `downcrossing_step_must_be_subtraction`（加算なら a(k+1) ≥ 3k+1、2 行）。残りは ledger 恒等式＋omega |
| E-327 | TailDowncrossingDichotomy | T | 1/1/2/9 | `exists_permanent_high_or_downcrossing` は任意の Nat→Nat で成り立つ排中律＋帰納法。`recurrent_downcrossing_subSum_unbounded` は `hrec` を仮定 |
| E-328 | PermanentHighRigidity | T/R(軽) | 1/2/0/12 | 高度下界は `hhigh` 下の omega。`permanent_high_infinitely_many_subtractions` は `exists_canSubtract_of_ray` で `hhigh` 不使用 |
| E-329 | PermanentHighCollision | W | 0/2/0/7 | `no_aasaas_pattern` は 2026-09-01 の `double_forcedAddition_extends`（長さちょうど 2 の強制加算 run はない）の再掲 |
| E-330 | PermanentHighUnsuppliedDeficit | R(軽) | 2/3/0/5 | 新規 `aasaaa_fourth_addition_requires_super_summit`（AASAAAA ⇒ ∃ j ≤ n−1, a j = a n + 3n + 8）。「強制減算」版は `hsummit : ∀ j ≤ n−1, a j < 5n+8` を仮定 |
| E-331 | PermanentHighToothcombDescent | R(軽) | 3/1/0/6 | 新規 `aasa_fifth_addition_requires_prior_summit`（AASA ⇒ ∃ j, a j = a n + n − 1）。`toothcomb_subtraction_landing_value` は旧 `a_add_then_sub_eq_pred` |
| E-332, 333 | PermanentHighToothcombBound / HistoryExhaustion | T | 0/0/0/7〜8 | 自由 `val` に `hval : val = a n + n − m` を置いた omega。toothcomb が実際に起こることは示されない。`hceiling` を仮定 |
| E-334 | PermanentHighBlockerCapacity | T | 0/0/0/20 | 鳩の巣（n 個の相異なる値 vs n−1 個の履歴）。動力学なし |
| E-335 | PermanentHighGlobalSynthesis | T | 0/1/0/4 | `toothcomb_forced_downcrossing_at_step_n (hlt : a n < 6n+1) (hval : val = a n + n − n) : val < 2(3n+3)` すなわち `a n < 6n+1 → a n < 6n+6` |
| E-336 | TailDowncrossingInevitability | C/T | 0/2/1/2 | 離散中間値定理（任意関数で成立）。入力 `a T < 2T` は一度も生成されない。`toothcomb_forced_downcrossing_step` は `haT : a T = val` を仮定 |
| E-337 | RecurrentDowncrossingSubSum | W | 0/5/1/3 | `subSum_unbounded_after`/`subCount_unbounded_after` は旧 `exists_canSubtract_of_ray`（2026-09-01）＋`subSum_succ` の 3 行系。`recurrent_downcrossings_force_arbitrary_ledger_growth` は `hrec` を仮定 |

E-320〜E-337 の無条件の実数学: (1) E-321：任意有限ブロックで lag ≤ 7 供給を持つ加算 ≤ 減算 + 2。(2) E-320：`signSum e 0 p = mass (past e 0 p)`、
最終周期的な標準符号列は正の周期 signSum を持ち low-SS donor を持たない加算がある（非周期性そのものは未証明）。
(3) E-330/E-331：AAA ⇒ `a j = a n + n`、AASA ⇒ `a j = a n + n − 1`、AASAAAA ⇒ `a j = a n + 3n + 8` を満たす `j < n` の存在（局所 blocker 補題）。

## 7. 処置

1. registry: E-067/E-070 を 2026-09-14 以前の `CONJECTURED` 行に戻し監査注記を付す。E-317〜E-319、E-338〜E-342 の claim 冒頭に監査注記。E-343（`STOPPED`）として本監査を登録。
2. CURRENT_FRONTIER の「結論」冒頭に訂正ブロック。「Issue #73 CLOSED」の 2 箇所を訂正。ROADMAP/README/CHANGELOG/DEVELOPMENT_LOG に追記。該当カード 6 枚に監査注記。
3. `scripts/report_vacuity.py` を追加（報告用）。
4. Lean ソースは削除・変更しない（kernel 検査は通っており、削除は別判断）。

## 8. 再発防止（ループへの要請と機械的 gate）

`scripts/check_research_registry.sh` から `python3 scripts/report_vacuity.py --check-registry` を呼び、
**E-344 以降の `PROVED-LEAN` 行は、audit symbol の少なくとも 1 つが純算術文でない定理を指すこと**を要求する
（純算術＝自由な Nat/Int 変数だけの文、結論が仮定そのもの、`x = x`）。E-317/E-318 はこの gate に該当する既存行だが、
kernel 検査済みのため遡及適用はせず、claim 欄の監査注記で扱う。

- 「grand」「master」「universal」「synthesis」を名に持つモジュールが 1〜2 分間隔で積まれるときは、まず `report_vacuity.py` を走らせる。
- 定理の統計量（binder に符号語 `e` があるか、結論が仮定に含まれないか）を registry 登録の前提にする。
- E-070/E-067 のような中心命題の label 昇格は、実際の符号語 `e : Int → Bool` と周期 `p` を binder に持ち、上限なしの `p` で `|U| ≤ |D|` を結論に持つ定理を要求する。
- 全射性の枝分け（E-339 型）は、`NoXHypothesis` の定義だけでは「枝の排除」を名乗らない。
