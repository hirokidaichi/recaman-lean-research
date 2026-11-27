# 2026-11-27 daily research handoff (`R-20261127-01`)

## 1. 結論（Conclusion First）

2026-11-27 の親サイクル **`R-20261127-01`** において、任意深さ（arbitrary-depth）優先プロトコル（§1.8）に基づき4本の深さ一般トラックを遂行し、**3件の新規 Lean 4 モジュール（`E-781`, `E-783`, `E-785`、`PROVED-LEAN`、全15監査定理 vacuity 0 flagged / 0 unknown、標準公理 `[propext, Classical.choice, Quot.sound]` のみ）** と **3件の完全 PAPER 結果（`E-782 PROVED-PAPER`, `E-784 REFUTED`, `E-786 PROVED-PAPER`）** を確定した。

1. **実 `EndN` 任意高さの下降 excursion 3間隔予算と二進重み容量（`E-785 PROVED-LEAN`）**: 任意の `BlockWord ++ A^a` 前史・任意区間長・任意高さ `r : Int` に対し、`3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * A_{r-1}` を無条件証明し、`E-674` を全高さで約3倍厳密強化した。結果として床+4供給を `6 * free` から `3 * E_{m+4} ≤ 8 * free` へ改善し、さらに任意高さ上限 `H` で **`q = 1/2` の一様二進重み容量 `dyadicAdditions ≤ 3 * dyadicFree` と `A_{m+h} ≤ 3 * 2^h * free`** を Lean 4 で証明し、実 `EndN` を `E-775` の緩和 height-kernel cone 障壁（`q < 0.4534, ρ ≈ 2.2056`）から厳密に分離した（新 cone `ρ ≈ 1.8067 < 2`）。
2. **実 `EndN` 固定高さ帯での指数成長下界 `Ω((5/3)^H)`（`E-786 PROVED-PAPER`）**: 全高さ `H ≥ 2`・全 `ε > 0`・任意旧前史 `U` に対し、相対高さ帯 `[0, H + 1]` 内の再帰ゼロ shift 平衡語 `B_H = V_0^{(H)} ++ V_H^R`（`ΔΦ_{H-1}(V_H) = 0` より `D_{H+1}(V_H) = |V_H| = 2 A(V_H)` が恒等成立）が実 `EndN` 上で `A(B_H)/(F + O_c) ≥ (12/25 - ε) · (5/3)^H` を達成することを PAPER 証明した。これにより実 `EndN` 上での固定高さ多項式上界と `q > 3/5` の幾何重み容量が反証され、`E-785` と併せて実 `EndN` の指数成長基数が **`[5/3, 1.8067]`**（幾何重み閾値 `κ ∈ [0.5535, 0.6000]`）へ狭められた。
3. **多 block source bank 再利用による線形容量の無条件反証（`E-783 PROVED-LEAN`, `E-784 REFUTED`）**: `H-20261126-01`（`2A ≤ 3(F+O_c) - 3`）および任意の線形容量 `A ≤ C(F+O_c) + K` を、任意の旧前史 `U`（原点 `0`・共 supplier 保持）を持つ多 block stage 語で反証した（`E-783` で raw sign 全 `(C, K)` を Lean 4 証明、`E-784` で `E-759 (I)/(II) = 0`・8条件実 greedy 実行可能な単位 shift 族 `A/(F+O_c) = 2k - O(1) → ∞` を PAPER 証明）。さらに `E-783` の各高さ `H = 3k` での `3 * E_H = (H-1)^2 - 1` は `E-785` の上界 `(H-1)^2 + 2` と定数差 `3` で漸近一致する。定数勾配の線形多 block `A/(F+O_c)` 課金路線は **`STOPPED`**。
4. **標準軌道の空間 gap 容量と8条件語選別 no-go（`E-781 PROVED-LEAN`, `E-782 PROVED-PAPER`）**: 標準 Recamán 軌道 `a` / `valuesThrough b` の任意時刻 `b` に対する空帯 prefix trapping・空帯上相異訪問数上界 `≤ b + 1 - g`・降順 gap-rank 上界 `≤ b - θ` を Lean 4 で無条件証明した（`E-781`）。これにより `H-20261126-02` の literal 歩幅 `b` 格子は失格する一方、剰余回避橋格子 `d = b - 200 N` が `E-778` の4 scalar 条件 + `E-781` の4空間条件（計8条件）を厳密な distinct seen 集合 `V` で全 coherent 有限語に対し充足することを PAPER 証明した（`E-782`）。静的空間 gap 選別路線は **`STOPPED`**。

**非主張の明記**: 一般 `C1`・`Q`・`H`・`SL`・全射性および固定保護命題（`E-001`, `E-067`, `E-070`, `E-179`）はいずれも**未証明**である。

---

## 2. 仮説カード一覧（Hypothesis-Card Status）

| Card ID | 対応行 | 状態 | 要約・判定 |
|---|---|---|---|
| [`H-20261127-02`](HYPOTHESIS_CARD_2026-11-27_SPATIAL_GAP_INVENTORY.md) | `E-781`, `E-782` | `PROVED-LEAN` (`E-781`) / `PROVED-PAPER` (`E-782`) / 選別法 **`STOPPED`** | `H-20261126-02` の空間必要性を厳密強化して Lean 化。literal 歩幅 `b` 格子を反証しつつ、修正橋格子 `d = b - 200 N` で8条件 language no-go を確定。 |
| [`H-20261127-01`](HYPOTHESIS_CARD_2026-11-27_CROSS_BLOCK_REUSE.md) | `E-783`, `E-784` | `PROVED-LEAN` (`E-783`) / **`REFUTED`** (`E-784`) / 線形課金法 **`STOPPED`** | `H-20261126-01` と全線形多 block `A/(F+O_c)` 容量を raw sign（Lean）と coherent 8条件 greedy（PAPER）の双方で反証。 |
| [`H-20261127-03`](HYPOTHESIS_CARD_2026-11-27_EXCURSION_SPACING.md) | `E-785` | **`PROVED-LEAN`** | 下降 excursion 3間隔による任意高さ予算 `3*E_{r+1} ≤ W_r + 2*A_{r-1}` と `q = 1/2` 二進重み容量を Lean 4 証明し、`E-775` の `q < 0.4534` 障壁を実 `EndN` で突破。 |
| [`H-20261127-04`](HYPOTHESIS_CARD_2026-11-27_EXPONENTIAL_CASCADE.md) | `E-786` | **`PROVED-PAPER`** | 再帰ゼロ shift 平衡語 `B_H`（`D_{H+1}(V_H) = |V_H| = 2A(V_H)`）により実 `EndN` 上で `A/(F+O_c) ≥ (12/25 - ε)(5/3)^H` を証明し、固定高さ多項式上界を反証して成長基数を `[5/3, 1.8067]` へ狭窄。 |
| [`H-20261128-01`](HYPOTHESIS_CARD_2026-11-28_CROSS_HEIGHT_CAPACITY.md) | （次回） | **`CONJECTURED`**（未実行） | 狭窄された窓 `[5/3, 1.8067]` の精密決定、`E-786` の Lean 化、および `E-759 = (0,0)` coherent greedy 実行可能性下での指数成長の可否判定。カード作成は進展に含めない。 |

---

## 3. 確定した証拠（Strongest Evidence）

| ID | Evidence Label | Artifact | 主要結果と境界 |
|---|---|---|---|
| `E-781` | **`PROVED-LEAN`** | `Recaman/CanonicalGapCapacity.lean` ([G5 audit](statement_audits/E-781.md)) | 任意時刻 `b` の標準軌道 `a`・`valuesThrough b` で `walk_peak_le_upperTri`, `empty_gap_prefix_trapped`, `no_empty_gap_gt_clock`, `empty_gap_tail_peak_le`, `empty_gap_distinct_tail_count_le`, `multi_gap_rank_bound` を無条件証明（9/10 substantive, vacuity 0/0）。 |
| `E-782` | **`PROVED-PAPER`** | [Spatial note](RESEARCH_NOTE_2026-11-27_SPATIAL_GAP_INVENTORY.md) | 厳密 distinct seen `V` での scalar 4条件 + 空間 gap 4条件（計8条件）を通過する橋格子 `G_d`（`d = b - 200N`）を全 `E-759` 許容語に構成。併せて `H ≤ 1` の任意 `S^L ++ w` 許容性を証明。未Lean・人間レビュー未。 |
| `E-783` | **`PROVED-LEAN`** | `Recaman/CrossBlockReuseUnbounded.lean` ([G5 audit](statement_audits/E-783.md)) | 任意旧前史 `U` で `additions_partition_after_cut`, 最小2-block反例 `h20261126_two_block_counter`, 全 `(C, K)` 無界比 `no_linear_cross_block_capacity` を無条件証明（26/28 substantive, vacuity 0/0）。`D_depth = 0`, `F >> m` であり `C1` 反例ではない。 |
| `E-784` | **`REFUTED`** | [Cross-block note](RESEARCH_NOTE_2026-11-27_CROSS_BLOCK_REUSE.md) | `E-759 (I)/(II) = 0`（8条件実 greedy 実行可能）下でも 2-block 反例 `[(2,1,1),(1,1,1,2)]` と全 `k ≥ 3` 単位 shift 族（6高度帯多項式分離, `A/(F+O_c) = 2k - O(1) → ∞`）が線形多 block 容量を反証。時刻0 canonical 前史や `C1` 反例ではない。未Lean・人間レビュー未。 |
| `E-785` | **`PROVED-LEAN`** | `Recaman/SupplyExcursionSpacing.lean` ([G5 audit](statement_audits/E-785.md)) | 任意 `BlockWord ++ A^a` 前史・任意高さ `r` で `actual_same_height_supply_three_slots`, `same_height_supply_three_spacing_budget`, `actual_floor_plus_four_three_spacing` (`3*E_{m+4} ≤ 8*free`), `dyadic_height_weighted_capacity` (`q=1/2, C=3`), `actual_height_exp_two_bound` (`A_{m+h} ≤ 3*2^h*free`) を無条件証明（18/24 substantive, vacuity 0/0）。新 cone `ρ ≈ 1.8067 < 2 < 2.2056`。 |
| `E-786` | **`PROVED-PAPER`** | [Exponential cascade note](RESEARCH_NOTE_2026-11-27_EXPONENTIAL_CASCADE.md) | 全 `H ≥ 2`, `ε > 0`, 任意旧前史 `U` で `Fw ∈ [0, H+1]` の明示再帰平衡語 `B_H` が `A(B_H)/(F+O_c) ≥ (12/25 - ε)(5/3)^H` を達成。多項式上界と `q > 3/5` 容量を反証し、成長基数を `[5/3, 1.8067]` へ狭窄。整数平均高さのため greedy 実行・canonical 前史未構成、C1 反例ではない。未Lean・人間レビュー未。 |

---

## 4. 変更・新規作成ファイル（Changed Files）

- **Lean 4 モジュール（3本、各1モジュール・30分以上間隔で通常コミット、`RECAMAN_ALLOW_BURST=1` 不使用）**:
  - `Recaman/CanonicalGapCapacity.lean` (`E-781`)
  - `Recaman/CrossBlockReuseUnbounded.lean` (`E-783`)
  - `Recaman/SupplyExcursionSpacing.lean` (`E-785`)
  - 更新: `Recaman.lean`, `Recaman/Audit.lean`
- **G5 Statement Audits**:
  - `docs/statement_audits/E-781.md`, `docs/statement_audits/E-783.md`, `docs/statement_audits/E-785.md`
- **仮説カード・研究ノート**:
  - `docs/HYPOTHESIS_CARD_2026-11-27_SPATIAL_GAP_INVENTORY.md`, `docs/RESEARCH_NOTE_2026-11-27_SPATIAL_GAP_INVENTORY.md`
  - `docs/HYPOTHESIS_CARD_2026-11-27_CROSS_BLOCK_REUSE.md`, `docs/RESEARCH_NOTE_2026-11-27_CROSS_BLOCK_REUSE.md`
  - `docs/HYPOTHESIS_CARD_2026-11-27_EXCURSION_SPACING.md`, `docs/RESEARCH_NOTE_2026-11-27_EXCURSION_SPACING.md`
  - `docs/HYPOTHESIS_CARD_2026-11-27_EXPONENTIAL_CASCADE.md`, `docs/RESEARCH_NOTE_2026-11-27_EXPONENTIAL_CASCADE.md`
  - `docs/HYPOTHESIS_CARD_2026-11-28_CROSS_HEIGHT_CAPACITY.md`（次回用、`CONJECTURED`）
- **再現可能 Python 発見・反証・ホールドアウトスクリプト（`COMPUTED` 支持）**:
  - `docs/data/depth_general_20261127/spatial_inventory_audit.py`
  - `docs/data/depth_general_20261127/spatial_inventory_holdout.py`
  - `docs/data/depth_general_20261127/cross_block_discovery.py`
  - `docs/data/depth_general_20261127/cross_block_holdout.py`
  - `docs/data/depth_general_20261127/excursion_spacing_audit.py`
  - `docs/data/depth_general_20261127/exponential_cascade_audit.py`
- **共有台帳・追跡文書**:
  - `docs/EVIDENCE_REGISTRY.tsv`, `docs/CURRENT_FRONTIER.md`, `docs/RESEARCH_GENERALIZATION_TRACKER.md`, `docs/RESEARCH_PORTFOLIO.md`, `docs/RESEARCH_HANDOFF_2026-11-27_DAILY.md`, `viewer/manifest.json`
- **不変確認**: `docs/PROTECTED_CLAIMS.tsv` および `docs/protected_pins/` は無変更（`git diff origin/main` 差分 0）。

---

## 5. 実行コマンドと検証結果（Commands Run）

- Python 反証・発見・ホールドアウト（全5本 exit 0）:
  - `python3 docs/data/depth_general_20261127/spatial_inventory_audit.py`（4.31s CPU: `a(0..1000)` 発見 / `a(1001..5000)` holdout, 63 disc / 192 holdout 語）
  - `python3 docs/data/depth_general_20261127/spatial_inventory_holdout.py`（0.13s CPU: 長さ8全256語, `E-777 W_1..W_4`, `H ≤ 1` 197語 `S^L`, 負例対照 `AAS`）
  - `python3 docs/data/depth_general_20261127/cross_block_discovery.py`（0.49s CPU）
  - `python3 docs/data/depth_general_20261127/cross_block_holdout.py`（4.68s CPU: 6種非空前史 `U`, coherent 2-block, Family A `k=1..5`, Family B disc `k=3,4` & frozen holdout `k=5..7` 最大 `Q=1,902,094`, 8条件 literal greedy replay）
  - `python3 docs/data/depth_general_20261127/excursion_spacing_audit.py`（4.50s CPU: 全32,766語 `L=1..14` 発見, 10,000件 random `BlockWord ++ A^a ++ tail` holdout, `E-783 H=3k (k=1..6)` シャープ性 `0.989691`, 負例対照 `SAAASS` & 非 `BlockWord` 前史）
  - `python3 docs/data/depth_general_20261127/exponential_cascade_audit.py`（0.12s CPU: `B_0 -> B_2 -> B_3 -> B_4` の実 `EndN` 検証・`H=4 (c_4=2)` 100% 内部 `Win` 供給 `8115/8115`・6種任意前史 `U` 不変性・`H=2..12` 厳密整数スケジュール達成率 `99.91%–100.00%`）
- Lean ビルド・ゲート・vacuity 監査:
  - `python3 scripts/harness_gate.py --lint-module Recaman/CanonicalGapCapacity.lean`（9/10 substantive）
  - `python3 scripts/harness_gate.py --lint-module Recaman/CrossBlockReuseUnbounded.lean`（26/28 substantive）
  - `python3 scripts/harness_gate.py --lint-module Recaman/SupplyExcursionSpacing.lean`（18/24 substantive）
  - `python3 scripts/harness_lean.py --vacuity-row E-781`（0 flagged, 0 unknown, 6 theorems）
  - `python3 scripts/harness_lean.py --vacuity-row E-783`（0 flagged, 0 unknown, 4 theorems）
  - `python3 scripts/harness_lean.py --vacuity-row E-785`（0 flagged, 0 unknown, 5 theorems）
  - `./scripts/check.sh`（全1046ジョブビルド・`Recaman/Audit.lean` 公理監査・禁止トークン検査・G1–G6 Lean pin check・直近 vacuity check すべて通過）
  - `python3 viewer/gen_manifest.py --check`（最新確認済み）

---

## 6. 失敗した試み・反証例（Failed Attempts & Counterexamples）

1. **`empty_gap_tail_peak_le` の初期無条件版**: `hi ≤ a t` を外した無条件上界は `b = 4, (lo, hi) = (6, 11), t = 3`（`22 > 18`）で falsifier に反証された。`hi ≤ a t` を明示することで真の空間ピーク上界へ修正。
2. **`multi_gap_rank_bound` の初期版**: 1つの広い空帯を複数にスライスする反例が falsifier で見つかり、`hi_i ∈ valuesThrough b` の真の空帯鎖 `GapChain` へ厳密化。
3. **`H-20261126-02` の literal 歩幅 `b` 橋格子**: `E-781` の空帯上相異訪問数 (`f7`) と gap-rank (`f8`) で失格（幅 `b` 空帯上に `100N` 点 > 上限 `1`）。余白付き歩幅 `d = b - 200N` で `E-782` を構成。
4. **`E-783` の `minCounterWord` (`[(1,2,1,1),(1,1,1,2)]`) の `E-759` 検査**: `E-759 = (1, 0)`（S着地衝突1件）だったため raw sign Lean 反例として分離保持し、最小 coherent (`E-759 = (0, 0)`) 2-block 反例 `[(2,1,1),(1,1,1,2)]`（`2A = 22 > 21`）を別途 `E-784` で確定。
5. **単純な `3 * E_{r+1} ≤ lowAdditionWeights(r)` 強化案**: `(S A A A S S)^R` の `r = 0`（`3 * E_1 = 3R > R = W_0`）で falsifier が即反証。下降 excursion の出口項 `+ 2 * A_{r-1}` を導入して `E-785` の正確かつ漸近シャープな定理 `3 * E_{r+1} ≤ W_r + 2 * A_{r-1}` に到達。
6. **`BlockWord` 前史なしの `E-785` テスト**: 非 `BlockWord` 負 Dyck 前史 `SASASASSSSAAAASASASA` + `A` + `SASS...` で `r = -1` 違反を確認（負例対照として保存）。`BlockWord` 前史仮定の必要性を裏付けた。

---

## 7. 残存する不確実性と次の一手（Remaining Uncertainty & Next Decision）

- **残るギャップ**:
  - 固定床・高さ幅 `H`（`Fw ∈ [m, m+H+1]`）の実 `EndN` における指数成長基数は `[5/3, 1.8067]`（幾何重み閾値 `κ ∈ [0.5535, 0.6000]`）へ狭められたが、その真値および `E-786` の単位 shift 版が `E-759 = (0,0)` coherent greedy 実行可能性下でも指数成長を保つか否かは未解決。
  - `all-free` / `F + O_c` から `LOW-free`・class 数・`D_depth` への変換、および時刻 `0` からの実行済み canonical 前史構成は依然として未払い。
- **停止勧告（STOPPED）**:
  - 静的 scalar + 空間 gap フィルターのみによる有限語選別（`E-782` で `STOPPED`）。
  - 単一銀行のブロック横断再利用を許す定数勾配の線形多 block `A/(F+O_c)` 課金（`E-783`/`E-784` で `STOPPED`）。
  - 実 `EndN` 固定高さ上での多項式容量探索（`E-786` で反証済み）。
- **次回セッションの判断**:
  - `local_progress = yes`, `depth_general_progress = yes`, 一般化連続停滞 `0` → 次回配分 **`30/60/10`**（別機構 `>= 25min`）。
  - 主ターゲット: [`H-20261128-01`](HYPOTHESIS_CARD_2026-11-28_CROSS_HEIGHT_CAPACITY.md)（`[5/3, 1.8067]` の精密決定、`E-786` の Lean 化、および `E-759 = (0,0)` coherent greedy での指数成長可否判定）。
