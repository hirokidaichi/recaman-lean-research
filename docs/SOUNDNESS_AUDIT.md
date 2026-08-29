# Recamán Lean 形式化リポジトリ 敵対的健全性監査

- 監査基準: commit `e99bd68` + working tree（2026-08-29 17:14 JST 時点）
- 対象: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- 制約遵守: リポジトリ内ファイルは一切変更していない。`lake build` / `scripts/check.sh` / `lake env lean` は実行していない。
- 注意: 別セッションの自律ループが監査中もコミット・ファイル追加を継続している（`Recaman/Audit.lean` は監査中に 576 → 588 directives へ増加、`Recaman/PermanentAboveClock112Obstruction.lean` は 17:13 に出現）。以下の行番号は基準時点のもの。

---

## 監査後の対応状況（2026-08-29、統合担当による追記）

本監査は独立したサブエージェントが読み取り専用で実施したものである。報告後、統合担当が以下を確認・対応した。

| 監査項目 | 対応 |
|---|---|
| §3.3 / OC-1 / OC-4 semantic枝が自明に居住可能 | **独立に再現・確認済み。** 別経路の調査（`Recaman/SemanticOracleRecursion.lean`、commit `252b4ba`）でも同じ結論に到達し、`semantic_or_flooredCore_of_pos`としてLeanで形式化した。ROADMAPの優先順位を組み替え、semantic枝のpayload強化を最優先に設定した。 |
| §5.1 公理監査の完全性が未確認 | **監査時に渡したログが末尾20行のみの切り詰め版だったことによる（依頼側の不備）。** 統合担当が`lake env lean Recaman/Audit.lean`の全出力（602宣言）を機械照合し、**全602宣言が`propext` / `Classical.choice` / `Quot.sound`のみに依存**することを確認した。`sorryAx`・`Lean.ofReduceBool`・ユーザー定義公理はゼロ。 |
| OC-5 check.shが公理集合をassertしていない | **対応済み。** `scripts/check.sh`に公理集合のassertを追加した。許可集合外の公理が一つでも現れれば非ゼロ終了する。宣言数がゼロの場合も失敗させる。 |
| §5.2 Audit.leanから漏れている定理 | **対応済み。** `all_targetResolvable_implies_surjective`、`coverageOracle_implies_occurs`、`refinedPhaseSearchOracle_of_crossing`、`all_targetTailReturn_implies_surjective`、`historicalMinimumTime_after_lowWitness`を追加した。 |
| OC-2 / OC-3 / OC-6 docsの過大主張 | **対応済み。** README・CHANGELOG・PROOF_MAP・RESEARCH_REPORT・DEVELOPMENT_LOG・ROADMAPの該当箇所を訂正した。 |
| §2.3 ready crossing ⊊ crossing の型ギャップ | 未対応。`SemanticOracleRecursion`が同じギャップを`ReadyCrossingRefinedStepHypothesis`と「unready crossing漏れ」へ分解しており、ROADMAP項目3として登録した。 |
| §5.3 孤児モジュール | 別セッションが執筆中の作業ファイルであり、本セッションの管轄外。統合時に当該セッションがrootへimportする。doc コメント内の禁止語については当該セッションへ連絡済み。 |

---

## 0. 総合判定

**偽の定理・`sorry`・隠れ公理は発見されなかった。** 読んだ範囲の Lean 定理はすべて statement 通りに正しく、数値アンカーは独立計算と完全一致した（96件中 95件一致、残り1件は背理法の中間式で claim ではない）。

一方で、**「証明の内容」と「docs が読者に与える印象」の間に、複数の重大な乖離**がある。最大のものは、リポジトリの過半（`PermanentAbove*` 系 約90モジュール）が終着している主張型が **論理的に自明に居住可能** で、情報量ゼロだという点である。これは不健全（unsound）ではないが、「反例を締め上げている」という研究上の主張を実質的に支えていない。

---

## 1. 定義の正しさ ✔ 合格

### 1.1 数列定義

`Recaman/Basic.lean`:

```lean
def CanSubtract (n : Nat) (state : State) : Prop :=
  n < state.value ∧ state.value - n ∉ state.seen
def nextValue (n : Nat) (state : State) : Nat :=
  if CanSubtract n state then state.value - n else state.value + n
def stateAt : Nat → State
  | 0 => initial            -- initial = ⟨0, [0]⟩
  | n + 1 => step (n + 1) (stateAt n)
def a (n : Nat) : Nat := (stateAt n).value
```

- `n < state.value` ⟺ `state.value - n > 0`（Nat の切り捨て減算を正しく回避している）。
- `state.value - n ∉ state.seen` が「未出」。`seen` は `[0]` から始まり全履歴を保持。
- OEIS A005132 の標準定義（a(0)=0、a(n)=a(n-1)-n が **正かつ未出** ならそれ、さもなくば a(n-1)+n）と完全一致。

独立実装（`scratchpad/audit/recaman.py`、Lean を見ずに標準定義から起こしたもの）と照合:

```
first 16: [0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24]
```

`Basic.lean` 末尾の `example : (List.range 16).map a = [...] := by decide` と一致。200項まで一致を確認。**問題なし。**

### 1.2 最終目標の言明

- `Recaman/Coverage.lean:144` `all_coverageOracles_imply_surjective : (∀ m, 0 < m → CoverageOracle m) → ∀ m, ∃ t, a t = m`
- `Recaman/CrossingTailRefined.lean:210` `all_targetTailReturn_iff_surjective : (∀ target, TargetTailReturnHypothesis target) ↔ ∀ target, ∃ time, a time = target`

結論の `∀ m, ∃ t, a t = m` は正真正銘の全射性（ℕ 上）。`m` に上限や型制約はない。**言明のすり替えは無い。**

---

## 2. ギャップ地図

### 2.1 実際に無条件で証明されている最前線

```
∀ m, ∃ t, a t = m                          ← 未証明（最終目標）
  ⇐ ∀ m>0, CoverageOracle m                 [Coverage.lean:144]      含意は証明済み
  ⇐ ∀ m>0, TargetResolvable m               [Coverage.lean:110]      含意は証明済み
        └ ただし TargetResolvable は強すぎる：m=1 で反証済み
          (`not_targetResolvable_one`)

主線（phase search）:
∃ t, a t = target
  ⇐ 0 < target ∧ CrossingRefinedStepHypothesis target
                                            [RefinedOracleBoundary.lean:66] 含意は証明済み
      ├ 非crossing constructor（ready current / ready debt / extended-history）
      │   は残余なしで証明済み            [RefinedOracleBoundary.lean:26]
      └ crossing constructor：**未証明**（唯一の残余）
            部分成果: horizon_ready 付きの ReadyCrossingSearchInvariant に限れば
              TargetTailReturnHypothesis から閉じる
                                            [CrossingTailRefined.lean:296]
```

### 2.2 仮定として置かれている命題の分類

| 命題 | 定義位置 | 判定 |
|---|---|---|
| `CoverageOracle m` | Coverage.lean:24 | **(b) 仮定のまま** |
| `TargetResolvable m` | Coverage.lean:11 | **(b)** かつ m=1 で**反証済み**（`not_targetResolvable_one`）。使えない |
| `PhaseSearchOracle m` | PhaseSearch.lean:118 | (b) 仮定のまま |
| `RestrictedPhaseSearchOracle m Valid` | PhaseSearchStart.lean:57 | (b) 仮定のまま |
| `SemanticPhaseSearchOracle target` | PhaseSemantic.lean:216 | (b) 仮定のまま |
| `HistorySearchOracle m` | HistoryBudget.lean:386 | (b) 仮定のまま |
| `CrossingRefinedStepHypothesis target` | RefinedOracleBoundary.lean:16 | **(b) 仮定のまま。これが現在の唯一の主残余** |
| `ReadyCrossingTailDowncrossHypothesis target` | CrossingTailRefined.lean:219 | **(c) 別の仮定へ還元されただけ**（`TargetTailReturnHypothesis` から従う） |
| `TargetTailReturnHypothesis target` | CrossingTailRefined.lean:169 | **(c) 全射性そのものと同値であることが証明済み**（CrossingTailRefined.lean:210） |
| `DiagonalSuccessorProperty` | (ROADMAP.md:70 が言及) | (b) 仮定のまま |

### 2.3 GAP B1（未文書の型ギャップ）

`CrossingRefinedStepHypothesis` は **素の** `CrossingSearchInvariant target node` 全体に対する義務（RefinedOracleBoundary.lean:16-20）。
一方、閉包が証明されているのは `ReadyCrossingSearchInvariant`（= `CrossingSearchInvariant` + `horizon_ready : target ≤ node.horizon + 1`、CrossingDowncrossRefined.lean:17-20）のみ。

- `OrbitReadyRefinedInvariant` の第3成分は素の `CrossingSearchInvariant`（OrbitReadyRefinedStep.lean:31）で、`horizon_ready` を保持していない。
- `CrossingSearchCertificate` が内包する `CrossingRecoveryInvariant`（CrossingRecovery.lean:10-17）は `crossing_before_horizon : n + 1 < horizon` を持つが、`target ≤ horizon + 1` は導かない（`a n < target ≤ a n + n + 1` から horizon の上界は出ない）。
- リポジトリ内に「refined domain 内の crossing node は必ず ready」という補題は **存在しない**（`horizon_ready` の grep 結果、構成側のみで消費側の橋渡し無し）。

したがって、**仮に `TargetTailReturnHypothesis` を認めても `CrossingRefinedStepHypothesis` は閉じない。** docs（`docs/PROOF_MAP.md:29-31`）は「ready crossing の局所 step は `TargetTailReturnHypothesis` まで縮約済み」と正しく ready 限定で書いているが、同じ PROOF_MAP:56 の「残余を `CrossingRefinedStepHypothesis` ひとつへ縮約」と併読すると、この型ギャップが見えなくなる。

### 2.4 循環の有無 ✔ 論理的循環は無い

- 「A を仮定して B を証明し、B を使って A を証明する」構造は見つからなかった。
- `TargetTailReturnHypothesis ↔ 全射性` は循環ではなく、**明示的に証明された同値性**（CrossingTailRefined.lean:210）。docs も README.md:154 等で正直に同値と書いている。ただしこれは「残余が本質的に元の問題と同じ強さ」であることの証明でもあるので、進捗としては中立である。

---

## 3. 空虚性（vacuity）検査

### 3.1 依頼された4構造体の判定

| 構造体 | 判定 | 根拠 |
|---|---|---|
| `TailFixedPointCore` (FixedPointCore.lean:23-31) | **居住可能（vacuous でない）** | 下記 3.2 |
| `TerminalExactDischargeReplayCertificate` (SuccessorRank.lean:102-127) | **予想が真なら無人。無人性は未証明。これは「勝利形」であって欠陥ではない** | `PermanentTailDischargeReturnCertificate` 経由で `MissingStrictAboveTail`（target 未出）を内包 |
| `PermanentTailDischargeReturnCertificate` (PermanentAboveCycleExit.lean:23-46) | 同上 | `historical_tail : MissingStrictAboveTail target tailStart` |
| `LeastMissingTarget` (CrossingTailRefined.lean:70-72) | 予想が偽のとき、かつそのときに限り居住 | 定義通り |

**docs が「排除した」と書いている箇所で無人性が未証明、というパターンは見つからなかった。** 排除定理（`target_ne_nineteen` 等）はすべて「証明書が存在すれば矛盾」という含意として正しく書かれている。

### 3.2 `TailFixedPointCore` は実際に居住する（重要）

`terminalPredecessorCrossingNode parent c = ⟨parent.horizon, a c, .normal, a c⟩`（PredecessorCrossing.lean:24-26）なので、`node_reproduction` は `parent = ⟨h, a c, .normal, a c⟩` を意味する。よって `TailFixedPointCore target parent c` の内容は実質:

- `parent = ⟨h, a c, .normal, a c⟩`（h は自由）
- `a c < target ≤ a (c+1)`
- `a (c+1) = a c + (c+1)`（強制加算）

具体的証拠: `c = 2`（`a 2 = 3`, `a 3 = 6 = 3 + 3` は強制加算）、`target = 4`、`parent = ⟨h, 3, .normal, 3⟩` で全フィールドが成立する。

→ したがって **`TailFixedPointCore` 単体に床は付かない**。実際、床定理はすべて `(missing : ¬ ∃ time, a time = target)` を追加で取る（例: FixedPointFloorTwo.lean:43-46 `nineteen_le_target (core) (missing) : 19 ≤ target`）。**これは正しい設計であり、docs の記述とも整合する。** 空虚性の問題は無い。

### 3.3 【重大】12個の outcome 型が自明に居住可能 — ここが本当の空虚性

`PermanentTailUnifiedOutcome`（FixedPointCore.lean:47-73）の第一コンストラクタ:

```lean
| semantic_progress
    (stepParent child : PhaseSearchNode)
    (semantic : PhaseSemanticInvariant target child)
    (progress : PhaseSearchProgress target child stepParent) :
    PermanentTailUnifiedOutcome target start
```

`stepParent` が**完全に自由**で、`start` とも証明書とも一切結び付いていない。よって次が成り立つ:

**主張**: 任意の `target > 0`・任意の `start` に対し `PermanentTailUnifiedOutcome target start` は、証明書を一切使わずに約5行で構成できる。

構成（リポジトリ内の既存補題のみ使用、コンパイルは未実行）:

1. `exists_targetStartNode : 0 < m → ∃ node, TargetStartInvariant m node`（PhaseSearchStart.lean:45）で `node = targetStartNode n = ⟨n, a n, .normal, a n⟩` を得る。
2. `targetStartInvariant_phaseSemantic`（PhaseSemantic.lean:72）で `PhaseSemanticInvariant target node`。
3. `phaseSearchProgress_of_horizonAndAnchor (htime : parentHorizon ≤ childHorizon) (hanchor : childAnchor < parentAnchor)`（NormalClosure.lean:56-63）に `parentHorizon = childHorizon = n`、`parentAnchor = a n + 1`、`childAnchor = a n` を与えれば `PhaseSearchProgress target ⟨n, a n, .normal, a n⟩ ⟨n, a n + 1, .normal, a n⟩` が出る。
4. `.semantic_progress ⟨n, a n + 1, .normal, a n⟩ (targetStartNode n) ... ...`

同じ形の `semantic_progress`（`stepParent` 自由）は次の12モジュールに現れる:

`FixedPointCore.lean:49`, `HistoryLanding.lean:88`, `IterationClosure.lean:33`, `LandingHorizon.lean:43`, `LandingMount.lean:89`, `MountedIteration.lean:27`, `ReplayInterface.lean:31`, `SuccessorRank.lean:144`, `TerminalProgress.lean:30`, `TerminalSuccessor.lean:28`（`ReplayBoundary.lean:91` だけは `progress : ... child parent` と束縛されている）。

**なぜこうなっているか**（設計上の必然であり単純ミスではない）: `TerminalProgress.lean:44-77` の証明を見ると、semantic 枝が返す stepParent は分岐ごとに
`targetStartNode (source.downTime + 2)` / `terminalHistoricalPredecessorNode parent (firstTime - 1)` / `terminalCurrentPredecessorNode (firstTime - 1)` / `parent`
とバラバラである。モジュール冒頭のコメント（TerminalProgress.lean:12-15）自身が「semantic edge stores its actual local parent … rather than being forced to compare against the original discharge parent」と述べている。

**帰結（これが最大の発見）**:

- `LeastMissingTarget.semantic_or_flooredCore`（Summit.lean:52）と `LeastMissingTarget.semanticProgress_or_nineteen_le`（Summit.lean:67）は、**`LeastMissingTarget` 仮説を一切使わずに左枝だけで証明できる**。すなわち情報量がゼロ。
- 「固定点 core を全部排除すれば semantic 枝が残る」→ その semantic 枝は常に真なので **何の矛盾も出ない**。
- `RestrictedPhaseSearchOracle`（PhaseSearchStart.lean:57-62）は「**与えられた** parent に対して child を返す」ことを要求する。stepParent が自由な形の semantic 枝は、原理的にこの oracle に接続できない。「consumer をこれから作る」ではなく、**この形のままでは consumer は存在し得ない**。

`docs/ROADMAP.md:389-390` は「semantic 枝の消費者…固定点が全て排除できたとしても、これが無ければ大域組み立ては完成しない最古の負債である」と自覚しているが、負債の性質を「未実装」と捉えている。実際には**主張型の設計を直さない限り実装不可能**である。

### 3.4 `Recaman/Examples.lean` ✔ 適切

`firstAt_seven`（:5）、`actualBlocker_at_five : ActualBlocker 5 7 0 1`（:44）、`targetAttempt_seven_to_one`（:60）など、低層構造体の具体的居住証拠を `decide` で与えている。これらは「blocker 機構が空回りしていない」ことを保証する本物の inhabitation。加えて `NormalSemanticBoundary.lean:39-63, 66-88` は「証明書が期待される性質を持たない」反例（`normalSearchCertificate_coordinates_not_at_horizon`、`normalSearchInvariant_does_not_imply_time_ready`）を明示しており、健全な自己批判である。

---

## 4. docs の主張と Lean の実態の照合（overclaim 一覧）

### OC-1【重大】ROADMAP が「固定点を排除すれば全射性が従う」と書いている

- 主張: `docs/ROADMAP.md:372`
  > 固定点の排除が完了した時点で`TargetTailReturnHypothesis`が無条件化し、全射性が従う。
- 反証: 固定点を排除して得られるのは `Summit.lean:52` の左枝（semantic progress）のみ。§3.3 の通りこれは無条件に真なので矛盾は出ず、`TargetTailReturnHypothesis` は導かれない。加えて §2.3 の型ギャップ（ready vs 素の crossing）も残る。同一ファイル `ROADMAP.md:389-390` が「これ（semantic 枝の消費者）が無ければ大域組み立ては完成しない」と自ら述べており、**文書内で自己矛盾**している。
- 訂正案:
  > 固定点の排除が完了しても、それだけでは `TargetTailReturnHypothesis` は無条件化しない。統合 outcome の semantic 枝（`PermanentTailUnifiedOutcome.semantic_progress`）は `stepParent` を自由変数として持つため無条件に居住可能であり、固定点枝を潰しても矛盾は生じない。全射性へ到達するには、(i) semantic 枝の `stepParent` を元の discharge parent（または outer 再帰の現 parent）へ束縛するよう主張型を再設計し、(ii) `CrossingRefinedStepHypothesis` の素の `CrossingSearchInvariant` を ready 化する橋を証明する、の二つが追加で必要である。

### OC-2【中】「無条件 112≤clock・114≤target」の適用範囲が明示されていない

- 主張: `README.md:139`／`CHANGELOG.md:27`／`docs/RESEARCH_REPORT.md:922`／`docs/DEVELOPMENT_LOG.md:1389-1390`／`docs/ROADMAP.md:374`
  > 床を無条件112≤clock・114≤targetへ引き上げ済み
- 実態: `PermanentAboveCorridorReplayFloorFour.lean:843` `onehundredtwelve_le_crossingTime (r : TerminalExactDischargeReplayCertificate source) : 112 ≤ r.crossingTime`、同 :877 `onehundredfourteen_le_target ... : 114 ≤ target`。**`TerminalExactDischargeReplayCertificate`（= discharge replay 枝）についてのみ。**
  統合 outcome はこの枝を含め3枝あり（FixedPointCore.lean:47-73）、`landing_cycle` 枝は replay 証明書を持たず `TailFixedPointCore` しか持たないため、床は依然 `18 ≤ crossingTime ∨ target = 19` と `19 ≤ target`（Summit.lean:33）のまま。したがって「最小未出目標は 114 以上」ではない。
  `docs/PROOF_MAP.md:143` は「replay kernel floor IV」と枝名を付けており正確。README/CHANGELOG/RESEARCH_REPORT が修飾を落としている。
- 訂正案:
  > 床を **discharge replay 固定点枝について** 無条件 `112 ≤ clock`・`114 ≤ target` へ引き上げ済み（landing 固定点枝の床は依然 `18 ≤ clock ∨ target = 19` および `19 ≤ target`）。

### OC-3【中】「例外リストを空に」が現在の状態を表していない

- 主張: `README.md:135`
  > 同機構でtarget 61のreplayも完全排除し、例外リストを空に：無条件32≤clock・target≥34
- 実態: clock ≤ 32 の掃過については正しい（`SixtyoneElimination.lean:770 thirtytwo_le_crossingTime` は例外なしの無条件形）。しかし clock 112 では新たな例外 371 が生きている（`PrefixSuccessorCoverage.lean:158 prefixSuccessorCoverageExcept_onehundredtwelve : ReplayPrefixSuccessorCoverageExcept 112 371 371`）。`DEVELOPMENT_LOG.md:1391` は「19・61・76に続く第四の深部残留値」と正しく書いている。
- 訂正案: README:135 の直後に一文追加、
  > （ただし床を 112 まで上げた段階で、新たな深部残留値 371（初出 t=4825）が例外として現れている。例外リストが空なのは clock 32 までの掃過に限る。）

### OC-4【中】「19 未満の反例が到達し得る経路は semantic 枝だけ」が誤誘導

- 主張: `README.md:249-251`／`docs/PROOF_MAP.md:592-593`／`docs/DEVELOPMENT_LOG.md:1281-1282`
  > 固定点で終端する反例のtargetは無条件に19以上で、19未満の反例が外側再帰へ到達し得る経路はsemantic枝だけです。
- 反証: §3.3 の通り semantic 枝は**すべての** target について常に居住可能なので、「semantic 枝だけ」は制約になっていない。この文は「ほとんどの反例を排除した」という印象を与えるが、実際には何も排除していない。
- 訂正案:
  > 固定点で終端する場合の target は 19 以上である。ただし統合 outcome の semantic 枝は `stepParent` が自由なため無条件に居住可能であり、この二分岐は現時点では target に対する制約を与えない。semantic 枝を制約にするには、`stepParent` を outer 再帰の現 parent へ束縛する主張型の再設計が必要である。

### OC-5【小】`scripts/check.sh` は公理集合を検証していない

- 主張: `README.md:14`「主要定理の公理監査を同梱」、`README.md:16`「`sorry`、`admit`、ユーザー定義公理、`native_decide`は不使用」
- 実態: `scripts/check.sh:22-27` は `lake env lean Recaman/Audit.lean` を**実行して出力を印字するだけ**で、出力内容（`propext`/`Classical.choice`/`Quot.sound` 以外が現れていないか）を一切 assert していない。`sorry` は Lean では warning であり終了コードは 0 なので、`#print axioms` が `sorryAx` を印字してもスクリプトは成功する。人間が目視する前提の advisory チェックである。
- 訂正案: check.sh に `lake env lean Recaman/Audit.lean | grep -vE '^\s|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$'` 相当の assert を追加するか、docs 側を「公理監査の出力を同梱（合否判定は目視）」と正確に書き換える。

### OC-6【小】`852655` の主張に出典がない

- 主張: `docs/ROADMAP.md:377`
  > 経験的には852655が10²³⁰項を超えても未出であり、偽仮説は真剣に考慮すべきである。
- 実態: 独立検算で 3×10⁶ 項までは未出であることを確認した。10²³⁰ という規模は本監査では**検算不能**で、リポジトリ内にも出典・計算手順が無い。
- 訂正案: 出典（OEIS A005132 のコメント／Benjamin Chaffin の計算等）を明記するか、「外部報告によれば」と留保を付ける。

### 過大主張では**ない**と確認したもの

- `README.md:7-8`, `README.md:281`, `docs/RESEARCH_REPORT.md:5, :589, :933-934`, `CHANGELOG.md:134`: 「全射性は未証明」を繰り返し明記。**適切。**
- `README.md:154`／`docs/PROOF_MAP.md:61`: tail return と全射性の同値性を隠していない。**適切。**
- `docs/RESEARCH_REPORT.md:593-600`, `:930-931`, `docs/PROOF_MAP.md:640`: 計算実験の結果を Lean 証明に取り込んでいない旨を明記。**適切。**
- `docs/ROADMAP.md:378-379`: 「床上げは漸近的には定理へ近づかない」と自ら限界を述べている。**極めて健全。**

---

## 5. 公理監査の完全性

### 5.1 記録された `check.sh` 出力の判定

`/private/tmp/.../tasks/b4085um5s.output`（1593 bytes）:

- `EXIT=0`、末尾に `All Lean builds and audits passed.` → その時点でビルドと禁止語走査は通っている。
- しかし `depends on axioms` 行は **12件しか含まれていない**（`Recaman/Audit.lean:568-579` に対応する末尾のみ。ログが先頭側で切られている）。当時の Audit.lean は 576 directives。
- 見えている12件はすべて `[propext, Quot.sound]` のみ。`sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` / ユーザー公理は**この12件については**無い。
- **判定（監査時点）: この成果物から「576件すべてが標準3公理のみ」と結論することはできない（2%しか見えていない）。**

> **追記（統合担当）**: 上記は依頼側が渡したログが末尾20行の切り詰め版だったことによる。全出力（602宣言）を機械照合した結果、**全602宣言が`propext` / `Classical.choice` / `Quot.sound`のみに依存**することを確認した（許可集合外はゼロ件）。またOC-5の指摘を受けて`scripts/check.sh`に公理集合のassertを追加したため、以後はEXIT=0が公理の清潔さを意味する。

補助的根拠として、私自身が全 `.lean` を grep した結果、`sorry` / `admit` / `axiom` 宣言 / `native_decide` 実使用 / `debug.skipKernelTC` / `implemented_by` / `unsafe` / `opaque` / `#exit` はいずれも存在しなかった（唯一のヒットは §5.3 のコメント）。したがって公理汚染の可能性は低いが、**「検証済み」とは言えない**。

### 5.2 Audit.lean から漏れている重要定理

基準時点の Audit.lean（588 directives）に **無い** もの:

| 定理 | 位置 | 深刻度 |
|---|---|---|
| `all_targetResolvable_implies_surjective` | Coverage.lean:132 | 中（`all_coverageOracles_imply_surjective` とは別の仮定族。他の監査済み定理に包含されない） |
| `refinedPhaseSearchOracle_of_crossing` | RefinedOracleBoundary.lean:46 | 中（主線の骨格定理） |
| `all_targetTailReturn_implies_surjective` | CrossingTailRefined.lean:191 | 低（`all_targetTailReturn_iff_surjective` が直接呼ぶので推移的に包含） |
| `coverageOracle_implies_occurs` | Coverage.lean:102 | 低 |
| `historicalMinimumTime_after_lowWitness` | PrefixSuccessorCoverage.lean:58 | 低 |
| `clock112_target_prefix_coverage` | PermanentAboveClock112Obstruction.lean:18 | **高**（§5.3 参照：そもそもビルドされていない） |

`PermanentAboveCorridorReplayFloorFour.lean` は23定理中2つしか監査されていないが、監査済みの2つ（`onehundredtwelve_le_crossingTime`, `onehundredfourteen_le_target`）が残り全部に依存するので公理カバレッジは推移的に足りている。粒度の問題であり穴ではない。

### 5.3 【重大】ビルドされていない孤児モジュール2つ

`lakefile.toml` は `[[lean_lib]] name = "Recaman"` のみで glob 指定が無く、`lake build` は `Recaman.lean` の import 閉包しかコンパイルしない。`Recaman.lean` は162 import。`Recaman/` には165ファイル。差の3つは `Audit.lean`（意図的）と:

- `Recaman/PermanentAboveClock112Obstruction.lean`（untracked、17:13 作成）— どこからも import されていない。含まれる `clock112_target_prefix_coverage`（`∀ value : Fin 262 … ∃ witness : Fin 2623` を `maxRecDepth 1000000` の素の `decide` で証明）は**一度も型検査されていない**。
- `Recaman/ChunkedTraceCertificate.lean`（untracked、監査中も 336 → 370 行と成長し続けている執筆途中のファイル）— どこからも import されていない。したがって内容は一度も型検査されていない。重複宣言などの構文的問題は基準時点では検出できなかった。

**加えて**: `ChunkedTraceCertificate.lean:282` のコメント内に文字列 `native_decide` が含まれる。`scripts/check.sh:24` の `rg -n --glob '*.lean' '\b(sorry|admit|native_decide|axiom)\b' .` は rg のデフォルトで .gitignore を尊重するがこのファイルは untracked かつ ignore 対象外なので走査される。**現在の作業ツリーのままでは `./scripts/check.sh` は禁止語検出で exit 1 になる。**（監査制約により実行はしていない。パターンと該当行から機械的に判定。）

### 5.4 走査パターンの盲点（現時点で悪用されてはいない）

`\b(sorry|admit|native_decide|axiom)\b` は次を検出しない: `sorryAx`（`\bsorry\b` は `sorryAx` にマッチしない）、`set_option debug.skipKernelTC true`、`Lean.ofReduceBool` / `Lean.trustCompiler` の直接参照、`#exit`、`@[implemented_by]`、`unsafe`、`opaque`。いずれも現時点でリポジトリに存在しないことを確認済み。ただし `sorryAx` の穴は本来 `#print axioms` が塞ぐべきもので、§5.1 の通りその出力が検証されていないため、二重の防御が両方とも緩い。

---

## 6. 数値アンカーの独立検証 — 全件一致

Lean ソース中の `a N = M` 形の式を機械抽出（96件、`scratchpad/audit/lean_anchors.txt`）し、独立 Python 実装と照合:

```
matched: 95   mismatched: 1
  MISMATCH  a 2 = 2  (actual 3)
```

唯一の不一致 `a 2 = 2` は `Recaman/NormalSemanticBoundary.lean:61` の背理法の中間式で、直後の `:62` で `exact (by decide : a 2 ≠ 2) heq'` により矛盾として使われている。**claim ではない。実質 96/96 一致。**

### docs にのみ書かれた数値（Lean で検証されていないもの）の独立検算

| 主張 | 出典 | 検算結果 |
|---|---|---|
| 371 の初出は t=4825 | PROOF_MAP.md:143 ほか | **一致**（first(371)=4825、a[4825]=371） |
| 19 の初出は t=99734 | README.md:220 ほか | **一致** |
| 61 の初出は t=181653 | README.md:222 ほか | **一致** |
| 76 の初出は t=181643 | PROOF_MAP.md:613 | **一致** |
| 370 の初出は t=108 | PrefixSuccessorCoverage.lean:194 の内容 | **一致** |
| clock 112 の帯 `152 < target ≤ 261` | PrefixSuccessorCoverage.lean:214 | **一致**（a 112=152、a 113=265、a 109=261、a 110=151、a 111=40） |
| clock 112 の唯一の未被覆 successor は 371 | PrefixSuccessorCoverage.lean:158 | **一致**（`ReplayPrefixSuccessorCoverage 112 371` を全数チェック → 未被覆は t=108（a=370, successor 371）のみ） |
| cutoff 99734 の coverage は clock 776 まで続き、次は clock 777・successor 879（初出 328002） | RESEARCH_REPORT.md:930-931 | **first(879)=328002 は一致**。clock 776/777 の境界は、`ReplayPrefixSuccessorCoverage` をそのまま適用した私の実装では clock 129 で先に失敗する（successor 76 が cutoff 99734 以内に未出。first(76)=181643）。docs の「eligible clock」は追加の eligibility フィルタ（record 排除・downcross 前置界など）を掛けた後の数え方と思われる。**docs 側にその定義が書かれていないため再現不能。**「経験的結果でLean証明には未使用」と明記されている点は適切。 |
| 21 は prefix で t=9 の一度きり | README.md:133 | **一致**（t≤400000 で 21 の出現は t=9 のみ） |
| a 222 = 47（47 は t=222 のみ）／a 131 = 4／a 129 = 5 | 各所 | **一致**（4 は t=131 のみ、5 は t=129 のみ、47 は t=222 のみ、t≤400000） |
| 852655 が 10²³⁰ 項でも未出 | ROADMAP.md:377 | **t≤3×10⁶ では未出を確認。10²³⁰ 規模は検算不能・出典不明**（→ OC-6） |
| `clock112_target_prefix_coverage`（新規未ビルド）: (152,261] の値は 223 を除き t≤2622 で出現 | PermanentAboveClock112Obstruction.lean:18 | **数学的には一致**（唯一の例外 223、first(223)=181545）。ただしこのファイルはビルド対象外（§5.3） |

一般力学補題 `value_no_late_recurrence`（ReplayFloorFour.lean:35、`a w = v`, `w < m`, `v < m`, `a m = v` → False）も独立検証: t≤300000 の全 86267 件の値再訪について反例ゼロ。証明も妥当（`v < m` があるので加算枝は overshoot、減算枝は freshness 違反）。

---

## 7. 優先度付き推奨

1. **（最優先）semantic 枝の主張型を修正する。** `PermanentTailUnifiedOutcome` 系12型の `semantic_progress` から自由変数 `stepParent` を除き、`progress : PhaseSearchProgress target child parent`（`ReplayBoundary.lean:91` と同じ形）へ束縛する。束縛できない分岐が出るなら、それが本当の残余であり、そこを明示すべき。この修正なしには床上げが何ラウンド成功しても全射性へは近づかない。
2. **ROADMAP.md:372 を訂正する**（OC-1）。現在の記述は投資判断を誤らせる。
3. **`CrossingSearchInvariant` → `ReadyCrossingSearchInvariant` の橋を証明するか、不可能性を明示する**（§2.3）。
4. **`check.sh` に公理集合の assert を追加し、フルログを保存する**（OC-5、§5.1）。現状「公理監査済み」は目視前提。
5. **孤児モジュール2つを `Recaman.lean` へ import するか削除する**（§5.3）。特に `ChunkedTraceCertificate.lean` は現状 check.sh を落とす。
6. 床上げ（clock 112 → それ以上）は ROADMAP.md:378-379 の自己評価通り、上限付きの副次作業に留めるのが妥当。
