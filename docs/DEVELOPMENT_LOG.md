# 開発記録 — Recamán sequence Lean 4 formalization

この文書は各証明エポックで得られた詳細な技術記録である。
研究全体の要約は[研究結果レポート](RESEARCH_REPORT.md)、現在の依存関係は
[証明地図](PROOF_MAP.md)、次の作業は[ロードマップ](ROADMAP.md)を参照すること。

レカマン数列の全整数出現問題に向けた、機械検証済みの研究基盤です。
大域的な全射性そのものはまだ証明していません。局所力学、履歴blocker、
有限降下、負ポテンシャル・エポックを分離し、未証明の到達可能性を
仮定として紛れ込ませない構成にしています。

## 検証環境

- Lean 4.33.1（`lean-toolchain` で固定）
- Lean標準ライブラリのみ
- `sorry`、`admit`、ユーザー定義 `axiom` は不使用
- Presburger算術には標準タクティク `omega` を使用

通常のLean環境では次で検証できます。

```bash
lake build
lake build Recaman.Audit
```

このWorkサンドボックスでは、同梱の薄いラッパーを使います。

```bash
./scripts/lakew build
./scripts/lakew build Recaman.Audit
```

## 今回のエポックの主結果

時刻 `n>0` の実軌道を

```text
aₙ = n q + r,   0 ≤ r < n,
G(q,r) = r - U(q),   U(q)=q(q+1)/2
```

と書きます。

### 1. 実軌道では多段借りが起こらない

まず全時刻について

```text
aₙ ≤ U(n),       2q ≤ n+1
```

を証明しました。借用証明書

```text
b(n+1)+r=q+s,   0≤s<n+1
```

と組み合わせると、実軌道では常に

```text
b=0 または b=1
```

です。したがって、以前の「多段借りが負領域を繰り返しリセットする」
可能性は実軌道上では完全に排除されました。

### 2. 負領域は有限時間で一段借りへ到達する

`G(q,r)<0` かつ `b=0` なら

```text
q≥2,       s+2≤r
```

です。ゼロ借用が続くたびに剰余が少なくとも2減るため、任意の負状態から
高々 `⌊r/2⌋` 歩以内に必ず `b=1` の遷移へ到達します。

これは経験則ではなく、実軌道についての無条件なLean定理
`eventually_oneBorrow_of_negative_halfRemainder` です。

### 3. 一段借りの厳密な回復予算

一段借りの欠損を `δ=q-r` と置くと、

```text
0<δ≤q,       r+δ=q,       s+δ=n+1
G(q,r)=-(T(q)+δ)
```

が成立します。遷移によるポテンシャル増加は厳密に

```text
加算: ΔG=n+1-q
減算: ΔG=n+q
```

です。実軌道の商上界により、どちらの一段借りも `G` を厳密に増加させます。

目標面 `G=m` への着地時計も

```text
n+1 = U(k)+m+δ
```

と完全に決まります。この式から、`k=2,3` のexact gate／local escape面へ
着地できる時刻窓もLeanで導出しています。

### 4. 低商回復と高商障壁

実際の一段借り遷移について、着地商 `k≤3` なら必ず `G'≥0` です。
したがって非負回復に失敗するなら

```text
k≥4
```

でなければなりません。加算側の高商失敗では、阻害された減算候補

```text
y=aₙ-(n+1)
```

が既出で、しかも `2(n+1)≤y<aₙ` です。この値の初出時刻を取れば、
高商加算は「失敗」ではなくblockerによる値下降へ変換できます。

### 5. CoverageStepの簡約

大域帰納法を監査すると、後継ノードに必要なのは

```text
m≤y<a current
```

と `y` の初出証明だけであり、初出時刻まで親より小さいことは不要でした。
そこで `CoverageStep` を値の強帰納法に必要十分な形へ簡約しました。

- blockerは従来どおり「値と初出時刻の二重降下」を証明する
- 大域インターフェースは、そのうち必要な値下降だけを要求する
- 合法な減算は、新しい厳密に小さい値へ着地するので、それ自体が
  `CoverageStep` になり得る
- `CoverageStep` は、より大きい親値への移送、および高い中間目標から
  低い固定目標への移送が可能

この簡約によって、高商一段借りの減算側もblockerなしで扱えるようになりました。

### 6. 負エポック主定理

負領域側の主結論は `negative_epoch_undershoot_or_coverage` です。

```text
m≤n+1,
CoordinatesAt n q r,
G(q,r)<0
```

なら、ある `t` が

```text
n≤t≤n+⌊r/2⌋
```

を満たし、その実遷移の着地点について次のどちらかが成立します。

```text
0≤G'<m
```

または

```text
CoverageStep m (aₙ,n)
```

つまり負領域からの未処理部分は、もはや

- 多段借り
- 一段借りの高商加算
- 一段借りの高商減算
- 途中のゼロ借用加算

ではありません。それらは全て有限時間の値下降証明へ吸収されました。
残るのは、固定目標 `m` より小さい有限幅の非負ポテンシャル帯
`0≤G<m` へのアンダーシュートだけです。

### 7. 非負アンダーシュート・エポック

今回、`0≤G<m` の内部力学も有限化しました。非負性から

```text
U(q)≤r, したがって q≤r
```

なので、状態は必ず通常領域にあります。

- 合法減算は `G` を保存し、商を `q→q-1` と下げる
- `q≥2` で加算を強制された場合、既出の減算候補は `n+1` 以上なので
  `CoverageStep m` になる
- したがって高々 `q` 歩で、CoverageStepまたは低商 `q≤1` に到達する
- `q=0,1` からは高々2歩で `G` が厳密に下がる

これを統合した `undershoot_epoch_trichotomy` は、

```text
0≤G<m
```

から高々 `q+2` 歩で次のいずれかを与えます。

```text
CoverageStep m (aₙ,n)
G'<0
0≤G'<G<m
```

さらに非負レベル `G` に関する強帰納法により、
`undershoot_eventually_negative_or_localCoverage` を証明しました。つまり
アンダーシュート帯は軌道を永久には閉じ込めず、最終的に負領域へ戻るか、
後続状態で局所的なCoverageStepを生成します。

ただし、低商で `G` を下げる遷移は実値 `aₙ` を必ず増加させ、その増加は

```text
aₜ=aₙ+1 または aₜ=aₙ+(n+1)
```

の二つに限られることも同時に証明されました。したがって、後続状態のCoverageStepを元の
初出値へ単純な値帰納で戻すことはできません。

一方、その低商状態の旧レベル値 `g=G` は、遅くとも次時刻までに必ず履歴へ
記録されます。商0では現在値そのものであり、商1では合法減算の着地点または
加算を強制した既出候補です。さらにポテンシャル降下量は厳密に `1` または `3`
です。これで経験的に見えていた `Z→Z-3` 型履歴梯子の最初の一般補題が得られました。
通常減算区間まで含めても、CoverageStepが先に得られない限り、開始レベル `g`
全体が高々 `q+1` 歩で履歴へ入ることを
`nonnegative_epoch_records_level_or_coverage` として証明しています。

`negative_undershoot_cycle_coverage_or_parentGrowth` はこの残余を、

```text
元のCoverageStep
```

または

```text
後の負状態／局所CoverageStep かつ aₙ≤aₜ
```

という形に縮約します。現在の本質的障害はアンダーシュート帯そのものではなく、
ポテンシャル降下と親値上昇の交換を履歴情報で破ることです。

### 8. 履歴予算と三成分ランク

値 0,…,m-1 のうち時刻 n までに未出現の個数を
`missingBelowCount m n` と定義しました。履歴の成長に対して単調非増加で、
`g<m` の真の初出が起きると厳密に下がります。

blockerの初出時刻と前向き探索の履歴時刻を混同しないため、探索状態を
`(horizon, activeParent, orbitValue)` に分離し、

```text
(missingBelowCount(m,horizon), activeParent, orbitValue)
```

という辞書式ランクを導入しました。このランクはwell-foundedです。

- 新しい target-smaller 値の出現は第1成分を下げる
- blockerは履歴地平を保ったまま activeParent を下げる
- 局所的な加算→減算は orbitValue を下げる

という三種類の進捗を別成分で受け止めます。全ノードでこのランクを下げる
`HistorySearchOracle` が構成できれば目標出現が従うこともLeanで証明済みです。

### 9. 非負・負エポックの履歴ランク接続

`3≤g<m` の `q=1,G=g` 状態では、高々2歩でCoverageStep、未回収値数の
厳密下降、または軌道値の厳密下降が起きます。通常減算区間の前へ持ち上げた
`nonnegative_epoch_historySearchOutcome` も証明済みです。境界例外 `q=0` は、
負領域から後で到着した場合には合法減算の新しい着地点なので第1成分へ吸収されます。

また、任意の強制加算の直後に減算できれば

```text
a(n+2)+1=a(n)
```

であり、できなければ `a(n)-1` が既出blockerです。実軌道の `q≥2` では
`m≤n+1` から常に `m≤a(n)-1` なので、強制加算の値増加は高々1追加ステップで
ランク下降へ変換できます。

負エポックについては、一段借り直前の値が開始値以下であることと、最終分岐が
加算か減算かを保持する強化定理を証明しました。三成分ランクと統合すると、
未処理分岐は厳密に次の一点へ縮約されます。

```text
q=1, r=0, G=-1, a(t)=t
forced addition into q=1, G=t-1
target m=t+1
```

すなわち残る局所履歴命題は

```text
DiagonalSuccessorProperty:
  0<t and a(t)=t  implies  t+1 occurs
```

です。これを仮定すると負エポック全体が目標出現または三成分ランクの厳密下降へ
変換されることを `negative_epoch_historySearchOutcome` として証明しています。

さらに `a(t)=t` を逆向きに解析し、末尾の連続減算を極大まで延長しました。
その鎖の開始時刻を `s`、長さを `L≥2` とすると、直前では加算が強制され、
既出候補 `y` が

```text
t+1 ≤ y < a(s),    first(y) < s < t,
y + 2s = a(s)
```

を満たします。したがって対角状態ごとに、`t+1` の実出現または、より早い
初出時刻を持つ具体的な blocker／`CoverageStep` が無仮定で得られます。

この交換を循環なく扱うため、通常／対角負債の二位相を持つ四成分ランク

```text
(missingBelowCount(m,horizon), anchorParent, phase, localMeasure)
```

も導入しました。通常から負債への入口では `phase: 1→0`、負債中は
`localMeasure=first(y)`、通常への出口では `anchorParent` の厳密下降を使います。
この順序のwell-founded性と、全ノードを進める `PhaseSearchOracle` から目標出現が
従うことはLeanで証明済みです。対角二分法も、このランクへの入口へ接続済みです。

## 着地面とCoverageStep

借用回数 `b`、着地商 `k`、目標 `m` の共通逆像は

```text
b(n+1)+r = q+U(k)+m
```

です。

- 加算商条件: `q+1=b+k`
- 減算商条件: `q=b+k+1`
- 加算で `k≥2` へ着地した場合、阻害候補が直接blocker枝を与える
- 加算で `k=0,1` なら目標値は無条件に実出現する
- 合法な減算で `G=m` へ着地した場合、着地点そのものが新しい小さい値である

このため、実際の加算・減算が目標面 `G=m` に入るなら、遷移前が初出であるという
仮定なしに `CoverageStep m` を構成できます。

一方、単に `q=2,G=m` にいるだけではexact gateのfreshnessは保証されません。
`n=18` では `(q,r,G)=(2,7,4)` ですが、中間値24が既出なので次は加算です。
この反例も `Recaman.Examples` でカーネル検証しています。

## 既存の大域証明骨格

`CoverageOracle m` は、任意の初出値 `v≥m` から

1. `m` の実出現、または
2. `m≤y<v` を満たす別の初出値 `y`

を返す局所証明器です。値 `v` に対する強帰納法により、

```text
(∀m>0, CoverageOracle m)  ⇒  ∀m, ∃t, a(t)=m
```

をLeanで証明済みです。

直接の三角数方程式だけを要求する `TargetResolvable` は強すぎ、
`m=1,v=3,f=2` で偽です。そのため、直接下降だけでなく、
blocker、借り遷移、exact gate、局所脱出を同じ `CoverageStep`
インターフェースで組み合わせています。

## 非形式的な計算実験

以下はLean証明ではなく、次の仮説を選ぶための計算結果です。

標準Recamán列を10億項まで厳密計算した範囲では、

- 一段借りイベントは35回
- 加算12回、減算23回
- 全35回が最初の一段借りで非負へ回復
- 着地商は `0,1,2,3` のみ
- 負エポック長は最大3
- 多段借りは0回

でした。ただし「高商一段借りが観測されない」こと自体は強い証拠ではありません。
一様余りモデルでも `q≥6` の一段借り期待回数は10億項まで合計約0.022回です。
合同類にも明確な禁止則は見つかっていません。

経験的に有望なのは合同条件より履歴条件です。負エポック入口を阻害した候補を
`Z` とすると、観測された短いエポックでは `Z`、`Z-3`、
`Z+(t-2)` の既出・未出パターンが分岐を制御しています。これは次の探索候補ですが、
現時点では定理ではありません。再現用C++コードと実行方法は `experiments/` に
収録しています。

## 重要な未証明部分

本プロジェクトは、次をまだ主張しません。

1. ordinary normal nodeを現在軌道または生成元provenanceと整合するdomainへ精密化する。
2. 精密化したconstructorを全normal分岐で保存し、
   `SemanticPhaseSearchOracle`を追加仮定なしで構成する。
3. 全ての正整数 `m` について `CoverageOracle m` を構成できる。
4. レカマン数列が全ての非負整数を含む。

したがって、全射性証明はまだ完成していません。ただしcanonical開始点の全符号・
低level分岐は既存のwell-foundedランクへ接続されました。残る障害は局所力学ではなく、
ordinary normal証明書が現在horizonの値・座標・時刻条件を保持しないdomain設計上の問題です。

## 次の証明エポック

次の主対象は、ordinary normal domainのprovenance付き再設計です。有望な順に、

1. current-state用の`OrbitReadyNormalCertificate`をconstructorへ昇格する。
2. parent-drop、coverage、frontierが作るhistorical childを生成元別に分類する。
3. 各constructorのlocal oracleとdomain保存を証明する。
4. 精密domain上の`SemanticPhaseSearchOracle`へ統合する。

既存の四成分位相ランクは維持でき、canonical低levelの強制成長にも新しいrankは不要でした。
二段先のcandidateが元値より下がることを使えばCoverageStepへ戻せます。

## ファイル構成

- `Recaman/Basic.lean` — 数列、状態、履歴リスト
- `Recaman/Coordinates.lean` — 三角座標、符号付きポテンシャル
- `Recaman/CoordinateDynamics.lean` — 通常・一段借りの局所遷移
- `Recaman/MultiBorrow.lean` — 一般借用証明書と全域遷移
- `Recaman/OrbitBounds.lean` — `aₙ≤U(n)`、`2q≤n+1`、実多段借り排除
- `Recaman/Gate.lean` — 二段exact gate
- `Recaman/Blocker.lean` — blockerの値・初出時刻二重降下
- `Recaman/History.lean` — 保存履歴と実軌道の同値
- `Recaman/HistoryBudget.lean` — 未回収値数、三成分ランク、抽象探索帰納
- `Recaman/ActualDescent.lean` — 実下降、後方極大延長、blocker証明書
- `Recaman/TargetDescent.lean` — 目標下降の成功／blocker二分法
- `Recaman/Coverage.lean` — 値帰納とCoverageOracle
- `Recaman/Mechanisms.lean` — 局所機構のCoverageStep接続
- `Recaman/LandingSurfaces.lean` — 借り着地面の逆像
- `Recaman/PrestateCoverage.lean` — 着地前状態からblocker／CoverageStep
- `Recaman/NegativeRegion.lean` — 一般多段借り算術
- `Recaman/Recovery.lean` — ゼロ借用区間と一段借り到達
- `Recaman/RecoveryBudget.lean` — 一段借り欠損、回復予算、目標時計
- `Recaman/RecoveryFrontier.lean` — 低商回復、高商blocker
- `Recaman/RecoveryWindows.lean` — `k=2,3` の短い時刻窓
- `Recaman/OneBorrowFrontier.lean` — 一段借り到達時の商・増加前線
- `Recaman/NegativeEpoch.lean` — アンダーシュート／CoverageStep主定理
- `Recaman/Undershoot.lean` — 非負帯の有限降下、符号サイクル、親値増加前線
- `Recaman/HistoryFrontier.lean` — 履歴ランクへの負・非負エポック接続
- `Recaman/Diagonal.lean` — 対角状態、極大後方鎖、早期blockerの抽出
- `Recaman/PhaseSearch.lean` — 対角負債を吸収する四成分位相ランク
- `Recaman/DebtAddition.lean` — 強制加算理由と早期候補の抽出
- `Recaman/DebtSubtraction.lean` — 合法減算直前値と初出時刻下降
- `Recaman/DebtInvariant.lean` — debt意味的不変条件と最終遷移分類
- `Recaman/DebtCrossing.lean` — 目標またぎ分岐の可能・不可能結果
- `Recaman/DebtStep.lean` — debt局所分岐の完全な結果型
- `Recaman/DebtBackward.lean` — 合法減算の極大後方延長とanchor境界
- `Recaman/AnchorBoundary.lean` — anchor等号境界の局所形とnormal退出
- `Recaman/CrossingRecovery.lean` — strict crossingの符号・エポック接続
- `Recaman/CrossingGap.lean` — crossing後の有限clock catch-upと全符号epoch前線
- `Recaman/CrossingGrowth.lean` — catch-up成長枝の最強三分岐と実在obstruction
- `Recaman/CrossingHorizon.lean` — horizon前進時のbudget／anchor rank境界
- `Recaman/CrossingIteration.lean` — 同時成長の反復残余と実軌道例
- `Recaman/CrossingFrontier.lean` — frontier符号分類とsemantic閉包
- `Recaman/PhaseEpoch.lean` — 負エポックから四成分位相ランクへの接続
- `Recaman/PhaseProgress.lean` — 四成分位相進捗の推移律
- `Recaman/InitialRegion.lean` — 可変目標に一様なエポック適用領域への入口
- `Recaman/PhaseSearchStart.lean` — canonical開始点とrestricted oracle
- `Recaman/NormalPhase.lean` — 負normal不変条件と保存失敗の完全分類
- `Recaman/PhaseSemantic.lean` — 認証済み探索nodeを統合する意味的domain
- `Recaman/NormalClosure.lean` — parent-drop／forward-exitのsemantic閉包
- `Recaman/BoundaryAudit.lean` — horizon輸送、横断予算、反例の境界監査
- `Recaman/NormalComplete.lean` — 負normal全分岐の無条件semantic step
- `Recaman/NormalSemanticBoundary.lean` — weak normal証明書の反例とorbit-ready境界
- `Recaman/NonnegativeSemantic.lean` — 非負normal通常域のsemantic閉包
- `Recaman/CanonicalOracle.lean` — canonical全符号分類と低level残余
- `Recaman/CanonicalLevelZero.lean` — level 0とsuccessor residualの閉包
- `Recaman/CanonicalLevelOne.lean` — level 1分岐とforced q=1残余
- `Recaman/CanonicalLevelTwo.lean` — level 2分岐とforced growth状態
- `Recaman/CanonicalComplete.lean` — 低level分類の統合
- `Recaman/CanonicalForcedGrowth.lean` — forced growth共通形と二段回収
- `Recaman/CanonicalGrowthRecovery.lean` — canonical開始点の完全な局所step
- `Recaman/NormalProvenance.lean` — current／historical normalのprovenance-aware domain
- `Recaman/OrbitReadyComplete.lean` — orbit-ready current normalの全符号局所step
- `Recaman/ExtendedHistoryNormal.lean` — representative time／history horizon分離と輸送残余
- `Recaman/TypedNormalProvenance.lean` — historical normalの5種類のtyped生成元
- `Recaman/OrbitReadyAdapters.lean` — current normal生成枝のrefined adapter
- `Recaman/CoverageDebtBridge.lean` — Coverage blockerのfuture current／earlier debt分解
- `Recaman/DowncrossBudgetGap.lean` — downcross endpointからのcrossing recovery閉包
- `Recaman/EarlyRepresentative.lean` — early representativeの次遷移分類
- `Recaman/EarlyRepresentativeClosure.lean` — legal downcross残余の閉包
- `Recaman/EarlyForcedCandidateClosure.lean` — forced below-candidate残余の閉包
- `Recaman/EarlyRepresentativeComplete.lean` — early representative全域step
- `Recaman/ExtendedHistoryBudgetClosure.lean` — strict budget gapからの新規below-target抽出と閉包
- `Recaman/ExtendedHistoryComplete.lean` — extended-history normal全域step
- `Recaman/HistoricalDebtBridge.lean` — parent-drop／debt／crossingのcurrent/debt精密化
- `Recaman/ReadyDebtInvariant.lean` — horizon-ready strong debt
- `Recaman/ReadyCurrentDebt.lean` — ready current/debt domain保存step
- `Recaman/OrbitReadyRefinedStep.lean` — refined semantic childとclock残余
- `Recaman/Examples.lean` — 小さい実例とfreshness反例
- `Recaman/Oracle.lean` — `+---` 局所脱出族
- `Recaman/Audit.lean` — 主要定理の公理依存監査
- `experiments/` — 10億項探索に用いた再現用C++コード（Lean証明とは分離）

`#print axioms` では、一部の証明がLean標準基礎の `propext`、
`Quot.sound`、`Classical.choice` に依存します。`sorryAx`、
ネイティブ評価公理、ユーザー追加公理への依存はありません。

## 2026-08-28 — 対角負債の並列分岐調査

対角負債の局所二分法を、最終遷移分類、合法減算、強制加算、計算実験の
四テーマに分けて並列調査した。

### Leanで得られた結果

- `DebtInvariant`として、目標下界、初出証明、horizon以前の初出時刻、
  anchorによる値上界をまとめた。
- `FirstAt a y fy`の最終遷移を、時刻0、合法減算、強制加算へ完全分類した。
- 合法減算で初出した値から、直前値とそのより早い初出時刻を無条件に抽出した。
  これによりdebtの時刻成分は厳密に下降する。
- 強制加算を、非正の減算候補と正の既出候補へ完全分類した。後者から候補の
  `FirstAt`と厳密に早い初出時刻を抽出した。
- 対角極大下降末尾から、意味的不変条件を持つdebtノードへ入る補題を得た。

### 判明した境界

合法減算の直前値は元のdebt値より大きいため、固定anchor未満に残ることは
自動ではない。強制加算の既出候補についても、目標以上または任意のanchor未満
という境界は強制加算だけからは従わない。`a 5 = 7`から`a 6 = 13`への実遷移を
使い、目標下界とanchor上界が自動でない具体例をLeanカーネルで確認した。

したがって次の核心は、候補が目標未満へ落ちる場合を履歴予算低下へ変換すること、
または合法減算の直前値を固定anchor内に保つ追加不変条件を得ることである。

### 計算実験

`recaman_debt_history.cpp`を追加し、対角状態、極大減算末尾、blockerの初出分岐を
正確な履歴bitsetで追跡できるようにした。10億項までの実行では正の対角状態は
時刻`1`、`1520`、`9317`、`31221`の4件だった。後三件は直前の減算列が一段だけで、
後続目標値はすでに出現していた。二段以上の末尾を持つdebt対象イベントは0件だった。
これは補題選択の経験的材料であり、Lean証明の仮定には使用しない。

### 第二ラウンドの縮約

合法減算を初出時刻から後方へ極大延長した。減算尾が2段以上なら、開始直前の
強制加算から`y+3`以上のblockerを抽出できるため、目標下界を保ったまま初出時刻を
下げられる。尾が1段なら直前値は正確に`y+1`であり、`y+1<anchor`ならnormalへ
戻れる。したがって残る合法減算境界は`anchor=y+1`だけである。この等号は実軌道
`a 2=3`, `a 3=6`, `a 4=2`で実現する。

強制加算が`a n < target < a (n+1)`と目標をまたぐ場合も分離した。形式的なanchor
ランク下降は得られるが、child値が目標未満となり意味的不変条件を失う。この分岐では
目標方程式、目標面、exact gate、`missingBelowCount`下降が自動でないことをLeanで
証明した。step 3の`3→6`がtarget 4をまたぐ具体反例となる。

以上を`debtStep_classify`へまとめ、未解決部分をcrossingとanchor等号境界として
明示した。早い初出候補は固定horizonですでに履歴に含まれるため、それ自体から履歴
予算下降を得ることも不可能である。

### 第三ラウンドの統合

長さ1の`anchor=y+1`境界は、既出のpredecessorではなく初出landing`y`自身をnormal
childに選べばanchorが厳密に下がる。このため等号境界は閉じた。加えて、強い
`DebtInvariant`を持つnodeは常に自身の値でnormalへ退出できることを明示した。

strict crossingは専用の`CrossingRecoveryInvariant`として表現した。post-stateの
ポテンシャルは必ずtarget未満であり、負または非負undershootのどちらも実例がある。
既存エポック定理は`target≤time+1`なら適用できるが、対角由来のcrossingではこの条件が
必ず成立しない。したがって次の研究対象は、絶対時刻条件をcrossing gapなどの相対量へ
置き換えることである。

三成分履歴ランクをnormal位相の四成分ランクへ埋め込み、q=1例外をdebtへのrank下降へ
変換した。`negative_epoch_phaseSearchOutcome`は`DiagonalSuccessorProperty`なしで負エポック
全体を目標出現または位相進捗へ接続する。

初期領域についてはcanonical nodeと証明書を定義し、意味的domain上だけで動く
`RestrictedPhaseSearchOracle`を構成した。これにより全tuple上のoracleではなく、実際に
到達可能で不変条件を保存するnodeだけを対象にwell-founded探索を開始できる。

### 第四ラウンドの意味的統合

strict crossing後は時刻`target-1`または`target`まで有限前進することで、既存epoch APIの
絶対時刻条件へ必ず入れることを示した。catch-up地点のpotentialは負、undershoot、
target以上の非負領域の全てを既存定理へ接続した。相対crossing gapだけでは絶対時刻条件を
導けない実軌道反例も形式化したため、残る本質はclockではなく、前進中の値／anchor成長である。

負potentialのnormal nodeには`NormalPhaseInvariant`を導入し、負エポック結果を、目標出現、
意味的不変条件を保存するnormal/debt child、または保存できない理由を保持するobstructionへ
分類した。parent-dropとforward-exitではnormal条件の一部が現行APIから得られず、q=1 debtでは
`value < anchorParent`だけが不足し得ることが定理型に現れた。

最後に、canonical start、ordinary normal、strong debt、crossing recoveryを
`PhaseSemanticInvariant`へ統合した。canonical開始、debtの自己normal退出、anchor等号境界、
strict crossingではdomain保存を証明済みである。これにより全域数値tupleではなく、到達可能な
証明付きnodeだけを対象とする`SemanticPhaseSearchOracle`が最終的な局所完了条件になった。

### 第五ラウンドのobstruction精密化

finite catch-upの二つの成長比較を統合し、CoverageStepが得られる枝とanchorが下がる枝は
目標出現または位相進捗へ接続した。唯一残るのはcatch-up値が元のdebt値とanchorの両方以上に
なる枝である。debtからnormalへの同一horizon rank下降はanchor下降と同値であるため、この枝を
自然なnormal childで閉じることは原理的に不可能である。target 5、crossing 3→6、catch-up値7の
実軌道例で完全obstructionが実在することもLean化した。

normal側ではparent-dropを初出anchorのsemantic normal childへ接続した。forward-exitで一度残った
rank同値枝は、目標以上から目標未満への軌道横断が目標出現またはbelow-target履歴予算の厳密下降を
生む一般補題によって排除した。q=1 debt例外も強いnormal不変条件と矛盾する。結果として
`negativeNormal_phaseSemanticStep`は、負normal nodeから目標出現またはdomainを保存する
`PhaseSearchProgress`を追加仮定なしで返す。

### 第六ラウンドのcrossing閉包

同時成長obstructionのepoch frontierを、即時Coverage、後続negative、後続Coverageへ分解した。
frontierの初出値が旧anchor未満なら、実際の初出時刻までhorizonを拡張したsemantic normal childを
構成できる。horizon前進時のdebt-to-normal rankは、budget厳密下降、またはbudget不変かつ
anchor厳密下降と同値であることも証明した。

一方、target 5ではcatch-up値7の次に値13・負potentialへ進み、budgetもanchorも下がらない。
したがって同時成長の反復自体は実在する。それでもこの分岐の入力はstrong `DebtInvariant`を
保持しており、frontier下降が得られない残余ではdebt値自身へのsemantic self-exitを選べる。
`crossingGrowthObstruction_phaseSemanticStep`により、最終的に目標出現またはdomain保存rank下降へ
無条件で接続した。

### 第七ラウンドのcanonical閉包とdomain監査

canonical開始点をpotentialの負・目標以上・通常非負undershoot・低levelへ完全分類した。
非負通常域`3≤potential<target`は既存のhistory frontierからsemantic childへ輸送し、
残余をlevel 0/1/2だけに限定した。level 0は二段以内の目標出現へ閉じ、level 1/2の
合法減算と高quotient強制加算もCoverageStepへ接続した。

quotient-oneで強制加算されるlevel 1/2は、直後に値とanchorが増え、below-target budgetが
不変なので、元canonical parentからの即時`PhaseSearchProgress`にならない。target 5の実軌道で
この境界を検証した。一方、その次の減算候補は`n+level`で、元値`n+1+level`より1小さい。
合法ならfresh、blockedなら既出なので、どちらもCoverageStepとなる。この二段lookaheadにより
新phaseを追加せず`targetStartInvariant_phaseSemanticStep`を得た。

並行してordinary `NormalSearchInvariant`を監査した。この証明書は過去の初出値を後のhorizonへ
自由に載せられるため、nodeのlocal valueが`a horizon`であることも`target≤horizon+1`も従わない。
反例をLean化し、現在軌道に整合する`OrbitReadyNormalCertificate`を定義した。次のボトルネックは、
既存のhistorical normal childを生成元provenanceごとに保持する精密domainの構成である。

### 第八ラウンドのorbit-ready totalityとprovenance監査

`OrbitReadyNormalCertificate`が表すcurrent-state normalについて、potentialの全符号を分類した。
負領域は既存のnegative normal closureへ、高potentialの正商はCoverageStepへ接続した。商0の
高potentialは強制加算後の低商候補を、商1の低level強制加算は二段先の候補を使って閉じた。
これによりlevel 0/1/2を含む`OrbitReadyNormalInvariant.phaseSemanticStep`を残余なしで得た。

同時に、currentとhistoricalを混同しない`ProvenancedNormalInvariant`を導入した。horizon/value
mismatch例はcurrent constructorに入れず、rank edge付きのhistorical provenanceを要求する。
既存24箇所のnormal semantic生成を監査した結果、8箇所はorbit-readyへ直接移行できる一方、
残りはparent-drop、coverage anchor、downcross restart、debt exit、crossing frontierに分類される。

generic provenance chainはdomain admissionとしては安全だが、historical childのsuccessorを単独では
与えない。次の核心は、history horizonとanchorを実際に表すrepresentative timeを分離した
extended-history local step、および生成機構別のtyped constructorである。

### 第九ラウンドのextended-history境界とCoverage/debt迂回

historical normalについてrepresentative time、history horizon、first time、代表時刻座標を分離した。
representative timeがtime-readyで、そこからhistory horizonまでbelow-target履歴予算が不変なら、
完成済みorbit-ready stepをそのまま輸送できる。一方、representative readinessの失敗とbudget gapは
独立であり、両方の具体例をLean化した。budget gapではhistorical nodeがrepresentative nodeより
既にrank下位にあるため、代表状態からの局所下降を単純合成できない。

parent-drop、coverage anchor、downcross restart、debt exit、crossing frontierをそれぞれtyped
provenanceとして実装し、共通extended-history residualへ接続した。current生成8系統には
orbit-ready adapterを追加し、既存APIで失われていた条件が`target≤time+1`だけであることも明示した。

さらにcurrent親のCoverageStepはhistorical normalを経由する必要がない。candidateが親より後で
初出ならorbit-ready current child、親より前なら同じhorizon／anchorのstrong debt childとなる。
`coverageStep_currentOrDebt`によりこの分解を完全に証明した。残る中心はdowncross restartが必ず持つ
budget-gap residualと、debt／crossing sourceで不足し得るhorizon readinessである。

### 第十ラウンドのextended-history完全閉包とrefined clock監査

downcross budget gapは、below-target endpointから将来のweak upcrossingを取り、その直前値を
anchorにしたcrossing recoveryへ接続した。直前値はtarget未満、旧representative値はtarget以上なので、
既存四成分rankのanchorが厳密に下がる。新しいphaseやrank成分は不要だった。

early representativeを次遷移で分類すると、合法減算downcrossと、強制加算を起こした既出の
below-target candidateの二残余だけになる。前者は直後のbelow-target値、後者はcandidateの過去の
実出現から、それぞれrepresentative値までのupcrossingを構成できる。recovery horizonを
`max oldHorizon (crossingTime+2)`とすることで履歴予算を悪化させず、両残余を閉じた。

さらにstrict history-budget dropの定義を逆向きに解析し、representative historyでは未出だが
later horizonまでに出現した`g<target`を抽出した。この一般補題により、downcross provenance固有の
endpointがなくてもgeneric budget gapを同じcrossing recoveryへ送れる。結果として
`ExtendedHistoryNormalCertificate.phaseSemanticStep`はhorizon-readyな任意のextended-history normalを
残余なしで閉じる。

historical normalの回避も進めた。current parent-dropはfirst occurrenceを比較し、futureなら
orbit-ready current、earlierならstrong debtへ送れる。debtの通常局所解析ではhistorical self-exitを
earlier debt継続に置き換えた。crossing frontierだけはdebt timeとhistory horizonの間の二時計区間を
明示的に残すが、この中間残余は実軌道target 5にも存在する。

debt側には`ReadyDebtInvariant`を導入し、`target≤horizon+1`をproof dataとして保持した。Coverageの
current親からは親のtime readinessをdebt childへ伝搬できる一方、既存child certificate単独では
この条件が従わない反例も形式化した。ready current/debt、extended-history normal、crossing recoveryを
統合するrefined child domainを作り、broad semantic childを精密化した結果、残る情報不足は
normal/debt childのhorizon readinessだけになった。

次のクリティカルパスは、black-box semantic resultを事後精密化するのではなく、orbit-ready局所定理の
各生成分岐からrefined resultを直接返すことである。その後、ready debt obstructionとcrossing frontierを
統合し、restricted well-founded oracleへ接続する。

### 第十一ラウンドのdirect refinementとcrossing oracle境界

orbit-ready normalの全生成分岐をbroad semantic constructorへ変換する前に監査し、parent-drop、forward
above、downcross、Coverage、低levelの各childへclock証明を直接伝搬した。
`OrbitReadyNormalInvariant.refinedStep`は`normal_horizon_not_ready`／`debt_horizon_not_ready`をreachable
resultから除去し、目標出現またはrefined domain保存stepを返す。

ready debtではforced additionの二obstructionを専用crossing recoveryへ直接送り、合法減算が固定anchorへ
達する枝だけをhorizon-ready extended-historyへ退出させた。この枝は`firstTime=debtTime<horizon`という
二時計middle境界なので、future currentまたはearlier debtには分解できない。crossing frontierのmiddle
residualもsource debtのhorizon readinessを継承する同じtyped childへ閉じた。

extended-history側では、任意のactual below-target stateからfuture weak upcrossingを取り、拡張horizonと
低いpre-crossing anchorを持つcrossing childへ移す共通refined adapterを構成した。これによりstableな
representativeはdirect orbit-ready stepを輸送し、early／budget-gapはcrossingへ進む完全refined stepを得た。

最後にrefined domainのconstructorを完全監査した。orbit-ready current、ready debt、extended-historyは
無条件に閉じ、残るのは`CrossingSearchInvariant`自身だけである。
`crossingRefinedStepHypothesis_implies_occurs`は、この単一typed obligationからcanonical startの目標出現を
導く。現行crossing certificateはstrict crossingへの入口を保持する一方、元strong debtのpost-state
`FirstAt`、post値と旧anchorの比較、horizon readinessを保持しない。このproof-data消失が次の研究対象である。

### 第十二ラウンドのcrossing rank境界

refined経路で実際にcrossingを生成する中心はready debt forced additionとextended-historyからのfuture
upcrossingである。source provenanceの不足に加え、crossing nodeそのもののrank形を監査した。

crossing nodeのnumeric anchorはstrict crossing直前の値なのでtarget未満である。一方、orbit-ready
currentとextended-historyのanchorはtarget以上であり、ready debtのanchorはtarget以上のdebt値より
さらに大きい。したがってcrossingから非crossing refined childへ進むとき、anchor／phase／localの
成分ではrankを下げられない。`crossing_to_nonCrossing_progress_forces_budgetDrop`は、そのようなedgeが
必ず`missingBelowCount`のstrict dropを伴うことを証明する。

この結果、任意のrefined successorは「strict budget drop」または「再びcrossing」の二択になる。
同じhistory horizonなら前者は不可能なのでsuccessorはcrossingに限られる。次の局所totalityには、
source certificateの補強だけでなく、新しいbelow-target occurrenceを生むこと、またはcrossing間で
下降する有限量を見つけることが必要である。

### 第十三ラウンドのfuture-downcross閉包

reachable producerが保持できる`target≤horizon+1`をcrossing certificateに追加した
`ReadyCrossingSearchInvariant`を導入した。保存horizon以後に`target≤a t`から
`a (t+1)<target`へdowncrossするstepがあれば、forced additionは値を増やすため不可能であり、
そのstepはlegal subtractionである。したがってendpointは`valuesThrough t`に未出で、保存horizonの
履歴にも未出である。

`FutureDowncrossStep.strict_budget_drop`はこのfresh endpointから親horizonに対するstrict budget dropを
証明する。元crossingのpost-addition stateはtarget以上で座標も保持されているため、これを
representativeとし、downcross endpoint時刻を新horizonにしたextended-history childを構成できる。
`ReadyCrossingSearchInvariant.refinedStep_of_futureDowncross`が目標等号とこの退出を統合する。

残る領域は、保存horizon時点ですでにbelow-targetである場合と、保存horizon以後にdowncrossが存在しない
場合である。前者では次のupcrossingを構成できるが、旧pre-crossing anchorより下がるとは限らない。
後者はabove-target側の長期挙動を追加解析する必要がある。

### 第十四ラウンド：horizon-below crossingの完全分類

`crossingNumeric_progress_iff_budgetDrop_or_anchorDrop`を追加し、crossing数値ノード間の四成分rankを
完全に逆解析した。phaseとlocal measureはnormal crossingではanchorによって既に固定されるため、
進捗条件はstrict history-budget dropまたはstrict anchor dropの二つだけである。

horizonの実軌道値がbelow-targetなready crossingでは、clock readinessから次のweak upcrossingが必ず存在する。
`refinedStep_or_continuationGrowth_of_horizonBelow`は、目標出現、refined crossing進捗、または
`CrossingContinuationGrowthResidual`の三分類を証明する。残余はbudget stable、anchor nondecreasing、
かつ`PhaseSearchProgress`の否定をすべて保持する。

この残余はtarget 19の実軌道上に実在する。time 6の13→20 crossingに対しhorizon 31を保存すると
`a 31 = 14 < 19`であり、次の14→46 crossingはbudgetを下げずanchorを13→14へ増やす。
`crossingContinuationGrowth_actual_example`がこれを計算実験ではなくLeanカーネル上の定理として検証する。

### 第十五ラウンド：above-target tailへの縮約

growth残余のchild horizonがbelow-targetなら、直前のabove endpointからのdowncross endpointがfreshな
below-target値となりbudget stableに矛盾する。これにより残余childは必ずat-or-above targetに戻る。
その後のdowncrossはchild budgetをstrictに下げ、childと元parentのbudgetは同じなので、中間の
anchor growthを迂回した直接rank edgeを元parentへ作れる。

`exists_futureDowncrossStep_between`はabove開始点と後のbelow点の間に隣接downcrossが存在すること、
`no_futureDowncross_iff_tail_atOrAbove`はdowncross不在が以後のpermanent above-target tailと同値であることを
証明する。`TargetTailReturnHypothesis`をこの長期再帰境界として切り出し、
`ReadyCrossingSearchInvariant.refinedStep_of_targetTailReturn`で、これがready crossingの全局所分岐を閉じることを証明した。

したがって次の無条件証明対象は、crossing直後の局所力学ではなく、目標未出のまま軌道が
ある有限開始点以降ずっとtarget以上に留まる可能性を排除する長期命題である。

この命題が元の予想とどの程度独立かも監査した。`LeastMissingTarget`を導入し、それ未満の
個々の出現時刻を有限の一つのhistory horizonに集約できることを証明した。このhorizon以後の
below-target endpointは既出である一方、downcrossならlegal subtractionにfreshでなければならず矛盾する。
`LeastMissingTarget.eventually_strictlyAbove`は、最小未出目標があれば軌道が最終的に常にそれより大きくなることを示す。
さらに`all_targetTailReturn_iff_surjective`で、全targetのtail returnはRecamán全射性予想そのもと同値と証明した。
よってtail returnを新しい局所仮定として採用しても未解決性は減らない。

### 第十六ラウンド：permanent tailのzero-budget境界と最小値blocker

`PermanentAboveTail`を追加し、strictly-above tailの各状態から高々二遷移で`CoverageStep`を
抽出した。最初の減算が合法なら即時に値が下がる。forced additionなら次の減算候補は厳密に
`a n - 1`であり、合法ならfreshな初出、blockedなら過去の初出を取り出せる。

自然数値を取る無限tailが最小値を持つことを強帰納法で証明した。tail最小値では合法減算は
最小性に反するため最初のstepがforced additionとなる。その次の候補`a n - 1`への合法減算も
同じ理由で不可能なので二回目もforced additionである。候補は正で既出であり、その最初の出現が
tail内なら最小値未満になって矛盾する。したがって初出時刻はtail開始前、値はtargetより大きい。

below-target値がすべて既出なら`missingBelowCount=0`であることも帰納法で証明した。初期値0から
tailまでの有限upcrossingを選び、horizonをtail内かつtarget-readyまで進めることで、budget 0・
future downcrossなしの`PermanentTailCrossingCertificate`を構成した。crossingからnoncrossingへの
rank edgeはstrict budget dropを要求するため、この証明書では不可能である。refined子があれば
crossingに留まり、budget 0を保ち、pre-crossing anchorを厳密に下げる。

`PermanentAbovePotential`では二連続forced additionを既存potentialの下降量にする案を監査した。
実軌道の`2→7→13`ではpotentialが`2→-2`へ下がる一方、重なる`7→13→20`では`1→3`へ上がる。
両例を`decide`でkernel検証し、二連続forced additionだけではpotentialの方向が定まらないことを
定理`doubleForced_potential_has_both_directions`として固定した。

次の証明対象は、tail最小値が返すhistorical predecessorの初出時刻からcrossing列を復元し、
zero-budget crossing parentより小さいpre-crossing anchorを構成することである。

### 第十七ラウンド：historical predecessor反復の有限化と停留residual

below-target履歴被覆を必要としない`MissingStrictAboveTail`を分離し、tail最小値定理をこのcoreへ一般化した。
最小値直下のhistorical first occurrence以後を分類すると、future downcrossがある場合はそのendpointが
legal subtractionによる`FirstAt`となり、`missingBelowCount`を厳密に下げる。downcrossがない場合は
`no_futureDowncross_iff_tail_atOrAbove`とtarget missingから、そのfirst occurrenceを開始点とする新しい
strict-above tailが得られ、その最小値は旧最小値より厳密に小さい。

`HistoricalPredecessorOutcome`はこのbudget-drop／renewed-tail二分法を保持する。renewed-tail側の最小値を
自然数の強帰納法で反復し、`exists_historicalDowncrossCertificate`で有限回後のfresh downcrossを抽出した。
completed-history tailでは出発first occurrenceのbudgetが正、最終tail horizonのbudgetが0であることも示した。

次にdowncross endpointから旧tailまでの有限区間でstrict upcrossingを再構成し、combined crossingと同じ
zero-budget horizonへ載せた。anchorが下がれば`PhaseSearchProgress`を持つrefined crossing子になる。
下がらない枝を`HistoricalCycleGrowthResidual`として固定した。

最後に、このresidualが証明書の弱さだけではないことを示した。parent crossingを、まさにそのhistorical
downcross後に再構成したupcrossing自身として選べば、再生childはparentと同じnumeric nodeになる。
`exists_stationaryHistoricalCycleResidual`は、任意の仮想permanent tailから同anchor・同budget・no-progressの
停留residualを構成する。したがって次の設計にはcanonical crossing selectionまたはcycle間rankが必要である。

### 第十八ラウンド：canonical upcrossingとone-way cycle rank

`FirstWeakUpcrossingStep`を導入した。既存のfuture upcrossing witnessを上界とし、時刻への強帰納で
より早いwitnessがある限り下げることで、最初のweak upcrossingを標準ライブラリだけで構成した。
最初のwitnessは任意の他witness以下であり、一意である。historical downcross endpointから選んだ最初の
upcrossingは旧strict tail開始前に終わる。しかし同じendpointから二度選べば一意性により同じ時刻なので、
earliest canonicalization単独ではstationary residualを解消しない。

履歴方向を逆に測る`seenBelowCount target horizon := target - missingBelowCount target horizon`を定義した。
seenとmissingの和はtargetで、seen countは履歴とともに単調増加する。missing budgetがstrictに下がると
seen countはstrictに上がるため、zero-budget tail horizonからpositive-missing historical pointへ戻る向きでは
seen countがstrictに下がる。`TailHistoryProgress`はphase／seen／minimumのwell-founded rankとしてこれを確認した。

さらにzero-budget crossing anchorを最外層に加えた`TailCycleProgress`を定義した。四成分は
anchor、`crossing > backtrack > discharge` phase、seen count、tail minimumである。combined certificateは
同anchorのbacktrackへ厳密に入り、renewed-tailはseen/minimum、historical downcrossはphaseを下げる。
辞書式自然数四成分なのでwell-foundedである。

`tailCycle_exitCrossing_iff_anchorDrop`はdischargeからcrossingへ戻る進捗がstrict anchor dropと同値であることを
証明する。同anchor stationary exitは拒否され、従来の`HistoricalCycleGrowthResidual`は新rank上でも
`tailCycleExitObstruction`になる。これでhistorical内部の循環ではなく、exit anchor比較だけが残った。

### 第十九ラウンド：typed discharge returnとcrossing-time cursor

`PermanentTailDischargeReturnCertificate`を導入し、combined permanent-tail obstructionから、有限反復で得た
historical downcross、そのfresh endpoint、endpointから最初のweak upcrossing、親crossingの実時刻を一つの
proof objectへ統合した。canonical returnはhistorical tail開始前、従って親のzero-budget horizonより前に終わる。

親子crossingを`(anchor, crossingTime)`で測る`TailCrossingCursorProgress`を定義した。この辞書式順序は
well-foundedで、strict anchor dropだけでなく、anchor等号かつreturn時刻下降も進捗にする。さらに
`crossing > backtrack > discharge`、seen count、tail minimumを内側に加えた五成分
`TailCursorCycleProgress`を構成し、well-foundednessと、dischargeからcrossingへのexitがcursor下降と
必要十分であることを証明した。

`cycleExit_or_kernelResidual`は非進捗を三constructorへ完全分解する。return anchorが旧anchorより増える場合、
旧crossingがdowncross endpointより前にあってcanonical比較の候補にならない場合、anchorとcrossing時刻が
完全に同一なstationaryの場合である。旧crossingがendpoint以後ならcanonical returnは旧時刻以下なので、
同anchorの非進捗はliteral same timeに限られる。また旧crossing自身が同endpointからcanonicalなら、この
stationary constructorが実際に生じる。したがってtime cursorは非canonicalな等anchor loopを除くが、同じ
canonical crossingの再訪を除くにはvisited情報または別のhistorical choiceがなお必要である。

### 第二十ラウンド：canonical rebaseのstationary no-go

三kernel residualに対する最も自然な操作として、canonical return crossing自体を次の親へrebaseした。
`CanonicalReturnRebaseCertificate`は、return crossingを旧zero-budget horizonへ載せたready crossing、同じ
permanent tailとminimumを持つcombined certificate、同じhistorical downcrossを保持する新discharge certificateを
まとめる。return crossingは親horizonより前で、targetは大域的に未出なので、この再構成は任意の元certificateで可能である。

しかし新discharge certificateではold crossing timeがreturn timeそのもので、anchorも`a returnTime`に一致する。
`exists_rebasedStationaryKernel`はliteral stationary constructorを、`exists_rebase_with_noCycleExit`は対応する
五成分cycle exitの否定を返す。従ってgrowth／chronology mismatchをcanonical rebaseで正規化しても、同じ
endpointを再生する限り必ずstationary coreへ入る。次はparentの数値だけでなく、使用済みendpointまたは
別のhistorical minimumをproof dataとして保持しなければならない。

### 第二十一ラウンド：stationary canonical below corridor

stationary rebaseのfresh downcross endpointから最初のweak upcrossing predecessorまでを
`CanonicalBelowCorridorCertificate`として切り出した。開始点がbelowであり、途中でtarget以上になればより早い
weak upcrossingが存在してcanonicalityに反する。従って閉区間上の全軌道値はtarget未満である。

gap 0ではdowncrossの合法減算と直後のforced additionを展開し、`a (d+2) = a d + 1`というexact valleyを得た。
gap正では最初の内部transitionを二分した。合法減算なら次値はfirst occurrenceで、below-targetなので
`missingBelowCount`を厳密に下げる。forced additionなら次値もbelowであるため、加えるclock自体が
`d+2 < target`を満たす。この二分法を任意の内部transitionへ一般化し、legalならbudget drop、forcedなら
`time+1 < target`を証明した。budget不変なall-addition部分は固定target未満の有限clock領域に閉じ込められる。

### 第二十二ラウンド：all-forced corridorの有限rank

内部legal subtractionを一つも持たない場合を`AllForcedAdditionCorridor`として定義した。delayed corridorの
最後の内部timeにもforced clock boundが適用できるため、`returnTime < target`とgapのtarget-relative上界が従う。

各stepの加算clockを足す`forcedClockSum`を定義し、all-forced runの軌道値が開始値とclock和の和に一致する
telescoping式を帰納法で証明した。従ってrun内の値は厳密増加する。さらに`target - time`を残りclockとする
`CorridorClockProgress`を定義し、自然数順序へのpullbackとしてwell-foundednessを証明した。target未満の
forward stepはこのrankを厳密に下げる。

最後に任意のdelayed corridorを、internal legal subtractionとstrict budget drop、またはall-forced runと
return/gap boundへ分類した。rebased stationary certificateからもこのoutcomeを直接得られる。ただしremaining-clock
rankはreturnへ到達する有限segmentだけを閉じ、returnから同じparent crossingへ戻るedgeは下げない。

### 第二十三ラウンド：legal endpointのcanonical suffix cursor

`FirstWeakUpcrossingStep.suffix`は、最初のreturn crossingまでのbelow corridor内で開始点を後ろへ移しても、
同じreturnがfirst weak upcrossingであり続けることを証明する。これを使い、fresh below endpointとfirst returnを
持つ`CanonicalBelowCorridorSuffix`を定義した。

suffix内部のlegal subtractionは次時刻にfirst occurrenceを作る。その時刻を新endpointにすると同じreturnを
持つchild suffixになり、history budgetと`returnTime - endpointTime`の両方が厳密下降する。
`CorridorSuffixProgress`は後者を自然数順序へpullbackしたwell-founded relationである。

任意suffixをendpoint=return、later legal endpoint、all-forced suffixへ完全分類した。all-forcedでsuffixが非空なら
return時刻はtarget未満である。これにより固定return crossing内のlegal endpoint選択は有限化された。
一方、return crossing自体は固定したままなので、次の外側progressには別のhistorical dischargeが必要である。
