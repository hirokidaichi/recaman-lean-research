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

### 第二十四ラウンド：legal return境界のexact target

既存の`a_sub_then_add_eq_succ`をcanonical return境界へ接続した。corridor内部のbelow-target sourceでlegal subtractionし、
そのendpointがreturn predecessorなら、次のreturn stepはforced additionである。二歩後の値はsource値`+1`で、
weak upcrossによりtarget以上、sourceのbelow性によりtarget以下となるため、exact targetに一致する。

仮想permanent tailではtargetが未出なので、このlast legal subtractionは不可能である。
`internalSubtraction_before_return`は全legal child endpointがreturnより厳密に前であることを返す。
強化版child theoremはbudget下降、suffix cursor下降、strict endpoint境界を同時に保持し、さらに後続legal endpointが
なければ残りsuffixがall-forcedであることを示す。これでpost-legal terminalの`at_return`枝を除去した。

### 第二十五ラウンド：terminal all-forced crossing window

all-forced suffixのtelescoping式を再構成し、final return stepのforced additionまで延長した。これにより
`a (return+1)`はendpoint値と全clock和で明示される。`TerminalAllForcedSuffixCertificate`はtarget missing、
endpointのreturn以前性、all-forced性をまとめる。

`crossingWindow`はこの証明書から`endpoint < return < target`、`a return < target < a (return+1)`、
final addition式、全traceを抽出する。また`target - a return`と`a (return+1) - target`がともに正で、
return clock以下であることを証明した。legal child以後に後続legal endpointがなければ、このwindowと直前の
strict history-budget dropが同時に得られる。outer residualは有限算術windowへ縮約された。

### 第二十六ラウンド：suffix強帰納とterminal二形正規化

`returnTime - endpointTime`を帰納変数にして、任意のnonempty missing-target suffixがterminal all-forced suffixへ
到達することを強帰納で証明した。legal endpointが存在する場合は`child_of_internalSubtraction_missing`が返す
strict childへ移る。missing-target boundaryによりchildはreturnより前に残り、suffix cursorが厳密に減る。
legal endpointが存在しない場合は定義からall-forcedである。従って任意個のlegal endpointを一つの定理で消費できる。

original historical corridorについて、immediate returnならsource>target、fresh endpoint<target、down/add/valleyの
exact equationsを持つ`ImmediateHistoricalValleyCertificate`を構成した。delayed returnなら上の強帰納結果を
finite crossing windowへ変換する。`terminalShape`は全typed dischargeをこの二形のどちらかへ正規化する。
残る外側義務は、二形に共通するfreshnessまたはanchor progressを作ることである。

### 第二十七ラウンド：terminal strict crossing balance

immediate valleyとfinite all-forced windowの共通final stepを`StrictTerminalCrossingBalance`として切り出した。
target missingによりupcross endpointはtargetより厳密に大きい。forced addition式を展開するとtarget gapとovershootの
和は`returnTime + 1`に一致する。両差は正なので、それぞれ`returnTime`以下である。従来all-forced windowに保持して
いた上界がimmediate valleyにも成立することが共通定理から従う。

`NormalizedTerminalCrossingData`はこのbalanceと、original endpoint以後・return以前にあるfresh below endpoint、
およびそのendpointから同じreturnへのcanonicalityをまとめる。terminal二形をcase splitするのはこの変換定理だけで、
後続のouter progress設計はbranch-independentなinterfaceを利用できる。

### 第二十八ラウンド：terminal final blocker

共通balanceが保持する`¬ CanSubtract`を、定義通り数値不足とhistory membershipへ分解した。ただし残余をそのまま
返さず、strict crossingの算術と履歴APIで強化した。数値不足なら`a return ≤ return+1`であり、final addition式から
`a (return+1) ≤ 2*(return+1)`、strict crossingから`target < 2*(return+1)`を得る。

subtraction candidateが正なら、それが`valuesThrough return`に属する。first occurrenceを抽出し、candidateが
`a return`より小さいことからfirst timeはreturnと一致できず、厳密に前になる。candidate自身も正で、predecessorと
targetより小さい。`StrictTerminalCrossingBalance.ForcedReason`はこの二枝をtyped residualとして保持し、normalized
terminal dataとdischarge certificateの双方から直接取得できる。

### 第二十九ラウンド：terminal blocker position

`TerminalFreshEndpointCertificate`を独立させ、normalized terminalが返すfresh below endpointのorigin/return時刻境界、
first occurrence、canonical returnを再利用可能にした。final historical blockerのfirst timeをこのfresh endpointと比較し、
at-or-beforeとstrictly-afterへ分けた。

strictly-after枝ではblocker candidateがtarget未満でfirst occurrenceを持つため、`missingBelowCount_strict_of_firstAt`を
直接適用し、fresh時点からfirst timeへのstrict budget dropを得た。at-or-before枝はouter historical provenanceとして
残す。immediate valleyはfresh endpoint=returnで、全historical blockerがfirst time<returnを満たすため、after枝を
取らない。この結果、未解決のhistorical blocker residualはfresh以前に限定された。

### 第三十ラウンド：master terminal residual

terminal shape、strict balance、forced reason、blocker positionのcase splitを`PermanentTailTerminalResidual`へ統合した。
immediate枝はinsufficient／historicalの二形、finite window枝はinsufficient／outer blocker／budget progressの三形を持つ。
finite insufficientには`return < target < 2*(return+1)`のclock bandを保持する。

`terminalBudgetProgress_or_outerResidual`はfinite-after blocker constructorをstrict `missingBelowCount`下降として左辺へ
分離する。右辺に残る真のouter residualはimmediate insufficient、immediate historical、finite insufficient、
finite outer blockerの四constructorだけである。後続研究はこの四形に対してのみouter rank下降を構成すればよい。

### 第三十一ラウンド：finite terminal return candidates

finite insufficient枝のbandを`terminalReturnCandidates target`として明示列挙した。これは`List.range target`を
`target < 2*(return+1)`でfilterしたlistであり、membershipは二つのband不等式と同値である。filter前のrange長から
候補数がtarget以下であることを証明した。

候補のenvelope rankを`target-return`と定義し、自然数順序へのpullbackでwell-foundednessを証明した。同じtargetの
候補間でlater returnへ移るとこのrankは厳密下降する。最後にmaster outer residualのfinite insufficient constructorを
candidate membershipへ変換し、残るnon-clock residualをimmediate insufficient、immediate historical、
finite outer blockerの三形へ限定した。

### 第三十二ラウンド：outer historical blocker backtrack

immediate historicalとfinite outer blockerを`TerminalOuterHistoricalBlockerCertificate`へ統一した。positive candidateが
time 0に初出することは`a 0 = 0`に反するためfirst timeは非零である。first-time predecessorからfirst timeへ
`missingBelowCount`が厳密下降し、`seenBelowCount`が厳密増加する証明書を構成した。

history探索の向きを逆に取ると、このseen gainは既存`TailCycleProgress`のstrict backtrack edgeになる。
`tailCycleProgress_of_selected`はnext history timeを`firstTime-1`に選ぶ条件をtheorem statementへ明示する。
またblocker first timeをoriginal down endpointと比較し、後ならoriginal endpointからstrict forward budget drop、
以前ならouter-history residualへ分類した。残る不足はpredecessor clockのrankではなく、対応するsemantic search nodeを
構成・選択するprovenanceである。

### 第三十三ラウンド：blocker generation semantic boundary

terminal historical blockerのfirst occurrenceに`firstAt_final_transition`を適用した。candidateは正なのでtime-zero枝は
不可能である。legal subtraction枝では`legalSubtraction_firstAt_predecessor`を再利用し、candidateより大きいpredecessor、
そのearlier first occurrence、加法等式、candidate freshnessを保持した。predecessorのtarget相対位置も明示した。

forced addition枝ではpredecessorのfirst occurrenceを履歴から抽出した。candidate<targetとaddition equationにより、
predecessorとstep clockはいずれもtarget未満になる。subtraction failure reasonも保持する。
最後にcandidate landing自体はtarget未満なので、target以上を要求する`NormalPhaseInvariantAt`と`DebtInvariant`には
直接入れないことを証明した。残るsemantic gapはbelow-target historical/crossing domainへのadapterに限定された。

### 第三十四〜第三十六ラウンド：semantic adapterと反復可能なmaster rank

blockerを生成したpredecessorをtarget相対位置で分け、above-target側はearly/ready normalの既存complete theoremへ、
below-target側はfirst occurrenceとcanonical future returnを保持するcrossing証明書へ接続した。crossing anchorが下がれば
global phase progress、同値で時刻が早まればcursor progress、stationary再開ならblocker直前のseen budget、anchorが増えれば
`target-anchor`をそれぞれ下降量にした。選んだcrossingを次のpermanent-tail parentへinstallし、chronology mismatchもfresh
downcross endpointによるmissing-budget下降へ変換した。

これらをmissing history、anchor gap、crossing time、restart seen、cycle phase、local seen、minimumの七成分
`TailInstalledCycleProgress`へ統合した。重要なのは、個別のrank不等式だけでなく、selected crossing、old crossing time、
history horizon、次のdischargeを再構成できるprovenanceを同じ証明書に残したことである。

### 第三十七〜第三十九ラウンド：terminal全枝のsemantic closureと有限選択

above-target predecessorのearly/ready残余を既存semantic theoremで閉じ、immediate insufficient枝はexact `+1` reboundから
`CoverageStep`へ接続した。terminalで残ったfinite return branchには、returnだけでなくendpoint、parent anchor、old crossing、
down endpoint、historical first time、tail start、minimum valueを段階的にkeyへ追加した。各keyは固定target/horizonの有限listに
属し、fresh selectionは`erase`後のlist長を厳密に下げる。

一方、minimum witness timeはparent horizonで直接有界とは限らない。ここでは有限keyへ無理に追加せず、shifted tail上の
`FirstAtOrAfter`としてcanonical化し、同じtail startとminimum valueから得る時刻の一意性を証明した。これにより、
「有界な選択は列挙して消費し、非有界なwitnessはcanonical identityで消す」という役割分担が明確になった。

### 第四十ラウンド：visited-list no-goとexact replay境界

canonical keyをvisited listから除去しても、同じ有効windowからexact revisit residualを再構成できることを証明した。
従って「候補を一度使ったから次は選べない」というlist membershipだけでは数学的矛盾にならない。再訪を拒否する状態を
増やす前に、このno-go theoremを置いたことで、残る義務がデータ構造ではなくexact canonical segment自身の算術であると判明した。

### 第四十一ラウンド：finite terminal windowの算術的排除

all-forced suffixの最後の一歩とinsufficient boundから直前値を1以下に抑え、traceをfresh endpointまで戻した。
first occurrence条件によりendpointは時刻1・値1に固定され、長いsuffixは最初のclock 2だけで上界に反するためreturnは時刻2となる。
strict crossingは`a 2 = 3 < target < a 3 = 6`なのでtargetは4または5だけである。しかしLeanカーネルが
`a 131 = 4`と`a 129 = 5`を`decide`で検証し、target missingに矛盾する。これによりfinite branchとexact replayは追加仮定なしで消えた。

### 第四十二ラウンド：progress-only outcomeとsuccessor provenance

terminal outcomeをtarget occurrence、strict history progress、semantic phase progress、installed master progressの四形へ平坦化した。
semantic枝は比較元のlocal parentを保持し、異なるrank contextを誤って比較しない。さらにinstalled master枝ではselected crossingの
installとactual next dischargeの存在を結果に同梱した。terminal局所解析に残余はなく、次の未解決点は三種類のwell-founded relationを
跨いでsuccessorを反復するglobal recursionだけである。

## ここまでの証明から得た学びと進め方の指針

### 数学・証明設計

1. **残余は曖昧な命題でなくtyped constructorにする。** 非進捗をgrowth、chronology、stationary、insufficient、historicalなどへ
   完全分類すると、各枝に不足している証明データと、本当に実在する反例が分離できる。
2. **局所停止と大域進捗を混同しない。** corridor内のclock下降、history内のminimum下降、cycle間のanchor下降は別relationである。
   まず各relationを独立にwell-founded化し、遷移方向が確定してから外側優先順位を持つ辞書式rankへ統合する。
3. **証明書には次の一手を再構成するprovenanceを残す。** 値と不等式だけでは不足する。first occurrence、representative time、
   history horizon、old crossing、tail start、選択endpoint、local parentをconstructorから失わないことが再帰化の条件になる。
4. **有限選択とcanonical選択を使い分ける。** target/horizonで有界な時刻や値は明示listとerase-length rankで管理する。
   有界でないwitnessは最初の出現などへcanonical化し、一意性で選択依存を消す。
5. **visited情報はそれ自体では再訪矛盾を与えない。** 同じ数学的certificateは「使用済み」という外部状態と無関係に再構成できる。
   stateを増やす前にno-go theoremを試し、再訪segmentから新しいstrict edgeか算術矛盾を抽出する。
6. **抽象化の末端では定義を展開してexact equationへ戻る。** 今回はfinal forced addition、all-forced trace、first occurrenceを
   組み合わせることで巨大なresidual treeが`endpoint=1`、`return=2`、`target∈{4,5}`へ崩れた。
7. **反例は設計成果として形式化する。** potentialの増減両例、stationary rebase、visited-list no-goは失敗ではなく、無効なrankや
   interfaceを再提案しないための境界定理である。

### Leanでの実装・検証ループ

1. まず既存APIを`rg`で探し、小さいadapter theoremで接続可能性を確認してから大きなoutcomeを変更する。
2. 一つのIssueでは「残余の完全分類」「strict edgeまたはno-go」「semantic provenanceの保存」を一つの閉じた単位にする。
3. 長いcase splitは安定した時点で`structure`／`inductive`へ昇格し、後続モジュールでは内部枝を再展開しない。
4. `omega`へ渡す前にRecamán遷移、first occurrence、list membershipを専用補題でNatの等式・不等式へ落とす。
5. 具体的な小時刻の値だけを`decide`でkernel検証し、計算観測を一般定理の仮定にはしない。
6. 各ラウンドで`lake build`、`Recaman.Audit`、禁止語走査を行い、README・証明地図・研究レポートを同じコミットで同期する。

### Issue #60への引き継ぎコンテキスト

次はterminal caseをさらに分類するのではなく、`PermanentTailTerminalSuccessorOutcome`を消費するglobal predicateを先に設計する。
そのpredicateはhistory cursor、local semantic `PhaseSearchNode`、installed `TailInstalledCycleSearchNode`の各帰納仮定と、
installed successorが持つnext dischargeを表現できなければならない。実装順は、(1)各枝のcontinuation lemma、
(2)cross-domain edgeの外側priority、(3)mutualまたはsum-stateのwell-founded induction、(4)permanent-tail contradictionへの接続とする。
local parentをoriginal discharge parentへ同一視したり、三relationのstrictnessだけを並べて再帰呼出し可能とみなしてはならない。

### 第三十四ラウンド：finite selectionからterminal successorまで

finite return候補にremaining-list selection stateを導入し、fresh選択をwell-founded visited rankへ接続した。
`(returnTime, terminalEndpoint)`のwindow key、installed snapshotの`(window, anchor, oldCrossingTime)`比較、
original down endpoint差のhistory下降、historical first/minimum provenanceの固定horizon有限化、tail minimum時刻の
relative first occurrenceへのcanonical化を順に重ね、残る再訪をexact canonical revisitへ縮約した。visited listだけでは
exact replayを排除できないno-goを証明し、残務を単一のresolver interfaceへ集約した。

resolverの算術本体を解くと、finite insufficient windowは`endpoint=1, return=2, target∈{4,5}`に強制され、
`a 131=4`、`a 129=5`のkernel計算でmissing仮定と矛盾する。finite branchとexact replay branchはterminal分類から
完全に除去された。残る枝を全展開し、target occurrence、strict chronology history、local-parent semantic phase、
installed masterの四progress形へ平坦化した。installed master枝にはselected crossing、そのsemantic install、
`TerminalSelectedCrossingDischargeCertificate`の存在を同梱し、strict master edgeのchildをparentとする次の
terminal解析を証明オブジェクトから再開できるようにした。

### 第三十五ラウンド：discharge iteration rank

installed master edgeの七成分nodeは、内側cursorが各解析のblocker first timeに依存するため、連続する二解析間で
比較できない。installationが正確に輸送するのは共有horizon、installed crossing anchor、old crossing cursorの
三成分だけである。この三成分lexを`terminalDischargeIterationRank`としてdischarge-levelに定義した。

anchor growth枝ではinstalled anchorがtarget未満のままparent anchorを厳密に超えるため第二成分が下降し、
equal-anchor earlier crossing枝では第三成分が下降する。どちらでもない枝はanchorとcursorがともに一致する
exact replayで、rankは等式として不動になる。`terminalIterationOutcome`は全terminal dischargeをtarget出現、
既存history/semantic edge、strict iteration progress付きsuccessor、replay証明書の五形へ分類する。

### 第三十六ラウンド：successor iteration closure

三成分rankは`natTripleLex_wellFounded`により整礎なので、strict successor edgeに沿った再帰でiteration
constructorを消去できる。`terminalReplayReducedOutcome`は任意のdischargeが有限回のinstalled successorの後、
target出現・strict history・semantic phase・descendant discharge上のexact replay固定点のいずれかへ到達することを
示す。combined permanent-tail certificateからも初期dischargeを経て同じ四形が従う。未解決の数学は無限反復ではなく
単一のtyped固定点に集約された。

### 第三十七ラウンド：exact replay cycle pinning

replayが保持するeligibilityとselection上界`crossingTime ≤ returnTime ≤ oldCrossingTime`から
`returnTime = oldCrossingTime = crossingTime`が従う。canonical returnはold crossingそのものへ閉じ、dischargeは
fresh downcross endpointからold crossingへの文字通りのcycleになる。crossing clockは値より厳密に小さく、
blocker候補はexact subtraction defect `a C - (C+1)`としてC未満に初出し、crossing stepはtargetをまたぐ明示的
forced additionである。

さらにready crossing nodeは`node_eq`によりhorizonとanchorで形状が決まるため、installed nodeはparentに一致する。
successor dischargeはnode equalityに沿って同じparent・同じold crossing cursorの証明書へtransportでき、replayは
rankだけでなくnode-levelのself-map固定点である。

### 第三十八ラウンド：replay corridor band

`clock+1 < a clock < target`からcrossing clockはtarget未満になり、return・old crossing・downcross endpoint・
blocker first time・fresh endpointの全cursorがtarget未満の初期帯に収まる。endpointからcrossingまでの区間で
target以上の値が現れると、中間のweak upcrossingがfirst returnのcanonicalityに反するため、区間は全値target未満の
below corridorである。kernel計算により`a 0=0`, `a 1=1`, `a 2=3`は値境界を満たさず、crossing clockは3以上、
targetは5以上に限られる。

### 第三十九ラウンド：replay kernel floor

replay crossingは実軌道のイベントなので、小さいclockは実軌道の遷移そのもので排除できる。clock 3は実stepが
減算であること（`a 4 = 2 ≠ a 3 + 4`）、clock 4は値境界（`5 < a 4 = 2`が偽）、clock 5はまたぐtarget `8..13`が
すべて時刻16までに実出現することとそれぞれ矛盾する。従ってreplayはclock 6以上・target 8以上に限られる。
上側は`target ≤ a (C+1) ≤ upperTri (C+1)`の三角包絡で押さえられ、固定点の二parameterは両側から挟まれる。

### 第四十ラウンド：missing-target terminal interface

仮想反例内ではtarget-occurrence枝が`target_missing`と矛盾する。従ってcombined certificateが外側探索へ渡す
情報はstrict history edge・semantic phase child・exact replay固定点の三形に確定した。さらにreplayの
crossing cursorとanchor値はdischargeのold crossingで一意に決まり、複数のreplay証明書が異なるcycleを閉じる
ことはない。Issue #60の調査順序のうち、installed successorのwell-founded induction接続（項目2）はこの
三成分rankで完了し、残余はhistory/semantic枝のcontinuation（項目3）と、固定点を破る新しい大域情報の構成
（項目5の縮約形）である。

### 第四十一ラウンド：landing horizon bound

anchored landingの時刻境界を、上流のhistory progress生成箇所を書き換えずに事後導出した。missing targetの
反例では`below_covered`によりtarget未満の全値がtail startまでに出現済みで、first occurrenceの最小性から
landing時刻はstartより厳密に前になる。tailはstart以後厳密にaboveなので、landingとstartの間に弱上抜けが
存在し、canonical restart crossingは`crossing + 1 ≤ start < parent.horizon`を満たす。landingとその再開
crossingはinstalled crossing nodeの形状条件と正確に一致する履歴内境界を得た。

### 第四十二ラウンド：landing crossing mount

境界付きlandingを実際のsemantic nodeへ搭載した。missing-target tailではupcross endpointがtargetと一致
できないためstrict crossingになり、forced additionと正時刻coordinatesがそのまま得られる。parent horizonの
readiness clockはnodeがhorizonを再利用するため輸送される。in-horizon first upcrossingは常に
`CrossingRecoveryInvariant`を経てready crossing nodeを構成でき、閉じたterminal解析の全interface枝が
外側探索のsemantic domainの実objectを渡すようになった。

### 第四十三ラウンド：landing combined install

combined certificateのready crossing以外の全fieldは共有horizonにのみ依存する。従ってmounted landing
crossingへ全fieldがtransportし、terminal解析はmounted nodeから再入できる。landing枝はterminal leafでは
なく同じ解析の新しいparentである。旧parentとの比較はinstalled successor反復と同じanchor二分法に従う。

### 第四十四ラウンド：mounted iteration closure

landing再入反復を整礎に閉じた。anchor dropのlanding crossingはready crossingのままsemantic childとして
返り、anchor growthはanchor gap（自然数）を厳密に下げるため強帰納で消去できる。equal anchorではmounted
nodeがparentと文字通り一致する。mounted反復の最終結果はsemantic phase child・exact discharge replay・
node不動のlanding固定点の三形だけである。

### 第四十五ラウンド：unified fixed point core

二つの固定点の共通数値核を`TailFixedPointCore`として抽出した。どちらも、値がparent anchorと一致し、
missing targetをまたぐ明示的forced additionであり、mounted nodeがparentを文字通り再生産するcanonical
crossing選択である。最終統合定理`unifiedOutcome`により、missing-target permanent tailはsemantic phase
childを渡すか、discharge replay／landing cycleのprovenanceを付けたparent-node再生産固定点で終端する。

### 第四十六ラウンド：unified core kernel floor

統合coreにblocker不要のkernel floorを与えた。straddleとforced additionは実軌道イベントなので、clock 3は
実stepの減算、それ以外のclock 5以下はまたぐtargetの実出現と矛盾し、両固定点で共通にclock 6以上が従う。
上側は`target ≤ upperTri (clock+1)`の三角包絡で押さえられる。

### 第四十七ラウンド：replay floor second stage

同じ三系統排除をclock 17まで進めた。本質的障害はただ一つ、値19の初出が時刻99734と深く、clock 6の帯
`(13,20]`とclock 8の帯`(12,21]`の双方に19が含まれることである。他のtargetはすべて時刻31以内（clock 17の
帯`(25,43]`は時刻111以内）に出現するため、`18 ≤ clock ∨ target = 19`と無条件の`19 ≤ target`が従う。
次の壁はclock 18の帯に含まれる61（初出t=181653）で、二つの深い遅延値はkernel計算の射程外にある。

### 第四十八ラウンド：replay固定点の数値走査実験

固定点の必要条件を実軌道上で走査した（`experiments/replay_fixed_point_scan.cpp`、Lean証明から独立）。
clock 10⁴以下の適格強制加算クロックは2132個で歩幅2の櫛状鎖として出現し、候補対は約1101万。軌道10¹⁰項でも
5,640対（相異なるtarget 18個、すべて遅い初出値）が生存した。時刻200以内で自帯域を完全被覆できるclockは
17ただ一つで、kernel decideによる全域的floor引き上げ戦略は成立しない。着地・blocker条件は候補対をひとつも
排除しなかった。固定点の排除には非計算的な大域論法が必須という定量的根拠を得た。

### 第四十九ラウンド：fixed point shape API

node再生産からparentは自anchor値のready-crossing形状`⟨horizon, a c, .normal, a c⟩`に一意決定される。
phaseはnormal、localMeasureはanchorに一致する。同一parent上の全fixed-point coreは同じcrossing値を共有し、
異なるclockの二coreは「同じbelow-target値が二度forced additionでtargetをまたぐ」exact value recurrenceに
なり、endpointは必ず相違する。

### 第五十ラウンド：fixed point corridor統一

canonical first upcrossingまでの全下性を一般補題`FirstWeakUpcrossingStep.all_below`とした。途中にtarget以上の
値があれば中間弱上抜けがfirst性に反する。replay側で証明済みだったall-below corridorはこの特殊化であり、
landing固定点もfresh landingから再生産crossingまで同じbelow-target corridorを閉じ込める。

### 第五十一ラウンド：core kernel floor第二段

統合coreの床をclock 18へ引き上げた。coreはblockerを持たないため偶数clockもすべて帯排除で処理するが、
結論はreplay側と完全に一致する：`18 ≤ clock ∨ target = 19`、そしてclock解析と独立に無条件の`19 ≤ target`。
両固定点は同一の床を共有し、深い遅延値19（初出t=99734）と61（初出t=181653）だけがkernel計算の射程外に残る。

### 第五十二ラウンド：least-missing summit

全解析を最小未出目標から一本に合成した。`LeastMissingTarget`からpermanent tail・combined certificate・
unified outcomeを経て、semantic phase childまたは床付き固定点core（`18 ≤ clock ∨ target = 19`かつ
`19 ≤ target`）が従う。固定点で終端する反例のtargetは無条件に19以上である。（第七十一ラウンドの追記：semantic枝は
`stepParent`が自由変数のため任意の正targetについて無条件に居住可能であり、この二分岐はtargetに対する
制約を与えない。）

### 第五十三ラウンド：nineteen boundary

床を守る最初の未検証instanceを一つの具体値に確定した。19未満の全値の出現はkernel検証済みなので、
`LeastMissingTarget 19`は「19が一度も出現しない」ことと同値である。19の出現（経験的にはt=99734）を仮定
すれば、固定点で終端する最小未出目標は20以上になる。19の出現をkernel計算なしで証明するには、軌道の
櫛状区間の閉形式を帰納で与える証明書コンパイラ的な手法が候補である。

### 第五十四ラウンド：replay kernel floor第三段

床をclock 32まで拡張した。clock 18の帯`(43,62]`とclock 20の帯`(42,63]`は61（初出t=181653）だけを生存させ、
21..31は実軌道の減算またはclock境界で機械的に死ぬ。例外リストは{19, 61}で閉じたまま
`32 ≤ clock ∨ target = 19 ∨ target = 61`が成立し、targetは`19 ∨ 61 ∨ 34以上`へ三分される。clock 32の帯
`(46,79]`は第三の深い遅延値76（初出t=181643）を含むため、そこが次の非計算的境界である。

### 第五十五ラウンド：comb run閉形式

圧縮軌道検証の基盤として、forced additionと即時repaying legal subtractionの交互区間（comb run）の閉形式を
証明した。low railは1周期に1ずつ下降し、high railはlow railに現clockを足した値になる。CombStep/CombRunは
decidableで、実軌道の時刻23からの4周期combをkernel検証例として同梱した。

### 第五十六ラウンド：comb witness構成

comb stepを状態再評価なしのwitnessから構成した。加算がforcedである理由（減算欠損の非正値または既出witness）
と入口正値は局所的で、大域条件はdecrement値のfreshness一つだけである。run内部の各low-rail着地のfreshnessも
逆向きに抽出でき、圧縮検証の大域義務はfreshness供給一点に限定された。

### 第五十七ラウンド：comb値集合表現とfreshness輸送

comb runの値集合を表現定理として閉じた。run exitでのhistory membershipは事前履歴と二つのrailの直和に正確に
分解され、両railは入口値だけで決まる算術帯に住む。系として、最終low rail未満でrun入口にfreshな値はrun全体を
通じてfreshのままである。comb区間は床を守る深い遅延値（19、61、76）を黙って消費できない。

### 第五十八ラウンド：nineteen replay identification

例外target 19のreplay固定点を数値特定した。blockerのclock境界`clock+1 < 値 < 19`からclockは16以下に落ち、
第二床の消去でclock 6と8だけが残る。各clockはanchor（13／12）、blocker defect（6／3）、初出時刻の一意性による
blocker first time（3／2）まで固定される。first occurrenceの一意性補題`FirstAt.unique`も追加した。

### 第五十九ラウンド：nineteen replay uniqueness

dischargeのhistorical downcrossはcrossing以前に19以上の軌道値を要求するが、時刻6より前の軌道は13を超えない
ため、clock 6は排除される。時刻8より前で19以上の値は`a 7 = 20`だけなので、downcross時刻は7、fresh endpointは
crossing自身（即時return）に固定される。target 19のdischarge replayは「時刻7の`20→12`downcrossから
`a 8 = 12 < 19 ≤ 21 = a 9`のcrossingで即時returnする、anchor 12・blocker 3（初出2）の唯一の完全明示cycle」である。

### 第六十ラウンド：nineteen minimum pins

historical minimumデータも固定した。tail最小値のpredecessorはdowncross時刻7以前に初出し19を超えるが、
その範囲で19超の軌道値は`a 7 = 20`だけである。従ってpredecessor初出は7、tail最小値は21に確定する。
19-反例は保存された全数値成分でpinされ、残る自由は有界でないtail時刻だけになった。

### 第六十一ラウンド：nineteen tail bounds

そのtail時刻に具体的下界を与えた。実軌道は時刻131でなお4を訪れるため、19より上に永続するtailは131より後に
しか始まれない。tailStart>131、start>131、horizon>132で、19-反例は「clock 9以下の完全に固定された歴史」と
「kernel検証済みprefixの外に始まる未知のtail」に真っ二つに分かれる。最初の未知は、このprefix以後に軌道が
20未満へ戻るか、という一点である。

### 第六十二ラウンド：nineteen revisit forcing

pinされたtail最小値21はtailStart（>131）以後に達成されるため、19が未出なら軌道は時刻131以後に21を
再訪しなければならない。検証済みprefixで21はt=9の一度しか現れない。対偶として、21が131以後に再訪しない
なら19-replayは存在しない。19問題は「a 99734 = 19の出現」と「21の遅い再訪」の二イベントに挟まれた。

### 第六十三ラウンド：nineteen elimination

挟み撃ちが閉じた。一般力学補題として、既出の値は自分より大きい時刻で再訪できない：減算着地はfreshnessを
要求し、加算着地は自分のclock以上の値になる（`a_succ_ne_of_seen`）。21はt=9で既出なのでt>21の再訪は
不可能であり、19-反例が強制する21再訪と矛盾する。従ってtarget 19のreplay固定点は存在しない。深い初出
`a 99734 = 19`のkernel検証を一切使わずに例外target 19は全kernel floorから消え、無条件に`18 ≤ clock`、
`32 ≤ clock ∨ target = 61`、`20 ≤ target`が成立する。

### 第六十四ラウンド：sixtyone elimination

同じ再訪不可能性でtarget 61のreplayも排除した。61-反例のtailは`a 222 = 47`により222より後にしか始まれない。
minimum predecessorの初出fは58以下に落ち、59分岐のうち42件は帯値が61以下、2件は初出性違反、残る真の初出
15件はすべて後続値`a f + 1`（63〜115）が時刻222以内に既出であり、tail最小値の遅い再訪が不可能になる。
従ってtarget 61のreplayも存在せず、床は無条件に`32 ≤ clock`かつ`34 ≤ target`へ確定した。深い遅延値の
例外リストは空になり、この排除機構は帯検証＋再訪不可能性の組合せとして任意のclockへ機械的に拡張できる。

### 第六十五ラウンド：minimum predecessor shape

19・61排除に共通するパターンを一般テンプレートとして一度だけ述べた。順序境界（early clockと値が
minimum時刻未満）の下で、minimum predecessor初出直後の「減算→加算」follow-upはtail最小値の早期出現を
再生産し、再訪力学と常に矛盾する（`no_subAdd_minimum_predecessor`）。従って生存し得るreplayの
predecessor直後は「即時加算」または「二連減算」に制限される。次エポックはこの純局所二分法をclockごとに
攻撃できる。

### 第六十六ラウンド：predecessor follow-up witness

二分法にwitnessを付けた。predecessor値はtargetを超え自分の後続clockも超えるため、即時加算がblockedされる
理由は「減算欠損`a f - (f+1)`の既出」しかない。二連減算枝では合法減算のfreshnessから`f+1`にfreshな初出が
生まれる。生存replayは必ず、具体的な既出witnessか新しいfresh landingのどちらかを局所データとして携える。

### 第六十七ラウンド：crossing record exclusion

replay crossingが軌道recordであり得ないことを示した。downcrossはmissing target以上から始まり、straddleは
crossing値をtarget未満に保つため、crossing値はより早い軌道値（downcross値）に厳密に支配される。running
maximumを更新する櫛の上歯型clockは、帯検証を行わず一括排除できる。この定理と帯検証・再訪不可能性を
組み合わせれば、床のclockごとの引き上げは三種の機械的道具で進められる。

### 第六十八ラウンド：replay kernel floor第四段

三種道具の反復でclock 32..111を全消去した。recordクロック（33・66・101）は一括排除、機械的な減算／
clock境界の櫛が大半を消し、真の再訪排除が必要だったのは32・35・65・68・70・72・74・100・103・105・107の
11個である。tail開始の深い錨（`a 367 = 110`、`a 369 = 109`、`a 371 = 108`）を追加し、床は無条件に
`112 ≤ clock`・`114 ≤ target`となった。停止点はclock 112で、帯の最小前駆候補370の後続371の初出が
t=4825とkernel射程外にある。19・61・76に続く第四の深部残留値であり、さらなる引き上げには再訪排除を
深部値へ届かせる圧縮検証（comb機構）が要る。

### 第六十九ラウンド：prefix-successor coverageとclock 112 pinning

個別clockの再訪排除を`ReplayPrefixSuccessorCoverage`へ抽象化した。replay anchorより大きい全prefix値のsuccessorが
later low witness以前に出現済みなら、historical tail minimumは既出値の遅い再訪となりreplayは不可能である。
同じcoverageをclock区間へ一括適用するfloor定理と、唯一の未被覆successorをminimum値へpinするexcept版も証明した。

clock 112ではkernel計算を時刻371までに限定したまま、未被覆successorが371だけであることを証明した。その結果、
minimum値371、predecessor初出108、historical downcross 109、`152 < target ≤ 261`まで固定された。深い軌道等式を
`native_decide`で持ち込むと追加公理になるため採用していない。外部監査ツールではcutoff 99734のcoverageがclock
776まで続き、次の経験的障害はclock 777・successor 879（初出328002）と判明した。次はdeep traceをkernelで圧縮検証
するか、pin済みの`108 → 109 → 110 → 112` cycleからrecord／blocker荷重の新しい矛盾を抽出する。

### 2026-08-29 セッション振り返り：方向性評価

第三十五〜第六十八ラウンド（49コミット、新規34モジュール、約6,500行）を終えての評価は
「進んでいる。ただし進み方に構造的な但し書きが付く」である。

停滞ではないと判断する根拠は、残余の種類がセッション中に三度変わったことである。開始時の
「installed master反復は解析間で合成できない」という開放的残余は、まずexact replay固定点という
単一の型付きオブジェクトへ、次に「clock 112以上・target 114以上で、predecessor直後が二つの
witness付き形状に限られる単一のnode固定cycle」へと縮約された。最強の反停滞シグナルは、
「19と61の排除には非計算的議論が必要」と記録されていた壁が、`a_succ_ne_of_seen`という数行の
力学補題（既出値は自分より大きい時刻で再訪できない）によって深い初出の検証なしに落ちたことである。

生産性の正直な換算として、本当に荷重を支えている新しいアイデアは三つに絞られる。
(1) installed successorへ正確に輸送される三成分rank、(2) 固定点のnode-level同定
（installed node = parent）、(3) 再訪不可能性補題。残りのラウンドはこの三つを運ぶ足場であり、
コミット数を進捗の指標にしてはならない。

一方で成果はdischarge replay側に偏っており、動いていない前線が停滞リスクである。
landing固定点側には今回の武器が一つも届いておらず（predecessor初出の上界に相当するものが無い）、
semantic枝の消費者（restricted oracle再帰）は依然として存在しない。床上げは排除コストが桁で
下がったものの、それだけでは定理に到達しない無限プロセスである。次エポックの優先順位と
予想真偽の二仮説の下での位置づけはROADMAPに記載した。

セッション運営面では、並列サブエージェント4体が全て納品し（`lake env lean`単独検証・
ファイル分離の規約が有効）、数値走査実験が「kernel decideによる全域排除は不成立」を事前に示して
再訪排除論法への転換を促した。反省点は、前半で指定時間枠を大幅に下回って切り上げたこと、
root moduleへのimport追加を二度忘れたこと、docsに一度過大な主張を書いて修正したことである。

### 第七十ラウンド：witness下降連鎖のno-go決着

ROADMAP優先度1（clock非依存の一般排除）を検証し、否定的に決着させた。witness付き二分法のblocked枝から
`BlockedFirstOccurrence`を切り出し、減算欠損`a f - (f+1)`の既出witnessが`(値, 初出)`のearlier-smaller辺を
clock列挙なしで供給することを証明した。尺度`値 - 時刻`も真に減る。しかし整礎性は発火しない。blocked配置の
三条件のうちwitnessへ輸送されるのは初出性のみで、`clock < 値`とblocked性が落ちるためである。連鎖の停止点は
実軌道に無数に存在し、tail側から輸送される情報（witnessがtail最小値未満・tail開始前）はそれらと矛盾しない。

残余義務は`regenerate`の二条件として型で固定し、`blockedFirstOccurrence_impossible_of_regeneration`により
「それさえ埋まれば全blocked配置が一括で死ぬ」形へ縮約した。副産物として、blocked枝では`f+2`の減算候補が
`a m - 2`に確定することから`target + 2 < a m`がclock非依存に従う（証明書自身の`target + 1 < a m`の真の強化）。

判定：この経路は床上げの卒業には効かない。次に試すべきはdichotomyのもう一方（二連減算枝）で、
`CanSubtract (f+1) ∧ CanSubtract (f+2)`が強制する大きな下降とtail構造の噛み合わせを見る。

### 第七十一ラウンド：semantic枝が無情報であることの確定

大域組み立ての最古の負債（semantic枝の消費者）を正面から検査し、診断が誤っていたことを確定した。
`PhaseSearchProgress`は四成分lex順に過ぎず`stepParent`は存在量化されているだけなので、任意のchildに対し
anchorを一つ上げた親を常に捏造できる（`exists_phaseSearchProgress_parent`）。正のtargetは必ずcanonical
semantic startを持つので、頂点定理`LeastMissingTarget.semantic_or_flooredCore`の結論そのものが
`0 < target`だけから導出できる（`semantic_or_flooredCore_of_pos`）。つまり「消費者が存在しない」のではなく
「消費すべき情報がoutcome型で捨てられている」のが真因である。固定点解析側は無傷である。

消費者が持つべき強さの下界も確定した。`SemanticBranchClosure target`はそのtargetの出現と論理的に同値であり
（`semanticBranchClosure_iff_occurs`）、semantic枝はconstructor局所の補題では原理的に閉じない。

前向きの成果は三つ。(1) semantic childのrefined domain昇格をhorizon readiness仮定つきで四constructor完全に
構成し、その仮定が除去不能であることを具体反例で確定した。(2) 無仮定で「任意のrefined nodeから降下すると
目標到達かcrossing停止に必ず至る」を証明した。(3) 大域残余をsemantic枝の型強化・ready crossing局所step・
unready crossing漏れの三命題へ分解した。ROADMAPが名指ししていた「ordinary normal constructorのhorizon
整合性」は三層のうち最も軽い層であり、唯一の障害ではなかった。

次はsemantic枝のpayload強化である。生成元`PermanentAboveCorridorTerminalSuccessor`の`below_master`／
`phase_exit`枝は既にrefined情報を持っているのにoutcome型で捨てているため、加法的な精密版outcome型を
新設して拾い直す。

### 第七十二ラウンド：Issue #61の三分割とclock 112残余

prefix-successor coverageの次段を三つの子Issueへ分けた。#62はkernel検証可能なchunked trace、#63は
clock 112固定cycleの構造矛盾、#64はcoverage certificate generatorを担当した。

#62では認証bitmapと時刻別value配列を持つ`TraceMachine`を実装し、fresh／nonpositive／blocked witnessの
三理由を小さなcheckerで検査する構成にした。compact stateが既存`State`を表す`Represents`不変条件、
単chunkと複数checkpointのsoundness、`SeenBefore`／`FirstAt` adapterまでkernel内で証明した。15-step例は
通常`decide`で0.5秒程度だが、step単位の1024-step certificateは130秒超となった。従ってprototypeは健全でも
深部値371を実用的に検証する圧縮にはなっておらず、comb区間を一理由で検証する次形式が必要である。

#63では深い等式`a 4825 = 371`を使わず、clock 112のpredecessor follow-upを時刻109・110の二連合法減算へ
固定した。tail minimum clock `m`は`371 < m`、`FirstAt a 371 m`、時刻mの合法減算、
`a (m-1) = m + 371`を満たす。異なるtarget・sourceのclock-112 replayも同じmを選ぶため、残る深い自由度は
371のグローバル初出clock一つである。構造矛盾そのものは得られなかったが、追加補題の入力型は確定した。

#64ではexact-history走査を決定的TSVへするgeneratorと回帰テストを追加した。clock 112 / cutoff 371の唯一の
例外371、cutoff 99734によるeligible clock 112..776のcoverage、次の壁clock 777 / successor 879
（初出328002）を再現した。全行を`empirical`と明示し、実験結果をkernel証明として扱わない境界を保った。

### 第七十二ラウンド：敵対的健全性監査と過大主張の訂正

独立したエージェントに読み取り専用の敵対的監査を依頼し、その指摘を反映した。全文は
[健全性監査](SOUNDNESS_AUDIT.md)にある。

**偽の定理・`sorry`・隠れ公理は発見されなかった。** Lean中の軌道等式96件を機械抽出して独立実装と照合し
全件一致（1件の見かけ上の不一致は背理法の中間式）。docsにのみ書かれた数値（371の初出4825、19の99734、
61の181653、76の181643、clock 112の帯、879の328002）もすべて一致した。定義は標準的なRecamán数列であり、
最終目標も正真正銘の全射性で、すり替えはない。論理的循環もない。

公理監査は依頼側が渡したログが切り詰め版だったため監査時は「未確認」と判定されたが、統合時に全出力を
機械照合し、**全614宣言が`propext`・`Classical.choice`・`Quot.sound`のみに依存する**ことを確認した。
指摘を受けて`scripts/check.sh`に公理集合のassertを追加し、許可集合外の公理が一つでも現れれば非ゼロ終了
するようにした。監査から漏れていた5定理も`Audit.lean`へ追加した。

訂正した過大主張は次の通り。(1) 「無条件112≤clock・114≤target」はdischarge replay枝限定であり、
landing固定点枝の床は`18 ≤ clock ∨ target = 19`のままである（README・CHANGELOG・PROOF_MAP・
RESEARCH_REPORT）。(2) 「例外リストを空に」はclock 32までの掃過に限る（床を112まで上げた段階で
新たな深部残留値371が例外になる）。(3) 「19未満の反例が到達し得る経路はsemantic枝だけ」は制約に
なっていない（第七十一ラウンドの発見）。(4) ROADMAPの「固定点の排除が完了した時点で全射性が従う」は
誤りで、semantic枝の型再設計とready crossing橋の二つが追加で必要である。(5) 852655の10²³⁰項未出は
外部報告であり本リポジトリでの検算は3×10⁶項までである旨を明記した。

未対応として残したのは、ready crossing ⊊ crossing の型ギャップ（ROADMAP項目3として登録）である。

### 第七十三ラウンド：landing固定点への三種道具移植

これまで武器が一つも届いていなかったlanding固定点側へ、discharge側で有効だった三種道具を移植し、成否を
確定した。**再訪排除は無条件で移植できた**。`PermanentTailCombinedCertificate.minimum_revisit_absurd`は
crossing clockを一切参照せず、combined証明書だけで既出値の遅い再訪を禁じる。record排除は共有核レベルの
汎用形として無条件に成立し、landing分岐では`predecessorFirstTime < landingTime`のとき発火する。

**欠けているのはdowncross前置界ただ一つ**である。`window_below`により`[landingTime, crossingTime]`は
全区間target未満なので、target超のpredecessor初出は窓の外の二択（landing前かcrossing後）にしか居られない。
landing分岐はこの二択を決める情報を持たない。discharge側で上界を与えていた三段連鎖のうち`eligible`が
replay固有フィールドであり、combined証明書にもlanding分岐にも存在しないためである。代替の上界候補は
親の格納crossingしかなく、それも三通りにピン留めした（`exists_parentCrossing`・
`aboveTarget_before_crossing_or_pinnedParent`）。

前置界を仮定すればcoverageエンジンがそのまま発火し、landing床は例外なし`32 ≤ crossingTime`へ上がる。
統合outcomeを`semantic_or_thirtytwo_or_landingGap`として「semantic枝 ∨ 32≤clock付きcore ∨ landing gap」の
三択へ精密化した。landing gap枝は`crossingTime < predecessorFirstTime`かつ`target < a predecessorFirstTime`
という具体形であり、次の攻撃点である。

なおlanding側のcoverage cutoffは実測で131が上限であり（`a 32 = 46`の後継47の初出が時刻222）、
32を超えるには先にtarget床を48以上へ上げてcutoff 222を解禁する必要がある。順序はreplay側と同じ階段になる。

### 第七十四ラウンド：二連減算枝の構造化と排除不能性

witness付き二分法のもう一方の枝を構造化した。`DoubleSubtractStep`として切り出し、`a (f+1) = a f - (f+1)`・
`a (f+2) = a f - (f+1) - (f+2)`の確定、三時刻が相異なるfresh初出であること、いずれもtail開始より厳密に前に
あること、`a (f+2) + (2f+4) = a m`の厳密等式を証明した。

blocked枝で得た`target + 2 < a m`は**この枝へは輸送されない**。二連減算枝の実現値`a m - f - 2`と
`a m - 2f - 4`はどちらも`a m - 2`を厳密に下回るためである（`0 < f`は`a 0 = 0`とclock boundの矛盾から従う）。
残余義務は`tailMinimum_gap_of_attainment`として「`a m - 2`の実現witnessが一つあれば無条件化完了」の形に
切り出した。

**この枝の排除はpre-tail領域への下界なしには原理的に不可能である。** 証明書が軌道に下界を課すのは
`MissingStrictAboveTail.strictly_above`と`TailMinimumAt.minimal`のいずれもtail開始以降に限られるが、
二連減算枝が語る時刻は全てtail開始前にある。pre-tail領域へ届く大域フックは`a f = a m - 1`とtargetの欠損の
二本しかなく、両方すでに消費している。corridor側の三ケースも`a m`と`target`の距離を挟むだけで矛盾に至らない。

代償として無条件の強化が得られた。corridorデータ（`downcross.horizon_le_time` → `eligible` → `time_eq` →
`crossingTime_lt_target`）を繋ぐと`f + 2 < target`が出て、`f + 3 < a f`・`f + 4 < a m`が従う。
既存の`minimum_predecessor_value_above_clock`を2段強化したもので、clock床上げの探索範囲を直接削る。

したがって`minimum_predecessor_followUp`は依然として二本枝であり、clock非依存の一般排除は
「`a m - 2`の実現を枝に依らず取る」か「pre-tail領域に下界を持つ証明書フィールドの新設」のいずれかを要する。

### 第七十五ラウンド：床上げ機構の構造的天井の測定

床上げ路線に追加投資すべきかを判断するため、`ReplayPrefixSuccessorCoverage`の漸近的生存可能性を測った
（`experiments/coverage-limit-2026-08-29/`）。cutoffが時刻と値の両方の上界であることを使って
`Need(clock) = max { max(v+1, first[v+1]) : v = a t, t < clock, v > a clock }`と再定式化すると
`coverage(clock, cutoff) ⟺ Need(clock) ≤ cutoff`となり、cutoff非依存に全答えが一度に出る。

記録されていた経験的主張（cutoff 99734でclock 776まで、次の障害はclock 777・successor 879・初出328002）は
二つの独立実装で再現・確認した。換算は`射程 ≈ 0.049 · 床^2.01`（R² = 0.87）だが、フロンティア付近の
局所指数は6.29まで悪化し、最後は射程を18倍にしても1 clockも進まない。

**clock ≈ 5.4×10⁴に機構そのものの天井がある。** clock 53,906はanchor 167,475の上のprefix値167,476
（初出t=53,904）の後続167,477が5×10¹⁰まで未出であるため詰まる。理由は構造的で、初出深度比の裾が極端に
重い一方、anchorより上のprefix値の個数が`k ≈ 0.17·C`とclockに比例して増えるためである。射程無限大でも
clock 10⁶までの65%はcoverageでは消せない。

固定点の他の必要条件も国勢調査した。強制加算まで課しても213,739 clockが残り、そのうち99.4%が帯に
地平線内未出targetを含む。record排除が落とすのは22個だけで、生き残る`(C, T)`対は4.33×10⁸、decade別に
超線形に増える。帯幅が`C+1`で伸びるため反例候補の探索空間はclockとともに広がる。

投資判断として、深部軌道値のkernel検証（射程延長・圧縮証明書）への追加投資を行わないことを確定した。
clock 112の障害`a 4825 = 371`を検証しても床は192までしか上がらない。主資源は大域組み立ての構造的欠陥の
修復とclock非依存の一般排除へ投じる。これらの数値結果はLean証明には一切使用していない。

### 第七十六ラウンド：semantic枝の捏造不能な精密化

第七十一ラウンドで同定した情報欠落を実際に埋めた。精密版`PermanentTailRefinedSuccessorOutcome`の核心は
二点である。(i) 子が広義`PhaseSemanticInvariant`ではなくrefined domain `OrbitReadyRefinedInvariant`に属する。
(ii) 親を存在量化しない。四つのsemantic枝はそれぞれ証明書自身のclockから決まる名前付きノードを親に固定する。

非捏造性を三本の定理で形式化した。refined domainのnormal相では`anchorParent = localMeasure`が要求されるので
anchor bumpによる捏造はそこで詰まる。zero-budget親には子が存在しないので「どの親にも子がある」は偽である。
crossing枝の子は親とhorizonを共有するのでstrict edgeはanchor下降からしか来ず、refined domainでanchorが
target未満になれるのはcrossing recoveryだけなので、実軌道の本物のstrict crossing証明書が要る。

限界も明示する。四枝を忘却した`RefinedDomainEdge`が`0 < target`から導出できないことは証明していない。
非捏造性が確実なのは親を固定した各constructorであって忘却形ではない。下流は可能な限り精密版のまま扱い、
`toEdge`は最後の接続点でだけ使う。

immediate枝は元の`canonicalCoverage_phaseSemantic`経路が`target ≤ downTime + 3`を要求し、valley証明書から
その時計が出ないため精密化できなかった。同じ値`a (downTime + 2)`を親のzero-budget horizonへ格納する
extended-history表現へ経路変更して解決した（`immediateValley_extended`）。

残余は伝播であり、頂点までの10モジュールのうち9段は純粋な再包装、唯一新規生成する`MountedIteration`も
`crossing_refined`として構成できる。新しい数学は不要な機械的作業である。次エポックで加法的に積む。

### 第七十七ラウンド補遺：balanced kernel traceで時刻4825へ到達

Issue #62のflat trace checkerを64-step leafとbalanced treeへ組み替え、さらに認証済み訪問集合を`Nat` bitsetで
保持する`BitTraceMachine`を実装した。各branch codeは外部生成値にすぎず、`ValidBitTraceStep`、
`BitTraceMachine.Represents`、既存`State`へのstep soundnessを通らなければ定理にはならない。

通常のkernel reductionで`a 1024 = 3698`と`a 4825 = 371`を証明し、モジュール全体の型検査は約3.6秒だった。
これにより「深部値371はkernel射程外」という技術的な壁自体は解消した。追加公理や禁止された評価機構は使わない。

並行して、clock 112のtarget帯153..261から223を除く108値の明示witness表を9個程度のpiecewise-affine式へ
圧縮し、表と式の一致をkernelで検証した。`Clock112ExactHistoryCertificate`を与えればreplay targetが223に
一意化する。flat 2622-step入力からcertificateを作る試行は150秒超だったが、balanced 4825-step出力の
認証bitsetを直接読むadapterへ切り替え、追加仮定なしでclock 112 replayの`target = 223`を証明した。

同じtraceの4824-step prefixで値371のbitが未設定であることと、4825-step endpointを同時検証し、
`FirstAt a 371 4825`を得た。clock 112 replayのhistorical minimum clockは4825に一意化され、残余は
`4825 ≤ witness ∧ a witness ≤ target`を満たすfuture low witness一つへ縮約された。

重要な境界として、`a 4825 = 371`単独ではclock 112 replayを排除しない。tail minimum clockを4825へ同定して
矛盾するには、それより後のlow witnessをkernelで与える必要がある。経験的な最初の候補は時刻99734の値19であり、
これは今回の証明には使っていない。従ってformal replay floorは112のままで、Issue #61は継続する。

tooling側ではbranch reason列と108値のwitness表を決定的Lean断片へ出すgeneratorを追加した。flat断片が
kernel timeoutすることも再現し、balanced checkerが必要な理由を測定可能にした。さらにcompact code・64-step
leaf・balanced treeを再生成するsource generatorも追加し、4825-step生成物のhashを固定した。99734-stepなら
1,559 leaf・約486KBになるという測定まで行ったが、coverage機構の構造的天井が別途確定したためLean importは
行わない。ここで得たcheckerは有限証明基盤として残す。

### 第七十七ラウンド：pre-tail計数枠組みと無条件下界

`ReplayDoubleSubtractDescent`が同定した構造的欠落——証明書が軌道に下界を課すのはtail開始以降だけ——に
対する最初の一手を打った。`missingBelowCount`の厳密な補数`coveredBelowCount`を定義し、
`coveredBelowCount k n + missingBelowCount k n = k`と鳩の巣`coveredBelowCount k n ≤ n + 1`を
標準ライブラリのみの二重帰納法で証明した。

replayへ適用すると**無条件の`target < tailStart`**が出る。既存のtailStart下界はすべて`a 222 = 47`型の
条件付きkernel計算に依存していたが、こちらは計算ゼロ・条件なし・全replayで成立する。

ただし計数だけでは矛盾に届かない。計数が与えるのは常に「`tailStart`は十分大きい」方向で、証明書側の
`tailStart`上界は`tailStart ≤ start < parent.horizon`のみ、`parent.horizon`は無制限である。
「fresh初出3連発がbudgetを食う」路線も消費が3レベルにとどまり無視できる量だった。矛盾へ変えるには
`start`または`parent.horizon`の上界を与える別機構が要る。

副産物として`target + 2 < a m`の残余を単一配置へ釘付けした。tail最小値の局所witnessは`a m - 1`と
`a m - (m+1)`のどちらも`a m - 2`に届かない。`tailStart < m`なら`m-1 → m`の遷移は必ず減算になり
`FirstAt a (a m) m`が従う。`target + k < a m`の一般化は`k = 2`で止まると判定した。blocked枝が`k = 2`を
出せたのは強制加算の次の減算候補がちょうど`a m - 2`になる一回限りの偶然だからである。

### 第七十八ラウンド：精密版の伝播開始と忘却形の捏造可能性

精密版outcomeを頂点まで運ぶ作業に着手したところ、**忘却形もまた捏造可能である**ことが判明した。
`RefinedDomainEdge target`はcanonical start自身がrefined nodeであり`OrbitReadyNormalInvariant.refinedStep`が
局所全域なので、解析を一切使わずに構成できる（`occurs_or_refinedDomainEdge_of_pos`）。忘却形を伝播ペイロードに
すると除去したはずの欠陥が復活するため、生成証明書を保持する`RefinedTerminalSemanticStep`／
`RefinedSemanticEdge`へ設計し直し、忘却は最終接続点だけに限定した。前ラウンドで明示した留保が実際に効いた。

チェーンの構造も訂正された。`terminalProgressOutcome`と`terminalSuccessorOutcome`は`Audit.lean`以外から
参照されない形状監査用の袋小路である。頂点への実チェーンは8段で、先頭2段（SuccessorRank・IterationClosure）
の精密化を完了した。SuccessorRank段は純粋な再包装ではなく`terminalFiniteClosedOutcome`から独立に再分類して
いるため、`anchor_growth`側の3分岐は逐語コピーになった。`MountedIteration`の新規生成点はdischarge証明書では
なくcombined証明書に紐づくので、`RefinedSemanticEdge`に第2コンストラクタとして先行して用意した。

### 第七十九ラウンド：landing前置界の所在特定と新カーネル道具

landing側の前置界問題を一段深く掘り、**必要な最小情報が`predecessorFirstTime < landingTime`ではなく
`source.downTime < parentTime`である**ことを突き止めた。replay側のtool 3が使っているのはcombined証明書の
最小値前駆ではなくhistorical tailの前駆であり、そちらは`downcross.horizon_le_time`で上から抑えられている
ためである。一次消失点は`PermanentAboveCorridorInstalledStep`の`history_progress`で、3生成箇所のうち2つは
自明に、残る1つも`oldCrossing_cursor`経由でabove-target cursorを供給できる。2フィールドを6モジュール
素通しすれば`RefinedLandingCycle`が組め、landing床は無条件に例外なし`32 ≤ crossingTime`となる。

副産物として新しい無条件カーネル道具（prefix最大値バンド消去）が得られた。共有核レベルで
`32 ≤ clock ∨ (clock = 6 ∧ target = 19) ∨ (clock = 18 ∧ target = 61) ∨ (∃ t < clock, target ≤ a t)`へ
分解でき、深部残留値19と61が時刻込みでピン留めされる。replay枝にも適用できる。

### 第八十ラウンド：unready crossing漏れの決着とreadiness橋

大域残余の第三項を決着させた。漏れのliteralな形は**証明不能**である。target 12・node`⟨7, 7, .normal, 7⟩`が
具体反例になる（`a 5 = 7 < 12 < 13 = a 6`、時刻6は強制加算、`12 ∉ valuesThrough 5`）。よってこの残余は
非存在ではなく到達不能性で閉じるしかない。

`OrbitReadyRefinedInvariant`のcrossing成分を作る生成箇所を全数調査したところ、7箇所すべてで**子は常にready
であり、型がそれを記録していないだけ**だった。生成箇所1〜5はreadiness保持版を再証明し、
`ReadyRefinedInvariant`を保存する`RestrictedPhaseSearchOracle`を構成した。残る1箇所
`OrbitReadyDirectRefined.refinedStep`は目視監査では全分岐が非crossingへ落ちるが statement が記録していない。
`OrbitReadyNormalNonCrossingStep`として切り出し、既存定理の真の強化であることを証明した。最小修正は結論を
`RefinedNonCrossingInvariant`へ差し替えるだけで証明本体は不変である。

残余の縮約は`CrossingRefinedStepHypothesis`（素のcrossing全体）→`ReadyCrossingRefinedStepHypothesis`＋
unready漏れ→`ReadyCrossingReadyStepHypothesis`＋監査事実一つ、と進んだ。さらに
`TargetTailReturnHypothesis target`からこの仮説が従うので、
`0 < target ∧ OrbitReadyNormalNonCrossingStep target ∧ TargetTailReturnHypothesis target ⟹ ∃ t, a t = target`
が成立する。従来tail return仮説は「認めても主残余が閉じない」とされていたので、これは実質的な前進である。
難所を隠していないことは`readyCrossingReadyStep_iff_occurs`と`not_readyStep_pair`で明示している。

### 第八十一ラウンド：新成果の敵対的再検査

第七十〜第八十ラウンドの成果を敵対的に再検査した。**偽の定理・`sorry`・禁止機構は発見されなかった**が、
「statementが意図した情報を運んでいない」型の欠陥が三件見つかった。

第一に、忘却形`RefinedDomainEdge target`は**`0 < target`だけから直接導出できる**。
`exists_targetReady_state_of_pos`を二度適用して`target ≤ a n < a n2`なる実時刻を取り、共通horizonへ
`ExtendedHistoryNormalCertificate`として載せるだけでよい。捏造タプルは使わず、すべて実軌道の状態である。
`occurs_or_refinedDomainEdge_of_pos`より真に強く、`LeastMissingTarget`仮説すら不要である。帰結として
`historyEdge_or_refinedEdge_or_installedEdge`は空文、`stuckCrossing_of_refinedEdge`の仮定は死んでいる。
`semantic_or_thirtytwo_or_landingGap`も第一disjunctが空semantic枝なので同様である。

第二に、`refinedNormal_anchorBump_not_orbitReadyRefined`は`node.phase = .normal`を要求しており、
**debt相はこの防御の外にある**。`DebtInvariant.value_lt_anchor`はanchorを上げても保たれるので、
debt相ではanchor bumpがrefined domain内に留まる。非捏造性の主張はnormal相限定と訂正した。

第三に、`blockedFirstOccurrence_impossible_of_regeneration`の仮定は**偽**である。実軌道にblocked first
occurrenceが存在するため（`a 6 = 13`が初出、減算欠損6は既出）、結論が反証できる。第七十ラウンドの
「残余義務を型で固定した」という位置づけを撤回する。

検査側は「history枝も`(1, 0)`で自由である」とも報告した。これは**検査時点の定義に対しては正しかった**。
当時`TerminalChronologyHistoryProgress`は単なるbudget dropで、値1が時刻1で初出するので`(1, 0)`が通った。
ただし同時進行のlanding前置界作業がこの定義を`TerminalHistoryBudgetDrop`と
`TerminalHistoryCursor target (parentTime + 1)`の連言へ強化したため、この穴は閉じた。統合時の再検証で
提出された証明が型検査を通らないことに気づき、経過を追ってこの結論に至り、該当のprobe定理は取り下げた。
エージェントの「全定理が型検査を通った」という報告を鵜呑みにせず統合時に必ず再検証する運用が機能した例である
（この場合の原因はエージェントの誤りではなく、並行編集による定義の変化だった）。

docsの該当箇所（「無条件移植」「無条件に`f + 2 < target`」「anchor bumpは必ず外れる」「残余義務の型固定」）を
すべて訂正した。

### 第八十二ラウンド：頂点床の無条件32化と残余の一本化

landing側に欠けていた前置界を実際に輸送し、**頂点定理の固定点枝の床を無条件に`32 ≤ crossingTime`へ
引き上げた**（従来は`18 ≤ crossingTime ∨ target = 19`）。輸送は当初想定の「コンストラクタへ2フィールド追加」
ではなく、`TerminalChronologyHistoryProgress`の定義を`TerminalHistoryBudgetDrop`と
`TerminalHistoryCursor target (parentTime + 1)`の連言へ強化する形になった。この型は元から
`(target childTime parentTime)`だけで添字付けされているので、`source`依存が生成点に閉じ、下流6段を
Nat持ち上げなしにsource-freeで通せる。副次的にhistory枝自身の情報量も回復した。ただしsemantic枝が空である
事実は変わらないので、頂点定理の二択そのものは依然`0 < target`から出る。床の価値は枝の内容にある。

readiness橋も無仮定になった。`OrbitReadyDirectRefined`の内部ヘルパー8本の結論を非crossingの連言へ強化し
（証明本体の変更は4箇所）、`OrbitReadyNormalNonCrossingStep`を仮定ゼロの定理にした。大域残余は
`0 < target ∧ TargetTailReturnHypothesis target ⟹ ∃ t, a t = target`の一本になり、refined再帰・horizon clock・
crossing-recovery構成子はすべて解消された。価格も明示する。`targetTailReturn_iff_occurs`も同時に証明されて
おり、この仮定は出現と同値である。難しさは減っていない。減ったのは足場の量である。

`target + 2 < a m`の残余配置は否定的に決着した。`target = a f - 1`によりpinned配置は`f`だけで完全に決まり
実軌道上で判定できるが、`a_le_upperTri`の窓は`2f + 2 < target`かつ`target + 1 ≤ upperTri f`で、下端
`f ≳ √(2·target)`・上端`f ≲ target/2`とtargetとともに広がる。列挙すると候補は`f < 3×10⁶`で2438個、累積が
増え続け上限の兆候がない。kernel列挙は床上げと同じ無限トレッドミルであり、pinned枝は構造的議論でしか落ちない。

tail最小値の初出は残り1点へ縮約した。遷移は「減算（fresh初出）」か「強制加算かつ`m = tailStart`」の無条件
二分法で、後者は`5 ≤ m`と`a (m-1) ≠ 1`により死ぬ。残る穴は`m + 1 < a m`のみで、その場合は`a m - (m+1)`の
出現witnessが手に入る。pinned配置内では`target < tailStart`が効いて穴が閉じ、最小値前後4ステップの軌道が
完全決定する。

### 第八十三ラウンド：精密版の伝播（段3・段4）

精密版outcomeの頂点への伝播を8段中4段まで進めた。段3（ReplayInterface、`RefinedTerminalMissingOutcome`）は
予告どおり純粋な再包装で、`target_occurs`を`target_missing`で潰す一行だけが実質だった。段4（HistoryLanding、
`RefinedTerminalAnchoredOutcome`）はlanding側の強化を取り込み、`landing_cursor`も運ぶ形にした。
`progress.exists_freshLandingCursor`の第5成分をそのまま受けるだけで済む。写経はlanding復元の6行のみである。

伝播は`TerminalChronologyHistoryProgress`の定義強化がsource-freeだったおかげでarity追随が一切発生していない。
残りは段5（LandingHorizon）・段6（LandingMount）・段7（MountedIteration）・段8（FixedPointCore）で、
写経が要るのは段5のhorizon評価約25行と段7の強帰納約55行だけと見積もられている。段8到達時には左枝の
無料ルート探しを必ず実施する。忘却形が二度捏造されている以上、ここが最後の関門である。

### 第八十四ラウンド：pinned前方展開と壁の三度目の確認

無条件`FirstAt a (a m) m`は取れなかったが、残余枝を完全に記述した。残るのは
「`m = tailStart` かつ `a (m-1) + m = a m` かつ `m + 2 ≤ a m` かつ `target < m` かつ `a m ≠ target + m`」
の一枝だけである。なぜ計数で閉じないかもこの記述から読める。強制加算は`a m ≥ m`を要求するが、遅延再出現に
よる消去が必要とするのは`a m < m`であり、残余枝は消去の道具が働く条件を構造的に打ち消している。

計数側も追い込んだ。`target < tailStart = m`と`belowTarget_covered_preTail`から`target + 1 ≤ m`、
`a (m-1) = a m - m`がtargetを超える場合は`target + 2 ≤ m`まで伸びる。しかしこれは`m`の**下界**が伸びるだけで、
矛盾には上界が要る。証明書側の上界は`tailStart ≤ start < parent.horizon`のみで`parent.horizon`は無制限である。
**同じ壁に三ラウンド連続で当たった**ので、ROADMAPに独立の節として記録し、次エポックの最優先候補の一つとした。

pinned配置の前方展開は`m+3`まで強制加算で確定し、`m+4`で分岐が避けられないことを算術的に証明した。
第4段の減算候補`target + 2m + 4`はtail最小値を`2m + 2`も上回るので、tail最小性が禁じられない。
tailが効いたのは候補が`a m - 1`に落ちる第2段だけで、第3段は「既出」で決まり、その既出witnessが`a (m-1)`
だったのはpinned配置で後方1ステップが確定していたおかげである。ただし分岐しても情報は失われず、
どちらの枝でも`target + 2m + 4`が軌道上に出現する。
