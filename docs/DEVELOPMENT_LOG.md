# 開発記録 — Recamán sequence Lean 4 formalization

> [!NOTE]
> 本書はappend-onlyの実装・研究ログである。途中時点の「残余」「次の作業」は歴史記録として
> 保存され、現在の指示ではない。current frontierは[`CURRENT_FRONTIER.md`](CURRENT_FRONTIER.md)、
> 証拠labelは[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv)を参照する。

この文書は各証明エポックで得られた詳細な技術記録である。
研究全体の過去要約は[研究結果レポート](RESEARCH_REPORT.md)、依存関係は
[証明地図](PROOF_MAP.md)、判断の時系列は[ロードマップ](ROADMAP.md)を参照すること。

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

## 2026-09-01 午後 sharp-kernel エポック

5系統並列（Lean形式化×3、紙上分析×1、exact probe×1）→統合を5ラウンド回し、
residual kernelの両枝を9+モジュールで精密化した。紙上分析（Round 4入力）は
`CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md`として保存し、その2つの推奨定理
（第二欠損値・rigid recurrence）を即日Lean化した。

**Lean上の要点**

- `TargetStreamBlockerUnbounded`: `Classical.choose`で`hstream.2`から時系列chainを再帰構成する際、
  存在命題を`Nat × Nat × Nat`の単一∃へ先に整形してからchoose/choose_specを当てると滑らか。
  chainのfinal time単調性→単射性→`Fin (B+2)`制限→`exists_blocker_gt_of_many`の合成で鳩の巣が閉じる。
- `TargetStreamUpwardResets`: blocker値の`Nat.strongRecOn`。非reset枝では`a s₂ < blocker₁`と
  `entry_eq_blocker_add_length`から`blocker₂ < blocker₁`が出て降下が止まる。
- `EventualHighCorridorStructure`: 純加算rayの反証は「ray値がpre-ray hull `upperTri M`を追い越す」
  「ray内の隣接値は2以上離れる」「露出candidateは直前値-1」の3点で、witness時刻を
  `p = M + upperTri M + M + 2`と明示的に取る。`obtain ⟨p, hp⟩ : ∃ p, p = ...`でopaque化するとomegaが安定。
- `NoDoubleAdditionRun`: 減算直後の加算2連の次candidateは
  `a(n) - (n+1) + (n+2) + (n+3) - (n+4) = a(n)`で減算前の値に正確に戻る。probeの発見を即日Lean化。
- 統合時の再検証で問題は0件。全6モジュールとも初回`lake env lean`通過だった。

**probeの要点（1e9）**: 加算run長histogramは`1: 499935267, 2: 0, 3: 11957, 4: 6012, 5: 951, 6: 13`。
長さ2の空白が`NoDoubleAdditionRun`の発見源。cone-exterior率は毎decade約43%で定常、
low-candidate stepは毎decade再入しつつ頻度7e-8まで希薄化、mexは1355で1e6〜1e9の間凍結。

**残余の現在形**: B枝はreset repayment予想（STOPPED中）のみ。A枝は自給自足供給窓の無限持続を
排除する入力探し。詳細は`docs/PARALLEL_SPRINT_2026-09-01_AFTERNOON.md`。

## 2026-08-31 target-comb macro エポック

descending fresh combを時間順のmacro頂点として接続した。単純なterminal blocker単調減少は20M scanの
20個のupward resetで反証されたが、fresh intervalのfirst-occurrence性から次のexact二分法はLeanで通った。

```text
nextEntry < previousBlocker  または  previousBlocker < nextBlocker
```

従って下降辺では次fresh interval全体が旧blockerより下にあり、上昇辺ではblocker自体が旧値を越える。
intervalが旧blockerを跨ぐ第三形はない。

high-only excursionにはsigned excess `E_m(n)=a_n-(n+1)-m`を導入した。加算stepは`+n`、減算stepは
`-(n+2)`で、maximal high区間の全prefixはstrictなledger corridorを満たす。出口はlegal subtractionで、
直前余剰は`0<E_m(n)<n+2`である。ただしendpoint総和は既存ledger identityそのものであり、20Mでは
最小exit slack 1、最大window利用率99.9999%まで飽和した。uniform margin枝はここで停止した。

terminal blockerの初出transitionを完全分類した。legal subtraction起源ならolder predecessorはcomb entryより
上へstrict liftし、forced addition起源ならolder predecessorはblockerよりstrictに小さい。20Mの2,660 blocker中
1,260がsubtraction起源でlift違反0、2,655 macro辺中upward resetは20件で全てaddition起源だった。
次のgateは、upward resetのsubtraction起源を排除するか、value liftとfirst-time descentをlexicographic rankへ
統合することである。

### 幅広macro監査

reset provenance以外の可能性を、first-occurrence ancestry、値interval traversal、record gap fluxへ広げた。
任意二つの時間順combのfresh intervalが完全に左右分離する`fresh_intervals_ordered`はLeanで成立した。

一方、20M exact scanではupward ancestryが最大60,651 hop、edge再利用7、threshold crossing再利用4となり、
短い／一回消費ancestryは成立しない。interval traversalもupwardで最大2,237本、downwardで最大71本の
既存intervalを飛び越え、stack disciplineではない。upward 20件が全てglobal right recordという経験則だけが
残ったが、record gap 17,820,564のうち9,518,181は20M時点でも未訪問であり、fresh intervalだけの閉じた
保存則にはならない。次の限定枝をright-recordのcausal証明とhigh-reservoir込みgap fluxへ更新した。

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

### 第八十五ラウンド：精密版頂点定理の完成と左枝の非自明性

精密版outcomeの頂点への伝播が全8段完了した。新しい頂点定理
`LeastMissingTarget.refinedSemanticEdge_or_flooredCore`は、左枝がpermanent-tail証明書を保持する
`RefinedSemanticEdge`、右枝が`32 ≤ crossingTime ∧ 19 ≤ target`の固定点coreである。旧
`semantic_or_flooredCore`を二点で置き換えた形になる。写経が必要だったのは段5のhorizon評価（約25行）と
段7のanchor gap強帰納（約55行）だけで、`TerminalChronologyHistoryProgress`の強化がsource-freeだったため
arity追随は一切発生しなかった。

**新しい左枝が捏造不能であることは一行で示せた。** `RefinedSemanticEdge`の二つのコンストラクタはどちらも
permanent-tail証明書を保持しているので、`¬ ∃ t, a t = target`をそれ単独で含む
（`RefinedSemanticEdge.target_missing`）。したがって`∀ target, 0 < target → ∃ start, RefinedSemanticEdge`は
`target = 1`で即座に反証され、`probe_refinedDomainEdge_of_pos`と同型の攻撃は構造的に不可能である。
本日三度踏んだ空虚化の罠を、四度目で初めて形式的に閉じたことになる。

残る留保を明示する。排除したのは「`0 < target`からの導出」であり、「`LeastMissingTarget`から無条件に出るか」は
排除していない。手で追う限りそれは`mounted_crossing`の`a crossingTime < mountedParent.anchorParent`という
実軌道のanchor下降を作ることに帰着し、固定点解析が現に戦っている内容そのものなので無料である可能性は低い。
ただし出せてしまえば右枝が到達不能になるので、次エポックで一度専任で当てる価値がある。最悪でも今回の
精密化は純利得である。旧左枝は情報量ゼロだったが、新左枝は少なくともtargetの欠損を含む。

### 第八十六ラウンド：敵対的再検査の二巡目（空虚化ゼロ）

第八十二〜八十五ラウンドの成果を再検査した。**今回は空虚化・自明化の検出がゼロ**である（一巡目は3件）。

`TailFixedPointCore`を伴う右枝は実際に居住する。target 50・clock 32で`a 32 = 46 < 50 ≤ 79 = a 33`が
強制加算のstraddleをなし、`node_reproduction`も`⟨0, 46, .normal, 46⟩`で成立する（5フィールドすべて`decide`）。
したがって「右枝が居住不能で床定理が空虚に真」ではない。`landing_cursor`の空虚性も否定された。
床`32 ≤ bound`の導出でも、cursorの第5条項`∀ witness, a witness ≤ target → witness < tailStart`が
`hlow 131`から`131 < tailStart`を出す一点で実際に効いており、自由に得られる情報ではない。

`orbitReadyNormalNonCrossingStep`は真に仮定ゼロで、`OrbitReadyDirectRefined`の強化でも既存の強さは
失われていないことを確認した（強い版が新名、正準名が弱いままという命名の問題のみ）。
`surjective_of_targetTailReturn`は`all_targetTailReturn_implies_surjective`より直接的だが強くはない。
∀レベルで`(∀ target, TargetTailReturnHypothesis target) ↔ 全射性`が成立する。

`PinnedTailMinimumConfiguration`は無条件反証が不可能で、居住性は全射性予想と同じ深さで開いている。
ただしdocsの「候補2438個」は`target_missing`を含まない四条件の数であって住人の数ではないので、
誤読を招かないよう訂正した。数値調査（`f < 60000`）では四条件を満たす候補310個のうち232個が
targetの実出現により排除され、残る78個も400k項の範囲でwitnessが見つからないだけである。
障害は候補が生き残ることではなく、witness時刻に一様上界がないことである。

副産物として構造的リードが一つ出た。候補310個のうち**189個で`a (f - 2) = target`**が成立し、
`elim_of_predecessor_witness`がwitness `f - 2`で発火する。全域では成り立たないが、
`pinned_forward_orbit`が前方3ステップを決定しているのと対になる後方2ステップの決定が取れれば、
pinned枝の6割強が構造的に落ちる。

### 第八十七ラウンド：壁の構造的確定と最小修正の特定

三度当たった壁を正面から攻め、**上界が存在しない理由を定理にした**。`MissingStrictAboveTail target s`の
3フィールドはすべて`s`について上方閉なので、任意のboundを超えるvalidな`tailStart`が存在する。証明書の
horizon条件も全部上方閉である。特に`horizon_strictly_above`は`budget_zero`から自動的に従うことが判明し、
独立フィールドである必要がないと分かった。したがって`tailStart ≤ g(target)`型の定理は現行の証明書からは
原理的に導出不可能である。`TerminalHistoryCursor`も方向が逆で、内容は`strictly_above`の対偶と同値な下界に
すぎなかった。

**最小修正も特定した。** `tail_minimal : ∀ s, MissingStrictAboveTail target s → tailStart ≤ s`の1本を足せば
よい。validなtail startの集合はℕの空でない上方閉集合なので最小元を持ち、構築時に自明に満たせる。これで
`target < tailStart ≤ bound + 1`の両側評価が成立する。証明書は既にcoverageを二箇所で持っている。

そのうえで残る唯一の未知量はcoverage time自身の上界、すなわち「target未満の値が最後に初出する時刻`n₀`」に
対する`n₀ ≤ g(target)`である。これは新しい組合せ論的命題であり、計数路線の本当の核心である。

副産物の`covered_forces_above`は独立に強い道具である。あるレベル未満の値が全部既出になれば、時計が
そのレベルとcoverage時刻の両方を過ぎた後は軌道は二度とそのレベル未満へ戻れない（戻れば値が自分より
大きい時刻で再出現することになり、減算のfreshnessと加算のovershootが両方それを禁じる）。tailの存在自体が
これで説明できる。targetに限らず任意のレベルで使えるので、prefix-successor coverage側とも噛み合うはずである。

### 第八十八ラウンド：pinned配置の後方2ステップ決定

敵対的検査が副産物として出した観察（候補310個のうち189個で`a (f - 2) = target`）を定理にした。
`pinned_forward_orbit`の鏡像として**後方2ステップを完全決定**し、4通りの符号パターンへ分解した。

| `f`への遷移 | `f-1`への遷移 | `a (f-1)` | `a (f-2)` | 件数 | 判定 |
|---|---|---|---|---|---|
| 加算 | 減算 | `target + 1 - f` | `target` | 189 | **排除** |
| 減算 | 加算 | `target + 1 + f` | `target + 2` | 88 | 残存 |
| 加算 | 加算 | `target + 1 - f` | `target + 2 - 2f` | 21 | 残存 |
| 減算 | 減算 | `target + 1 + f` | `target + 2f` | 12 | 残存 |

第1行では`a (f-2) = a (f-1) + (f-1) = target`が代数的に強制され、targetの欠損と直接矛盾する
（`not_add_then_subtract`）。**189個の発火は偶然ではなく符号パターンで完全に決定されていた**ことになる。
数値切り分けと代数が一件も食い違わなかった。逆に言えばpinned配置は「加算のあと減算」という後方パターンを
取れないという新しい構造的制約を負う。

第2行（88件）が次の攻撃点である。この行では最小値`target + 2`が`f-2`に既出なので、`value_no_late_recurrence`
により最小時刻`m`が`target + 2`を超えれば矛盾する。replay側は既に無条件の`target < tailStart ≤ m`を持って
いるので、差は2だけである。詰まらない場合でも`middle_row_pins_minimum_time`により
`m ∈ {target+1, target+2}`の2点に釘付けされる。第3行・第4行は`a (f-2)`がtargetから`2f-2`／`2f`離れており
この道具では届かない。

### 第八十九ラウンド：tail startの両側評価（既存モジュール無編集）

前ラウンドで特定した最小修正を、既存モジュールを一行も編集せずに達成した。最小性を証明書のフィールドに
しなくても「validなtail start全体の最小元を取る」定理を一本立てれば済むからである。`Nat.find`はMathlabなしの
この環境に無いので、decidabilityを要求しない有界帰納法による最小元の存在定理を自前で書いた。結果として
両側評価`target ≤ least ≤ bound + 1`が成立する。副産物は`a (least - 1) < target`と、`target ≤ s`が任意の
valid tail startについて成立すること（前ラウンドの一般化）である。

詰まりはまだ動かない。両側評価は`least`についてのもので、証明書の`source.tailStart`に対しては下界しか
与えないからである。ただし`least_tailStart_minimumCertificate`によりtail最小値の機構一式を`least`の上に
建て直せることは証明済みで、建て直せば残る未知量はcoverage timeの上界ひとつになる。tail startはもはや
自由パラメータではない。

### 第九十ラウンド：精密版頂点定理の二択が実質的な分岐であることの確定

「左枝が`LeastMissingTarget`から無条件に出てしまわないか」という最後の高リスク課題に決着をつけた。
**出ない。** 左枝の`mounted_crossing`経路が要求するのは単一の算術不等式`a crossingTime < parent.anchorParent`
だけだが、これは全parentでは成立し得ない。anchor下降が取れると`landingReadyCrossing`でready crossingになり、
`installReadyCrossing`が同じtail・同じ最小時刻の証明書をanchorがより小さい新しい親の上に再生産するので、
反復すると自然数の無限狭義降下列ができる。証明書が無料で差し出す唯一の候補は親自身のcrossingで、
`a crossingTime = parent.anchorParent`と狭義不等号をちょうど0だけ外す。

さらに、**左枝はpermanent-above tailをまるごと持ち歩いている**ので、左枝単独で`TargetTailReturnHypothesis`と
`CrossingRefinedStepHypothesis`の両方が反証される。左枝は楽な逃げ道ではなく右枝と同じ大域的障害を背負って
おり、どちらの枝に落ちても残る義務は同一の一点（crossing局所step）である。したがって本日の床上げと
landing前置界の輸送は大域的にも無駄ではなかった。

`discharge_step`経路については形式的な不可能性証明は得ていない。各枝が`terminalFiniteClosedOutcome`の
分岐出力を要求し、他の分岐に落ちる可能性を排除する手段がないためである。ここが残る唯一の未閉鎖点である。

### 第九十一ラウンド：pinned後方形の二択化（中段行の排除）

pinned配置の後方2ステップ4通りのうち、残っていた第2行（両方混合の`(減算, 加算)`、88件）を排除した。
鍵は鳩の巣の精密化である。既存の`coveredBelowCount k n ≤ n + 1`は時刻0..nの各々に高々1レベルを課金するが、
**値が`k`以上の時刻は1レベルも埋めない**。中段行では`a (f-2) = target + 2`と`a (f-1) = target + f + 1`が
どちらも`target + 2`以上でtail開始前にあるので、pre-tail時刻のうち2つが遊んでいる。これを差し引くと
必要なpre-tail時刻数が2増え、差の2がちょうど埋まる（`coveredBelowCount_two_above`、
`target_add_three_le_tailStart`）。

しかも`a (base+1)`についての仮定は不要だった。`backward_trichotomy`の3行のうち`a base = target + 2`を
出せるのは中段行だけで、その行は同時に`a (base+1) = target + base + 3`を確定させるからである。
**中段行は自分自身の代数から2つのidle時刻を供給して自滅する。**

結果、`f`手前の2ステップは「両方減算」か「両方加算」のどちらかしかない（`pinned_backward_dichotomy`）。
混合形は2つとも死んだ——`(加算, 減算)`は第八十八ラウンドの`not_add_then_subtract`（189件）、
`(減算, 加算)`は今回の計数精密化（88件）である。数値上の残余は`f < 60000`で12件（両方減算）＋
21件（両方加算）＝33件、当初310件の約11%になった。

この`coveredBelowCount_two_above`は、本日の計数路線で**初めて上界側で仕事をした**道具である。
これまで計数は常に`tailStart`の下界しか生まなかった。

### 第九十二ラウンド：pinned残り2行の分離と限界の確定

pinned後方4パターンの残り2行を精査した。行そのものの排除には至らなかったが、両者の性質がはっきり分かれた。

**第1行（両方減算、12件相当）**では`coveredBelowCount_two_above`がそのまま適用でき、
`target + 3 ≤ tailStart`が出る（`a (f-1) = target + f + 1`と`a (f-2) = target + 2f`がどちらも
`target + 2`以上のため）。ただしlate recurrenceの的がないので行は生き残る。閉じるためのフックとして
`firstRow_forbids_late_repeat`を用意した。

**第3行（両方加算、21件相当）は計数では原理的に落ちない。** `covered_forces_above`は「レベル未満が
全部既出になったbound以降」でしか発火しないが、この配置では`a (f+1) = target - f`が時刻`f+1`のfresh初出
なのでboundは必ず`f+1`以上であり、`f-1`・`f-2`は射程外である。レベルを`target + 2`へ上げる道もtargetが
欠損しているため前提が成立しない。さらに`lastRow_values_below_target`が示すとおり後方2値はどちらも
target未満なので、鳩の巣の精密化はむしろsub-target値をpre-tailに2つ増やす方向に働く。
**第2行が自滅した構図の完全な裏返しである。**

代わりに第3行の残余を型で固定した。この行は時刻`f`への遷移が強制加算であることを自分の等式から強制し
（`lastRow_forced_addition`）、その原因は値の小ささではなく既出性でしかありえないので、
`target - 2f + 1`が時刻`f-1`までに出現していることが確定する（`lastRow_blocked_witness`）。
一方`a (f-2) = target - 2f + 2`はその1つ上の値で時刻`f-2`にある。**隣接する2値が`f-1`以前に揃っている**
という強い局所条件であり、`f ≥ 6`と重ねれば構造的矛盾に届く可能性がある。

pinned枝の総括：当初310件のうち277件（89.4%）を構造的に排除し、残る33件は2つの明示された残余へ縮約された。


### 第九十三ラウンド：coverage timeへの帰着完了

計数路線の未知量を一本に絞り切った。`CoversBelow target n`（target未満の全値が時刻`n`までに既出）を定義し、
その最小元`coverage`について次を証明した。

- 上方閉なので最小元だけが情報を持つ（tail startと同じ構図）。
- **`least = coverage + 1`が無条件で成立**（`least_tailStart_eq_coverage_succ_final`）。
  tail startはもはや独立した量ではなく、coverage timeの+1である。
- 下界`target ≤ coverage`。鳩の巣は`target ≤ coverage + 1`までしか出ないが、時刻24で`a 24 = a 20`の再訪が
  起きることをkernel計算で押さえ、そこで1スロット失われることを使って鋭化した（`target ≥ 25`が条件、
  replay floor 114で自動充足）。
- coverage timeはtarget未満の値の初出時刻であり、最小性は「最後の未被覆レベルがちょうどそのステップで
  供給される」ことを意味する。

したがって残るのは`coverage ≤ g(target)`ただ一つである。**足りない補題も precise に特定した**——
「`¬ CoversBelow target n`ならば`n`から高々`h(target)`ステップ以内に`a t < target`となる`t`が存在する」
という return-frequency lemma である。接続部品`least_tailStart_le_of_coverage_bound`は用意済みで、
`CoversBelow target g`を仮定として受け取り`least ≤ g + 1`を返す。

**なぜ現行の道具で出ないかも構造的に確定した。** 鳩の巣・`covered_forces_above`・`a n ≤ upperTri n`は
すべて「被覆レベル数の上界」を与えるもので、それはcoverage timeの下界にしかならない。
`a n ≤ upperTri n`も軌道がどれだけ高くなれるかを抑えるだけで「いつ降りてくるか」を一切言わない。
上界には「降下の頻度」という逆向きの命題が要り、現行のツールキットには含まれていない。


### 第九十四ラウンド：計数路線の閉鎖

return-frequency lemmaを攻めた結果、予想より鋭い結論が出た。**この補題はcoverage time上界への足がかりでは
なく、coverage time上界そのものである。** 両者は同値であり、片方を証明することは他方を証明することと
完全に同じである（`returnFrequency_iff_coverage`）。tail startの上界も同じ命題である
（`coverage_le_of_tailStart_bound`と既存の`least_tailStart_le_of_coverage_bound`が相互導出）。
したがって計数路線が手持ちの材料からどれかを作り出すことはできない。**計数路線は閉じた。**

失敗モードは完全に特徴づけられた。軌道がある時刻`bound`以降ずっとtarget以上に落ち着いたなら、その時点で
未被覆のtarget未満の値は永遠に未被覆である（`uncovered_at_tail_never_occurs`）。`bound`以降は軌道が
高すぎて供給できず、`bound`より前の履歴は確定しているからである。よって「降りてこない」状態が続きうるのは
target未満に第二の欠損値が存在するときだけであり、least-missing-targetの下ではその失敗モードは空である
（`returnFrequency_failure_mode_empty`）。**return-frequencyは定性的にはタダで成立する。**
未解決なのは定量版だけで、それが上の同値である。

定量側の切り分けも行った。`drop_le_upperTri_gap`（1ステップの変化量はクロックちょうどなので落下は三角数差を
超えない）から復帰時刻の下界`return_time_lower_bound`が出る。既存ツールが出せるのは常にこの向きである。
上界に必要なのは「ブロックの累積コスト」で、`forced_addition_run_defects`（強制加算の連鎖は狭義単調増加の
既出値族を要求する）が出発点になるが、概算すると必要条件が`a t ≲ t²/2`に帰着し`a_le_upperTri`から常に
成立するため矛盾にならない。加算の連鎖は任意に長くなりうる。

次は計数以外の入力へ切り替えるのが妥当である。候補は軌道の局所構造からの上界、semantic phase側の別ルート、
pinned配置のような具体構造の潰し込みである。


### 第九十五ラウンド：pinned第3行の窓縮小と、必要な道具の同定

第3行（両方加算、21件相当）の隣接witness条件を追った。窓は`2f + 3 ≤ target ≤ upperTri(f-3) + 2f - 1`まで
縮み、`f ≥ 6`も確定した（窓だけからは`f ≥ 5`までで、`f = 5`は`a 5 = 7`のkernel計算で潰した）。
しかし上端は`f²/2`オーダー、下端は`2f`オーダーなので**この方向の改善を何回積んでも交差しない**。

`a_succ_ne_of_seen`と`value_no_late_recurrence`は使えない。どちらも「値 < 時刻」を要求するが、第3行の
witness値は`target - 2f + 1`、時刻は`w ≤ f-3`で、実測21件すべてで値が時刻を大きく上回る（例：`f = 134`で
値135に対し`w = 126`）。late recurrenceの向きが逆である。代わりに効いたのは`a_le_upperTri`で、
これが窓の上端を縮める。

計数も効かない。第3行がpre-tailに供給する値はすべてtarget未満で、`coveredBelowCount`の被覆レベルに
そのまま数えられる。鳩の巣の精密化が数えるのは「値がレベル以上の遊休時刻」なので、第3行はむしろ供給側を
増やす方向に働く。第2行を殺した構図の完全な裏返しである。

**足りないのは早期witnessの追加ではない。** 強制加算はそのたびに新しい早期witnessを供給するので、
この連鎖は`ReplayWitnessDescent`で否定的に決着したblocked降下とまったく同じ形で発散する。必要なのは
「区間`[0, f-1]`に値が`V`以上の時刻は高々何個か」型の**密度側の上界**（`coveredBelowCount_two_above`の
双対）である。それが個数上限を与えれば、強制加算の連鎖が要求するwitness数と衝突して第3行が落ちる。


### 第九十六ラウンド：密度側の上界の汎用化

二つの前線が同時に必要とした「区間`[0,n]`に値が`V`以上の時刻は高々何個か」を汎用定理として構成した。
核は競合恒等式である。

```
coveredBelowCount level n + highCount level n ≤ n + 1
```

値が`level`以上の時刻は`level`未満のレベルを1つも埋めず、値が`level`未満の時刻は高々1レベルしか
新たに埋めない。この2本を時刻についての帰納法に載せるだけで出る。**被覆レベルと高値時刻が同じ時間予算を
奪い合う**という見方が本質だった。レベル未満が全部既出なら左項が`level`に確定するので
`highCount V n ≤ n + 1 - V`という真の密度上界になる。

これにより第九十一ラウンドの手作業版（2つの遊休時刻を名指しして望遠鏡で繋ぐ）が
**`highCount ≥ 2`の特殊ケース**であることが定理として確定し（`coveredBelowCount_two_above_by_density`）、
任意個数へ一般化された。汎用形`preTail_highCount_bound`は「replayのpre-tail領域にはtarget以上の値を
載せた時刻が高々`tailStart - target`個しか入らない」であり、高値時刻を`k`個名指しすれば
`target + k ≤ tailStart`が即座に出る。第1行の分離もこの一般原理から再導出できた。

**第3行には効かない。** その後方2値`target - f + 1`と`target - 2f + 2`はどちらもtarget未満なので
高値時刻に該当せず、第3行がpre-tailに持つ高値時刻はclock `f`の1つだけである。密度からは既知の
`target < tailStart`しか出ない（`lastRow_density_gives_only_one`）。次に要るのは「高値時刻の個数」ではなく
「小さい時刻に載る値の大きさ」型の制約で、`a t ≤ upperTri t`を複数時刻について同時に使う不等式が候補だが、
Recamánは単調でないため素朴な形は成立せず新しい着想が要る。


### 第九十七ラウンド：減算台帳——同値の輪の外からの最初の注入

計数路線の閉鎖（第九十四ラウンド）は「残余がすべて目標と同値になり、枠組み内の組み替えでは一歩も進まない」
ことを意味した。進捗はcertificateインターフェースに載っていない新しい動力学的情報の注入でしかあり得ない。
その最初の一本として、軌道の±分解そのものを情報化した。

`subSum t`を「時刻tまでに減算が起きたクロックの総和」とすると、**厳密恒等式**

```
a t + 2 · subSum t = upperTri t
```

が帰納法一発で成り立つ（`ledger_identity`）。加算はsubSum不変で両辺にt+1が乗り、減算はsubSumがt+1増えて
左辺のaがt+1減る。帰結は三系統ある。

**パリティ不変量**：`(a t + upperTri t) % 2 = 0`。`upperTri`の偶奇は周期4なので、任意の値の出現時刻は
mod 4で2剰余類に制限される（偶値は`t % 4 ∈ {0, 3}`、奇値は`{1, 2}`）。第九十五ラウンドの実測
「witnessオフセットが常に4の倍数」はこの周期4構造の現れだった。実際に第3行へ当てると、隣接2値のパリティが
相補になる（`adjacent_occurrence_opposite_parity`）ため witness は `w + 2 ≤ base` へ1締まり、窓の上端が
`upperTri (base − 1)`から`upperTri (base − 2)`へ下がった。O(1)-tightだった解析に対する実際のO(1)改善である。

**後方伝播**：`subSum`の単調性から`w ≤ t`で`a t + upperTri w ≤ a w + upperTri t`。高い値は過去の高さを
強制する——`covered_forces_above`（被覆は未来の高さを強制）のちょうど双対で、Nat引き算を避けた加法形で書ける。

**供給側カウンタ**：合法減算の着地はfreshなので減算着地は全て相異なる値であり、
`upperTri (subCount t) ≤ subSum t ≤ t · subCount t`の両側挟みが成立する。これまでの計数が
「時間予算の消費側」だけを数えていたのに対し、これは値の供給側を数える最初のカウンタである。

数値的裏付け：恒等式・パリティ・後方伝播はt < 2×10⁵で全数検証済み。減算密度は0.500ちょうどに収束する
（`a t = o(t²)`である限り必然）。


### 2026-08-29 夕方セッション振り返り：三度の空虚化と、その後

第七十〜第九十六ラウンド（27ラウンド、31コミット、新規27モジュール）を終えての評価を記す。
このセッションの性格は前半セッションとはっきり異なった。前半が「残余を縮約する」セッションだったのに対し、
後半は**「縮約したつもりの残余が実は空だったことを三度発見し、そのたびに作り直す」**セッションだった。

**発見された空虚化は三つである。** (1) 頂点定理のsemantic枝が`0 < target`だけから導出できた。
`PhaseSearchProgress`が四成分lex順に過ぎず`stepParent`が存在量化されているだけなので、anchorを+1した親を
常に捏造できる。約90モジュールの成果が最終目標に接続していなかったことになる。(2) その修復として作った
精密版の**忘却形**`RefinedDomainEdge`もまた`0 < target`から直接導出できた。canonical start自身がrefined
nodeなので解析なしに作れる。(3) 第七十ラウンドで「残余義務を型で固定した」と記録した条件付き定理の仮定が
実軌道で偽だった（`BlockedFirstOccurrence 13 6`）。定理は空虚に真であり、位置づけは撤回した。

**この三つはいずれも敵対的検査によって見つかった。** (1)は証明側と監査側が独立に同時到達、(2)は伝播作業の
途中で設計変更の必要として、(3)は専任の敵対的検査で。通常の証明作業では見つからなかったはずである。
そこから引くべき運用上の教訓は明確で、ROADMAPにも書いた——**新しいoutcome型を作ったら、必ず
「無料ルート探し」を実際に証明を試みる形で走らせること。生成証明書を保持しない忘却形は必ず捏造される。**

**四度目で初めて閉じた。** `RefinedSemanticEdge`は両コンストラクタがpermanent-tail証明書を保持するので
`¬ ∃ t, a t = target`を単独で含み、`target = 1`で即座に反証できる。さらに左枝の`mounted_crossing`経路が
`LeastMissingTarget`から無料で出ないことも、`installReadyCrossing`によるanchorの無限降下で証明した。
**精密版頂点定理の二択は実質的な分岐である。** そして左枝に落ちても`TargetTailReturnHypothesis`と
`CrossingRefinedStepHypothesis`は反証されるので、両枝は同一の一点（crossing局所step）へ収束する。

**前向きの成果も相応にある。** 頂点の固定点枝の床が無条件`32 ≤ clock`・`19 ≤ target`になった
（旧`18 ≤ clock ∨ target = 19`）。crossing readiness橋が無仮定で完成し、大域残余が仮定一本へ純化された
（ただし同仮定は全射性と同値であり、減ったのは足場の量であって難しさではない）。計数枠組み
`coveredBelowCount`を新設し、無条件`target < tailStart`と両側評価`target ≤ least ≤ bound + 1`を得た。
pinned配置の後方2ステップを完全決定し、混合形2通りを排除した。

**壁も三つ明確になった。** (a) 床上げ機構には構造的天井`clock ≈ 5.4×10⁴`があり、kernel射程を無限に
伸ばしてもclock 10⁶までの65%は消せない（数値実験）。(b) `tailStart`に上界が存在しないことは
構造的に証明された（全フィールドが上方閉）。(c) 二連減算枝の排除はpre-tail領域への下界なしには
原理的に不可能である。(a)は投資打ち切りの根拠になり、(b)(c)は最小修正の特定へ繋がった。

**残る未知量は一つに絞られ、そして計数路線は閉じた。** 計数の未知量は`tailStart`（無限の自由度）→
`least`（正準化）→ `least = coverage + 1`（完全決定）と潰れ、残るのはcoverage timeの上界だけになった。
ところがその上界は、return-frequency lemmaともtail startの上界とも**互いに同値**である
（`returnFrequency_iff_coverage`）。計数・鳩の巣・`upperTri`はいずれも下界しか生まないので、
**この路線が自前の材料からどれかを作り出すことはできない**。到達点を一言でいえば「計数でできることは
すべてやり切り、できないことの範囲も証明した」である。次は計数以外の入力へ切り替える。

なお失敗モードは完全に特徴づけられた。軌道が`bound`以降ずっとtarget以上に落ち着いたら、その時点で未被覆の
target未満の値は永遠に未被覆である。よって「降りてこない」状態が続くのは第二の欠損値がある場合だけで、
least-missing-targetの下ではその失敗モードは空——**return-frequencyは定性的にはタダで成立し、
未解決なのは定量版だけ**である。この切り分け自体が成果である。

**運営面の反省。** コミット粒度を一度崩した。docs訂正のコミットに`git add -A docs/`で未追跡の
`docs/human-proofs/`（142ファイル）を巻き込み、後から`viewer/`を追加して整合を取る羽目になった。
並行セッションの未コミット作業と自分の変更が同一ファイルで絡んだ場面もあり、index経由の外科的staging
（HEAD版＋自分の差分だけをstage）で凌いだが、本来は棲み分けを先に固めるべきだった。
一方でエージェントの「型検査を通った」という自己申告を統合時に必ず再検証する運用は機能した。
実際に一度、提出されたファイルが通らず（並行編集で定義が変わっていたため）、追跡して経過を記録できた。


### 第九十八ラウンド：least tail startによる証明書正準化

計数路線で未知量として残ったtail startに対し、存在する開始時刻の最小元を
証明書そのものに取り込んだ。この最小性は、直前時刻がまだ被覆しきっていないことと、
その次時刻から永久にtargetより上であることを同時に与える。鳩の巣計数と組み合わせると、
その直前時刻が最後のbelow-target初出であり、したがって

```
tailStart = coverage + 1
```

が厳密に得られた。境界は減算で新しいlowへ着地し、次の三時刻は強制加算、
直前の`missingBelowCount`はちょうど1である。これを`BoundaryCertificate`にまとめ、
元のdischarge parentへ再搭載した。

最も大きな成果はexact replayの消滅である。境界lowとparent anchorの比較は、
anchor dropならcertificate付きsemantic edge、anchor growthなら既存三成分rankの厳密降下を与える。
等号ならreplayはそのclockにおける値がclockより大きいことを要求するが、最後の
coverage lowは自分のclock以下なので矛盾する。この一点で、従来のreplay固定点、床、
pinned残余はcanonical経路の頂点から一度に消えた。well-foundedな`closedOutcome`は最終的に
history progressまたは`RefinedSemanticEdge`のみを返す。

ここで重要なのは、全射性が証明されたのではないことである。固定点は消えたが、
残った二枝はどちらも本質的な履歴情報を含む。次の大域証明はこの二枝の共通降下量を
作る必要がある。


### 第九十九ラウンド：深部認証traceと境界の一段後方分類

最小tail境界に現れる小さな例外を消すため、balanced trace生成器を深部入力に対応させた。
生成物は圧縮されたbranch bitとbalanced treeからなり、最終定理はLean kernelが履歴付きの
Recamán stepを再計算する。認証したendpointは

```
a 99734  = 19
a 181653 = 61
```

である。99,734-step版の単体型検査は約291秒、181,653-step版はさらに重い。
これらは経験データを定理として信用したのではなく、小さいcheckerとkernel reductionのみを
信頼する構成である。

深部値を最小tail境界に接続すると、すべての仮想的な最小未出目標に`62 ≤ target`、
最後の新規被覆lowに`61 ≤ a coverage`が得られる。これで`coverage = 131, low = 4`と
`coverage = 99734, low = 19`の両例外が消えた。

同時に、有限計算と独立に境界を一段後方へ読んだ。`coverage - 1`で減算できるなら、
境界へ入る一つ前の値は`low + 2*coverage - 1`で、高い値とlowは連続する二回の
fresh減算着地になる。減算できず`coverage ≤ low + 3`なら、`target`と`coverage`の
相対配置は厳密に6通りである。それ以外では`coverage - 2`に`low + 1`の初出valleyがあり、
`coverage - 3`時点の欠損budgetはちょうど2になる。

このパターンはそのまま深さ`d`へ一般化できた。各stageはclock、`low + d`の初出、
入射減算、targetより上の入射値、正確なbudget `d+1`を保持する。次のstageへ伸びないのは
高い減算前値が出るか、stage clockがstage lowの3以内へ入る場合だけである。
`low ≥ 61`を使えば61段反復でき、消費者向けには次の三形へ展開した。

1. 深さ61未満で明示的な高い減算前値が出る。
2. `coverage ≤ low + 183`。
3. 深さ61のstageが存在し、その直前の欠損budgetが62である。

さらに延長条件を最適化すると、`depth ≤ low`は十分条件にすぎず、正確な可用roomは
`low + coverage - target`であることが分かった。この最大深さでstageがまだ残るなら、clockの非負性から
`2 * room ≤ coverage`が必要になる。よって最大鏖も、明示的high枝、narrow由来のcoverage界、
この数値圧縮の三択に分解できる。

これは深部traceをさらに延ばすのではなく、有限な実軸道入力を反復可能な後方力学に
変換する新しい非計数路線である。

深部traceの重複チェックも避けられた。balanced treeの成功実行から右端leafの入力machineと
絶対clockを抽出し、leaf内の任意分割で中間machineを復元する汎用補題を追加した。
181,653-step証明の右端leafを11ステップ＋10ステップに分け、最後10個のbranch codeを
endpoint 61から逆算すると中間値は76に一意に決まる。これにより

```
a 181643 = 76
```

を新しい181,643-stepチェックなしで証明した。追加の型検査は約13秒で、別traceを
一からビルドする約25分に比べて大幅に安い。62〜75は実はclock 99以内に全て出現するため、
最小未出目標の下限は`77 ≤ target`へ上がった。boundary lowについては61自体は消えないが、
その場合は初出性とpermanent-above性の両方から`coverage = 181653`へ固定される。
したがって最終的な境界分類は

```
(coverage, low) = (181653, 61)  または  76 ≤ low
```

となった。

### 第百ラウンド：深部履歴mexと879への完全pin

値だけを検査していたbalanced trace終端に、bitsetの最小未出値を認証する
`verifiesBitsMex`とそのsoundnessを追加した。181,653-step traceを同じ小さなcheckerで
再評価し、次をLean kernelで証明した。

```
(∀ v < 879, v ∈ valuesThrough 181653) ∧
879 ∉ valuesThrough 181653
```

従って任意の仮想的な大域欠落値には無条件で`879 ≤ target`が成立する。さらに右端leafを
clock 181651/181652でも分割し、`a 181651 = 363366`、`a 181652 = 181714`とclock 181652の
合法減算を既存traceから復元した。sub-76境界は単なる数値例外ではなく、
`target = 879`、`coverage = 181653`、`low = 61`、直前二段が連続するfresh減算という
完全固定high-predecessor証明書になった。さらにmexの0〜878全既出情報とpermanent-above性を
使うと、879未満の境界lowはこの例外以外に存在できない。もう一方の境界枝は`low ≥ 879`であり、両方に
最大room後方構造三択が付随する。固定例外のroomは正確に180835で、その三択は深さ0の
high枝へ確定する。全射性自体は依然未証明で、次の有限的候補は経験的には
`a 328002 = 879`の認証だが、主残余はhistory progress / `RefinedSemanticEdge`の大域閉包である。

その後、source-free valley自身から完全なchronology edgeも抽出できた。境界直前の
`missingBelowCount`は1、境界時点は`CoversBelow`により0である。cursorにはclock
`coverage-1`、minimum/tailStartには`coverage+1`を選び、valley equationが値差1、
permanent-above性が全low witnessの時刻上限を与える。従って

```
TerminalChronologyHistoryProgress target coverage (coverage - 1)
```

が無条件に成立する。これはwell-founded relationの単一edgeであって無限降下ではないため、
さらにboundary low自身のfirst occurrenceと即時first upcrossingを組み合わせ、cursor込みの
`PermanentTailTerminalAnchoredOutcome`とrefined版へ直接搭載した。さらにsource-preserving
boundaryでは元combined parentのready crossingを使い、`RefinedTerminalMountedOutcome`まで
再搭載した。全射性はまだ従わない。次の課題は、この特定mounted branchを既存iterationの
strict progressへ固定し、等anchor時の残余をcanonical rank解析と統合することである。

### 第百一ラウンド：328002-step証明書の限界測定

次の有限候補`a 328002 = 879`について、既存generatorから5,126 leaf、1,634,667 byteの
決定的Lean sourceを再生成した。外部exact-history replayの終値879、FNV-1a
`538690d9af3ec36d`、生成sourceのSHA-256
`0bb7adc98493337a3f09e977d29a4645bd86d093b73014a3e22a5fc1ce4d7074`を固定した。
しかし既存の単一`traceBits_checked`をLeanで検査すると、witness不一致ではなく
`whnf`で20,000,000 heartbeats上限に達した。従ってこの等式はまだLean定理として
取り込んでいない。次の有限認証作業は、単純に上限を増やすより、traceを認証済み
checkpointへ分割して各kernel計算を小さくすることである。

### 第百二ラウンド：canonical閉包のstrategy gate

全射性への距離だけを基準にcanonical history／mounted路線を再評価した。canonical edgeは
`missingBelowCount target (coverage-1)=1`から`missingBelowCount target coverage=0`へ進むが、
この到着点から同じ`TerminalHistoryBudgetDrop`をさらに進むことは算術的に不可能である。
強化版`TerminalChronologyHistoryProgress`も第一成分に同じdropを含むため同様にterminalである。
この二つの非存在をLeanで定理化した。従って単一edgeとwell-foundednessを組み合わせても
矛盾は出ず、履歴閉包案は棄却される。

また`LeastMissingCoverageValleyCertificate`は`target_missing`と有限`CoversBelow`を保持するため、
そこから`LeastMissingTarget`を復元できる。逆向きは既存のcanonical valley構成であり、両者の
同値もLeanで証明した。正準化は有用な構造抽出だが、論理的には反例仮定を弱めていない。

mounted equal-anchorはcanonical coverage crossingを親として再選択するnode自己再現であり、
既存rankだけからstrict progressにする根拠はない。よって深部trace、有限mex床、固定段数の
後方反復、outcome/rank interface追加を主戦略として停止する。再開条件はpermanent-above tailを
直接破る新しい軌道不変量を紙上で得ることとする。

### 第百三ラウンド：研究portfolioの縮退

主残余との論理距離を基準に全路線を再分類した。tail return／crossing oracleはtarget出現と同値、
semantic consumerも同値、fixed-point床・deep mex・pinned列挙は有限下限、coverage／return-frequency／
tail-start上界の計数路線は相互同値、earlier-smaller `regenerate`は仮定が偽である。従ってこれらを
全射性の主戦略から外した。semantic parent-bindingはformalization品質の修正としては残るが、証明研究の
優先対象にはしない。

残す候補は`SubtractionLedger`だけである。ただしparityによる有限帯削減は停止し、厳密恒等式を
tail最小値区間の重み付き±pathとforced-addition blockerの供給／消費収支へ使う。簡易的な実軌道確認では
500万step時点で減算回数比0.499997、減算clock質量比0.499999352、連続加算・連続減算はいずれも最大5だった。
これは証明入力ではないが、質量収支を調べる動機になる。一方positive blockerは同じ値が最大13回再利用され、
forced additionのうちnonpositive candidateも多いため、単純な一対一blocker injectionは成立しない。
継続条件は、これら二つの漏れを含む一様な区間不等式を紙上で得ることとした。

### 第百四ラウンド：並列portfolio監査

ledger、blocker償却、有限反例モデルを独立に監査し、途中で浮上した高商負potential障壁、
diagonal predecessor、interval Hall matchingも追加調査した。

最小permanent-above tail start `s` とtail minimum時刻`t`を結合すると

```
target + 2 ≤ a t < 2 * t
```

が得られ、minimum checkpointの座標は`q ≤ 1`、potentialは`G ≥ -1`へ落ちる。ledgerも
`2 * subSum t`を`upperTri t`の線形誤差内に固定する。一方、tail-minimum区間で減算が半数以上、
または高さ差が区間長に比例するという自然な強化は実軌道反例で棄却された。

positive blockerの固定頂点容量とnonpositive resetへの一対一対応も反例で棄却した。唯一残った
subtraction-mass interval matchingは、同じlast occurrenceを共有する後続jobを互いに素なannulusへ
分解できる。異なるepisodeのfirst-job congestionに対するHall条件だけが残り、短期スプリント一回に
限定して継続する。

自由な初期履歴を許す抽象`Basic.step`状態では、履歴サイズ・軌道上界・parity・個別ledger条件を
満たしながら任意長のall-forced tailを作れる明示族を得た。従って局所状態と静的履歴条件だけから
一様returnを出す路線は停止する。実prefixとの差は履歴の因果的到達可能性だけである。

10億stepまで成立する経験的候補`q ≥ 6 → G ≥ 0`は、最小反例がregular forced additionであるところ
まで縮約できた。`q=6`は21本のaffine chordへ有限化できるが、高商側には幅`2q-1`の無限stripが残り、
独立本命にはならない。diagonal predecessorも一bitのbranchへ縮んだが、full tail certificateは
排除したいearly branchをむしろ要求し、既存APIと矛盾しない。

次周期はlow-quotient minimum、first-job Hall congestion、`q=6` affine chordの三本だけを扱う。
詳細なスコア、反例、停止条件は`docs/PARALLEL_RESEARCH_2026-08-30.md`に分離した。

### 第百五ラウンド：low-quotient形式化、exact Hall定数、H6停止

前ラウンドで選んだ三本を並列に実行した。A枝では最小permanent-above tail startとそのminimumを
既存のledger・座標APIへ接続し、仮想的least missing targetから

```
target + 2 ≤ a time
a time + 1 ≤ target + start
a time < 2 * time
q ≤ 1
(-1 : Int) ≤ potential q r
2 * subSum time + (target + 2) ≤ upperTri time
upperTri time < 2 * subSum time + 2 * time
```

を同時に与える`LeastMissingTarget.exists_leastTailLedgerMinimum`をLean化した。さらに低商を分け、
`q=0`または`q=1,r≤target`なら`a time≤time+target`、それ以外ならforced subtraction候補
`r-1`がpositiveかつ既出で、`target≤r-1<a time`を満たすfirst occurrenceが`time`より前にあることを
`PermanentTailMinimumCertificate.lowQuotient_bounded_or_earlierBlocker`として証明した。

B枝ではpositive blocker jobの全interval Hall条件をlazy range-add/range-max treeでexactに走査する
`experiments/blocker_interval_hall.cpp`を追加した。2,000万項までall-job familyと、同一last-occurrence
episodeの最初だけを残すfirst-job familyの双方で必要最小整数は`C_H^*=9`、最悪区間は常に`[2,6]`だった。
その区間は需要13、subtraction mass 4、count 1で、`C=8`はresidual 1、`C=9`はtightである。

H6枝では`f=N-4`の符号列が`−,+,+`へ一意化されたが、21個の`s`すべてについて座標、orbit bound、
ledger、parity、fresh legal/forced生成を満たす一様抽象suffixが構成できた。このsuffixは任意の高商
negative-potential stripへ拡張できる。不足するのは三つのaffine blockerを実prefixが同時に供給した
provenanceだけであり、mod 4分類によるH6直接攻略は停止した。

次周期はAのearlier blockerを反復可能certificateへ持ち上げる枝と、Bの有限初期部を除いた
first-window congestionをcausal inequalityにする枝の二本だけを残す。どちらも自由初期履歴モデルでは
成立せず、実prefixの共同生成を使うことを継続gateとした。

### 第百六ラウンド：canonical high枝の消滅と直接攻略の停止

A/B二枝の最終gateを実行した。一般strict tailのhigh blockerについては、値差がclock`time+1`に
等しい任意のpositive earlier occurrenceから

```
earlier + 3 ≤ time
2 * (subSum time - subSum earlier) + (time + 1) + upperTri earlier
  = upperTri time
time + 1 ≤ (subSum time - subSum earlier) + 3
```

を得るsharpな単一job定理をLean化した。first occurrence、座標、q=1には依存しない。さらに一般tailでは
blockerをhistorical predecessor outcome、downcross/budget dropまたはrenewed tail、既存tail-cycle rankへ
接続した。ただし複数blocker intervalのoverlapは制御せず、aggregate Hall定理ではない。

その後の自己監査で、`LeastMissingTarget`から直接得るcanonical witnessは既に
`a time+1≤target+start`と`start≤time`を持つため、常に`a time<time+target`であることを確認した。
従って座標は`q=0 ∨ (q=1 ∧ r<target)`で、earlier high-blocker右枝は正準主線では到達不能だった。
この強化を`exists_leastTailLedgerMinimum_lowCoordinates`としてLean化し、一般provenance定理を
noncanonical tail用と明記した。

Bではrestricted exact Hall probeを追加し、lazy scanを`H=100`, `C=0..12`の全区間brute forceと照合した。
初期releaseを除く`p≥7`では500万項までall-job/first-job双方の必要最小定数がsharpに`C=3`だった。
最悪例は常に単一jobの`−,+,+`三歩形であり、上のLean単一job定理と一致する。自由初期履歴にsynthetic
last-occurrenceをpreloadすると`[7,15]`で需要41、容量37となるため、aggregate候補は実prefixの共同生成を
本当に必要とする。

一方、仮にall-job `TailHall₃`を証明しても、old blockerとnonpositive additionを例外項として残すと、
得られる無条件帰結は`liminf a_n/n≤3`である。これはledger単独の二次上界より真に強いが、linear height、
positive subtraction density、permanent-above tailは両立し、固定未出targetとの矛盾にはならない。

以上によりロードマップの停止条件が成立した。Aのcanonical direct branchとBのsurjectivity branchを凍結し、
low-coordinate/provenance定理、sharp single-job `C=3`、Hall probe、H6/free-history no-goを独立成果へ移管した。
直接攻略の再開条件は、linear heightとpermanent-above性を矛盾させる外部入力、またはold blocker／
nonpositive resetを一様排除する独立定理である。

### 第百七ラウンド：target-relative comb圧縮とterminal blocker注入

類似greedy数列の一次文献から、Binary Enots Wolleyのopportunity recurrenceと有限消費、EKGの
frontier-window balanceを選び、Recamánのsigned subtraction candidateを固定target相対に解析した。
永久上側tailではbelow-target candidateが被覆済み履歴によりforced additionとなり、missing targetとの
等号候補は次のlegal subtractionで即座にtargetへ着地する。従って反例仮定下ではlow candidateの直後は
必ずstrict highであり、target wordに`LL`はない。

high-to-low subtraction後の`+,-,+,-,...`を既存`CombRun`へ一時刻ずらして接続した。entryがfreshなら
全low railはfirst occurrenceであり、時間的に分離したepisodeのrailは互いに素である。episodeが
historical predecessor `b`で止まるとfinal landingは`b+1`なので、同じ`b`が異なる完了時刻のcombを
止めることはできない。raw forced-addition jobでは偽だったblocker有限消費が、最大comb単位では
一回消費として成立した。

`target_transition_probe`の2,000万項scanはlow state 5,779,960、completed comb 2,661、最長
159,583 fresh landings、protocol違反0を返した。historical terminal blocker 2,660個のepisode再利用は
最大1で、Lean注入定理と一致する。残余は異なるblockerが上へ逃げるhigh-only excursionである。
次ラウンドはsigned candidateのHH遷移をclock重み付きmacro balanceへし、disjoint fresh intervalの
上界と同じevent族で衝突させられるかだけを調べる。
### 第百八ラウンド：low-to-terminal抽出、semantic mount、finite-basin no-go

2026-08-31 22:10 JSTから2時間枠で、target-comb、ancestry/ceiling、eventual-high causality、
finite-basin escapeを並列監査した。各tail low candidate landingがfreshであることから、low railの
自然数下降への強帰納法で有限 maximal comb suffixを抽出し、そのmaximal failureがhistorical
terminal blockerであることをLean化した。これによりlow stateからcompleted macro episodeへの橋は閉じた。

terminal blockerは現在horizonのOrbitReadyではないが、historical normalとして
ExtendedHistory/Refined/Semantic domainへ正しくmountできる。時間順episodeではlater-entry-leftが
strict progressを与え、upward resetも旧blockerがpre-tail triangular ceilingを越えていればtime ancestryで
strict childへ接続できる。finite anchorについて残余はexactに`progress ∨ anchor≤future blocker`となった。

しかし`blocker_j=r+j`, `entry_j=r+j+1`というright-moving singleton ladderはfresh interval order、
terminal blocker one-use、unboundedness、historical provenanceを全て満たし、future entryを一度もanchorの
左へ戻さない。このno-goをLeanで認証したため、finite-basinを現行macro interfaceだけで閉じる枝を停止した。

eventual-high側ではpositive forced candidateのearlier first-time mapを構成したが、標準prefixでcandidate 285の
再利用、既出output 2935への着地、異なるcandidateから同じoutput 265への衝突をLean認証した。2M replayでも
same-candidate最大reuseは13へ増えた。weighted ledger、cut flux、raw causal chargingはいずれも独立枝として停止する。

次の再開gateは、標準Recamán recurrenceだけが持つclock/legality no-escape、terminal利用ごとのfresh certificate
injectivity、またはeventual-high tailを直接排除するstrict rankのいずれかである。全射性自体は未証明で、
active direct branchは0本のままである。詳細は`docs/TWO_HOUR_RESEARCH_REPORT_2026-09-01.md`。

追加のclock監査ではterminal final直後の二clockがforcedであるexact launchを抽出し、singleton unit ladderの
次entryに5-clock gapを証明した。ただし6-clock刻みはgapとparityを無限に満たすためsparsityだけでは足りない。
20Mで`next blocker=previous entry`が0件だった事実は、visited-sensitive no-return候補として残す。

その無条件版は標準prefixで偽だった。target 4のepisode `(38,13,39,25)`のfresh entry 39は、
介在episode `(77,11,75,63)`の後、singleton `(111,0,40,39)`のterminal blockerへ戻る。この反例をLean認証した。
一方、後のblockerが古いfresh interval内に入るならinterior railでなくentryそのものに限られ、20Mでは
immediate same-target predecessor entryの再利用は0/2,655だった。残る候補を`TargetMacroSuccessor` gated no-returnへ限定する。

finite-root waiting episodeのfresh interval幅を足す`Q`について、各episodeの幅が`k+1`、clock幅と
`2Q=duration+2`で結ばれること、二episode版のhull boundをLean化した。20Mでは860系列・7,390 waitingで
有限族版不等式に違反0だが、最大待ち例のhull密度22.75%なので単独potentialは飽和しない。

eventual-highのcandidate reuse intervalにはexact subtraction balanceがあるが、標準prefixで5重overlapし、
strict high block内のactive depthは21から427へ増えた。candidate別望遠和と時刻multiplicityの双方が
reuse数を抑えないため、この集約枝も停止した。

### 第百九ラウンド：canonical upward provenance監査とfresh-certificate枝の停止

`target_upward_provenance_probe`を追加し、標準prefixを20M、200M、1B、2Bまで伸ばして、同一targetの
連続terminal episodeにおけるupward resetを監査した。2Bまでに28件あり、28/28がterminal right record、
28/28のblocker初出がforced additionだった。この規則は標準prefix上では強く安定している。

しかし必要だった有限課金は成立しなかった。28 blockerのうち26個は対象epoch中に新規生成され、forced-addition
birth candidateも19個がepoch中に新規生成された。さらにterminal fresh intervalに属するblockerは0/28だった。
候補値の再利用が最大1でも、tail自身が新候補を供給し続けるため、有限初期資源の消費にはならない。

加えて自由seedから実際の`Basic.step`を反復する探索で、target 5についてblockerが16から230へ上昇する
terminal right-record resetを得た。230の初出はclock 96での`326 - 96`というlegal subtractionである。
従って「upward terminal right recordならblocker初出はforced addition」という局所命題は偽であり、2Bの
観測をLean化するにはcanonical prefix到達可能性を分離する独立不変量が必要である。

この結果、terminal fresh certificate課金とlocal macro/historyだけによる証明枝を停止した。
canonical generation-vs-reuseの有望度を30から20へ下げ、標準prefix上のaddition-origin則は25で保留する。
現時点で相対的に残るのはfinite-root no-escape候補（45）だが、canonical reachability separatorが得られるまで
Lean化しない。全射性は未証明であり、active direct branchは0本のままである。

### 第百十ラウンド：finite-root残余のA/B kernel化

finite-root no-escape、canonical separator、proof architectureを並列監査した。finite-root枝はterminal stream
抽出、fixed-root separator、fresh interval packing、unbounded hull、infinitely many resetまで現行APIから
届くが、right ladderを壊すreset repaymentだけが新数学として残る。standard mex epochの統計は永久欠落tailの
直接観測でないため、finite-root枝を45から30へ下方修正した。

各terminal blocker自身をanchorにした監査では、2Bの21,510件中21,495件が後続entryでstrictに下へ戻った。
upward reset 28件では26件が次terminalで即時返済され、残る2件はtarget 4が実際に出現してepochが終了した。
ただし最大一般waitは20,097 episodeまで増え、一様waiting boundは再棄却した。

record gapのfuture consumptionもcohort固定で測った。200kまでのgapでrecord時未訪問だった44,341値は20Mまでに
44,290値が初出し、2M cohortも20Mまでに92.06%が消費された。これは強いqueue現象だが、任意固定gapの
eventual consumptionは全射性の再符号化になりやすいため診断用に留める。

proof architectureは`TargetTailResidualKernel`としてLean化した。tail後first occurrenceは既存
`coverageStep_at`で閉じるため、有限pre-tail oracleだけが不足する。全pre-tail rootがterminal escapeすると
CoverageOracleからtarget occurrenceが出て矛盾するので、固定finite no-escape rootを抽出できる。さらにlow candidate
のbounded/unboundedで仮想missing tailをeventual-high corridorまたはfixed-root unbounded right-terminal streamへ
exactに二分した。canonical clock-4 separatorは決定的標準軌道の言い換えに退化し、5/100で停止した。

### 第百十一ラウンド：target-low stream監査とreset repayment停止

`H-20260901-17`として研究問い、受理条件、停止条件を先に固定し、proposer、falsifier、formalizer、auditorを
分離した。statement auditにより、Round 16の`UnboundedRightTerminalStream`は構築過程で既知だった
target-low predicate、late start clock、universal fixed-root no-escapeを結論型で失っていたと判明した。
三点をconjunctionへ戻し、A/B kernel theoremを同じ仮定のまま強化した。

unbounded startから任意の既存terminal finalより後のlow clockが存在する。その最小clockを強帰納で選び、
間に別lowがあれば最小性に反すること、candidate equalityはmissing targetと矛盾することから全中間clockを
strict highへ上げた。これにより`UnboundedRightTerminalStream.exists_targetMacroSuccessor`をLean化し、
B枝からsame-target consecutive macroを反復選択できることを確定した。これはrepaymentを仮定しない。

返済を導く最弱の有限資源候補はfixed-history blocker preloadだった。返済が起きない間、全後続blockerの
first timeがreset startより前なら、one-useでblocker/first-timeが相異なり、unbounded streamから有限prefixへの
単射が生じて矛盾する。この依存鎖は`PROVED-PAPER`である。

しかしseed `seen={0,1,6,8,13}, current=13, nextClock=7`からexact greedy ruleを続けると、target 4の
reset `6→14`後、entryが14未満へ戻る前にblocker 199がclock 65のforced addition`134+65`で初出する。
コマンド`ruby experiments/target_reset_preload_counterexample.rb 1200`で再現でき、local preloadと即時返済を
`REFUTED`とした。exact permanent-missing antecedentは有限計算でinstantiateできず未反証だが、global preloadへ
修理すると返済またはtarget occurrenceの言い換えになる。

seeded repayment probeはdiscovery `5000 200 10000 20260901`と独立holdout
`1000 200 50000 20260902`へ固定した。前者は31,894 upward中31,259 repayment、337 target-end、298 censor、
後者は8,753中8,652 repayment、77 target-end、24 end-censorだった。resolved wait最大は双方9 episodeで、
uniform boundは仮定しない。これは`COMPUTED`であり永久欠落tailの証拠ではない。

以上によりexact repayment statementは`CONJECTURED`のまま、仮説カードを`STOPPED`とした。有望度を40から15へ
下げ、再開条件を「future return、target occurrence、canonical reachabilityを使わずpost-reset blocker birthを
抑えるindependently testable global invariant」に限定した。active direct branchは0本である。

検証コマンド：

```text
lake build Recaman.TargetTailResidualKernel  # 177/177
lake build Recaman.Audit                     # 230/230
ruby -c experiments/target_reset_repayment_probe.rb
ruby -c experiments/target_reset_preload_counterexample.rb
git diff --check
./scripts/check.sh                            # 230 jobs; 1,082 declarations audited
```

全体監査は成功し、1,082 declarationsの公理依存が
`{propext, Classical.choice, Quot.sound}`内であること、禁止された
`sorry` / `admit` / `native_decide` / user-defined `axiom`がないことを確認した。

### 第百十二ラウンド：burst use-gapの意味監査とlocal反例

`H-20260901-01`の次候補だった`sqrt(6m)` use-gapを形式化する前に、exact statementと
導出artifactを再監査した。記録にある`periodic_nogo_check.py`と他の抽象schedule scriptは
repositoryに存在せず、periodic no-goもschedule型・量化子・紙上証明を復元できない。
よって`PROVED-PAPER`判定を取り下げ、`OBSERVED`へ戻した。

use-gap導出の実質的な欠落は、`RecurringCandidateBurst`の「加算3連以上」を
「ちょうど3連」と読んでいたことだった。反証器として`m=q^2+2q`、word
`A^(q+1)S^q`、gap `2q+1`のseeded exact greedy continuationを構成した。この族は
candidate floorを保って両端で同candidateを取り、中間はclockよりstrict high、後端も
3-addition burstを持つが、`gap^2/m -> 4`である。

`SeededUseGapCounterexample`は`q=10`, `m=120`, `n=141`をLean kernelで認証し、
legal entry、中間high、`A^11S^10`、後端3-addition burst、`21^2 < 6*120`を一つの
theoremに固定した。計算反証器`use_gap_counterexample.cpp`はdiscovery `q=3..100`と
独立holdout `q=101..10000`を通過し、最終比は`3.999600090`だった。

結論は次の通り。local `sqrt(6m)` use-gapは`REFUTED`とし、run長上限を追加する修理は
`SeededHighCorridorNoGo`に反するため`STOPPED`とする。main burst-supply予想自体は反証されて
いない。反例族は`q`ごとにseedを変えるため、残る最弱の問いは「単一の有限seedが
per-use需要を無限に自己供給できるか」である。

検証コマンド：

```text
lake env lean Recaman/SeededUseGapCounterexample.lean
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/use_gap_counterexample.cpp -o /tmp/use_gap_counterexample
/tmp/use_gap_counterexample 3 100
/tmp/use_gap_counterexample 101 10000
./scripts/check.sh                            # 245 jobs; 1,130 declarations audited
```

全体監査は成功し、1,130 declarationsの公理依存が
`{propext, Classical.choice, Quot.sound}`内であること、禁止された
`sorry` / `admit` / `native_decide` / user-defined `axiom`がないことを確認した。

### 第百十三ラウンド：fixed-seed global supply並列監査と停止判定

`H-20260901-01`の最後に許可した修理を`H-20260901-02`へexact化し、需要birth、固定seed
falsifier、subtraction ancestry、periodic no-go有限核を独立に進めた。

`RecurringCandidateDemandBirth`はrigid需要`c+m`の初出をlegal subtraction birth／addition birthへ
分類し、late addition枝に`target+2(t+1)<c+m`をLeanで証明した。これは真のhalf-clock contraction
だが、subtraction枝は`CanSubtract(t+1)`を返すためforced supplier classに閉じない。

`SupplyAncestryCounterexample`はcanonical prefixで二つの障害をkernel認証した。candidate 42は
clock 20のlegal subtractionで初出しclock 36でforced reuseされるため、forced nodeからbirthへ
戻るとpremise polarityが反転する。またdistinct children 151/135はclocks 110/126で同じparent
261から生まれ、後にforced reuseされる。20M exact probeのholdoutでもshared parent 605746を得た。
従ってclosed supplier ancestryとgeneric parent injectionは`REFUTED`、addition contractionと
subtraction ledgerを足すdrift枝は`STOPPED`。

fixed-seed falsifierは一つのbyte-identical state（boundary 45、value 113、candidate 20、seen 489、
fingerprint `14161494152507716643`）から、bootstrap 46の後にclocks 94/286/862の3 counted usesを
exact replayした。需要114/306/882はseedに含まれずclocks 47/96/288で内部初出する。holdout 8650と
診断1Mはいずれも同じ3 useだけで、first post-plan non-highは868だった。出力SHA-256は
`209f96a0ce2f9df65aed7713aaa8cac0ba695712a8231f974cae23d38b876b5c`。これは
`COMPUTED`有限反例であり、無限fixed-seed countermodelではない。

periodic no-goはexact recurrenceと三つのsign-sum caseを紙上で再構成した。balanced periodの
actual cyclic phase drift総和`-p^2`と負phase存在を`PeriodicCandidateNoGo`でLean化し、periods
1..22の8,388,606語で独立回帰検査した。full eventually-periodic no-goは`PROVED-PAPER`、有限核は
`PROVED-LEAN`、非周期scheduleは未排除である。

以上によりexact infinite supply命題は`CONJECTURED`のまま、H-20260901-01/02の現proof branchは
predeclared stop conditionに到達して`STOPPED`。再開条件はexternal blocker集合`E`とfuture fresh
subtraction集合`S`のcutoff-independent debt/collision不等式、またはfuture return等を仮定しない
独立canonical invariantとした。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/periodic_candidate_nogo_check.cpp -o /tmp/periodic_candidate_nogo_check
/tmp/periodic_candidate_nogo_check 1 16
/tmp/periodic_candidate_nogo_check 17 22
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/supply_ancestry_probe.cpp -o /tmp/supply_ancestry_probe
/tmp/supply_ancestry_probe 10000001 0 10000000
/tmp/supply_ancestry_probe 20000001 10000001 20000000
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/fixed_seed_supply_falsifier.cpp -o /tmp/fixed_seed_supply_falsifier
/tmp/fixed_seed_supply_falsifier 2000000 4096
./scripts/check.sh                            # 248 jobs; 1,136 declarations audited
```

全体監査は成功し、1,136 declarationsの公理依存が
`{propext, Classical.choice, Quot.sound}`内であること、禁止された
`sorry` / `admit` / `native_decide` / user-defined `axiom`がないことを確認した。

### 第百十四ラウンド：研究情報アーキテクチャのリファクタリング

数学statementとLean APIを変更せず、研究状態の正本を`CURRENT_FRONTIER.md`へ集約した。
全射性、A/B residual、fixed-seed supply、periodic no-go、ancestry反例、use-gap、reset repayment、
`TailHall₃`を14件のfrontier-changing claimへ分け、`EVIDENCE_REGISTRY.tsv`にexact evidence label、
artifact、Audit symbol、reopen gateを記録した。exact命題の`CONJECTURED`と、証明ルートの
`STOPPED`は別rowに分離した。

既存文書は削除・移動せず、役割を次のように固定した。

- `CURRENT_FRONTIER`: current statusと再開gateの正本
- `EVIDENCE_REGISTRY.tsv`: claim/evidenceの機械可読正本
- `PROOF_MAP`: theorem dependency atlas
- `ROADMAP`: 判断とgateの時系列
- `STATUS_REPORT` / `RESEARCH_REPORT` / `RESEARCH_PORTFOLIO`: historical snapshot
- `DEVELOPMENT_LOG`: append-only log
- hypothesis card: 一つのbounded research unit

`check_research_registry.sh`を追加し、label集合、7-field schema、ID一意性、artifact存在、全registry IDの
current-frontier参照、および`PROVED-LEAN` rowの`Recaman/Audit.lean`登録を検査するようにした。
同checkを`scripts/check.sh`のfull build前へ統合した。

検証コマンド：

```text
bash -n scripts/check_research_registry.sh scripts/check.sh
bash scripts/check_research_registry.sh      # 14 entries; 5 PROVED-LEAN rows
git diff --check
./scripts/check.sh                            # 248 jobs; 1,136 declarations audited
```

全体監査は成功した。定理名変更、module移動、proof term変更はなく、既存の研究成果と
`recaman-visualizer/`には触れていない。

### 第百十五ラウンド：Lean module architectureのリファクタリング

数学statement、定理名、proof termを変えず、Lean sourceの依存境界を監査した。rootのdirect importは
全sourceを列挙していないが、欠けて見えた5 moduleはいずれもtransitiveに到達しており、実際のroot
closureは`Audit`を除く全library moduleを覆っていた。

最近追加した4 moduleについてdirect importを一つずつ除く単体コンパイルを行った。
`RecurringCandidateDemandBirth`の2 import、`SeededUseGapCounterexample`の`Basic`、
`SupplyAncestryCounterexample`のcandidate定義元は必要だった。一方、`PeriodicCandidateNoGo`は
`Std`なしで完結した。また`SupplyAncestryCounterexample`は`HighCandidateCausalReuse`の定理を
使っていないため、direct dependencyを`TargetCandidateTransitions`へ下げた。

構造の正本を`MODULE_ARCHITECTURE.md`、最近のfrontier境界の機械可読契約を
`MODULE_IMPORT_CONTRACTS.tsv`とした。`check_module_architecture.sh`は全sourceからgraphを再構成し、
project importの解決、duplicate/self import、root到達性、acyclic性、4件のdirect-import契約を検査する。
同checkをfull build前へ統合した。

検証コマンド：

```text
bash -n scripts/check_module_architecture.sh scripts/check.sh
bash scripts/check_module_architecture.sh
lake env lean Recaman/RecurringCandidateDemandBirth.lean
lake env lean Recaman/PeriodicCandidateNoGo.lean
lake env lean Recaman/SeededUseGapCounterexample.lean
lake env lean Recaman/SupplyAncestryCounterexample.lean
git diff --check
./scripts/check.sh  # 248 jobs; 1,136 declarations audited
```

このラウンドではdefinition ownershipの移動やlegacy moduleの一括再階層化を行わない。次に構造上
価値がある候補は、基礎概念`nextSubtractionCandidate`が高いbranch moduleに置かれている点を
consumer数とrebuild影響から監査し、移動の便益が十分な場合だけ別change setにすることである。

### 第百十六ラウンド：subtraction candidate definition ownershipの下位化

第百十五ラウンドで残した設計監査を別change setとして行った。`nextSubtractionCandidate`は
`a n - (n + 1)`というkernel-levelの式で、23 Lean moduleから参照されている一方、ownerは
target固有の`TargetCandidateTransitions`だった。完全修飾名を維持したままdefinition本体だけを
`Basic`へ移し、全consumerは既存のtransitive importでそのまま解決できた。

特に`SupplyAncestryCounterexample`はtarget-tail theoremを使わず、canonical prefixの`FirstAt`と
history membershipしか使わない。direct importを`History`へ下げた結果、project module dependency
closureは旧`HighCandidateCausalReuse`経由169、暫定`TargetCandidateTransitions`経由82から5へ縮小した。
定理名、statement、proof term、Audit symbolに変更はない。

最初に`lake env lean Basic.lean`だけを実行したところ、consumerは更新前の`Basic.olean`を読むため
未知識別子になった。これはsource graphの失敗ではなくownership移動時のcache orderingであり、
`lake build Recaman.Basic Recaman.TargetCandidateTransitions Recaman.SupplyAncestryCounterexample`で
依存順に84 jobsを再構築した後、全consumerのstandalone checkが通った。このpitfallをarchitecture
手順にも固定した。

検証コマンド：

```text
rg -l '\bnextSubtractionCandidate\b' Recaman --glob '*.lean' | wc -l  # 24 = owner 1 + consumers 23
lake build Recaman.Basic Recaman.TargetCandidateTransitions Recaman.SupplyAncestryCounterexample
lake env lean Recaman/TargetCandidateTransitions.lean
lake env lean Recaman/SupplyAncestryCounterexample.lean
bash scripts/check_module_architecture.sh
shellcheck scripts/check_module_architecture.sh scripts/check_research_registry.sh scripts/check.sh
git diff --check
./scripts/check.sh  # 248 jobs; 1,136 declarations audited
```

L0 source変更によりdeep certificateも完全再計算され、`DeepSixtyoneTraceCertificate`は1,116秒、
`DeepSixtyoneMexCertificate`は366秒を要した。最終的に248 jobsは全成功し、1,136 declarationsの
公理依存は`{propext, Classical.choice, Quot.sound}`内、禁止proof escapeは0件だった。この実測から、
今後のL0 ownership変更は依存削減の便益だけでなくdeep certificate再構築コストも事前評価する。

### 第百十七ラウンド：external blocker collision閾値の空虚性監査

`H-20260902-01`で、同一candidate `c`のsupplied successor demand `c+m`を、減算初出集合`S_c`と
加算初出を強制した正の外部blocker集合`E_c`へ分け、4回useで`E_c ∩ S_c ≠ ∅`となるH4を凍結した。
唯一の許可修理は閾値8とした。

`external_blocker_collision_probe`のcanonical discovery 2Mは1,568 supplied uses / 1,567 candidates、
frozen holdout 20Mは4,798 / 4,797で、4回use候補は双方0だった。最大はcandidate 723の2回
（clocks 984,4596）で`E={643}`, `S=∅`。既知fixed seedも3-useのためH4/H8はいずれも評価母集団が
空である。not-refutedを正の証拠とせず、同一candidate有限閾値のcollision設計を`STOPPED`とした。
次の許可形は異candidate間または固定clock windowへ集約され、仮説を先取りせず非空なdebt量に限る。

### 第百十八ラウンド：window集約demand provenanceの反証

`H-20260902-01`の停止判断が要求した「異candidate間または固定clock windowで集約される非空な
debt量」を`H-20260902-02`としてexact化した。低supplied use（`c ≤ m`、forced addition、需要
`w = a m - 1 = c + m`既訪問）をdyadic window `[2^k, 2^(k+1))`へ集約し、blocked加算初出の
blocker集合`E(W)`と減算初出需要集合`S(W)`の交わり（H-W）、減算初出の半clock縮約`2t < w`（H-S）、
加算初出の非truncated性`2b < w`（H-A）の3命題を凍結した。discovery 2M、holdout 20M、許可修理は
window形の変更1回のみとした。

`window_demand_provenance_probe`の結果、3命題ともdiscoveryで反証された。2Mでは低use 971件、
適用window 13件すべてで`E ∩ S = ∅`、near-diagonal減算初出444件、truncated加算初出259件。
holdout 20Mでは低use 2,987件、適用window 17件すべて交わりなし、near-diagonal 1,533件、
truncated 732件で、window `[2^23, 2^24)`では減算初出449件中401件がnear-diagonalだった。
H-Sの最初の2証人（151@110、135@126）は`SupplyAncestryCounterexample`のkernel認証済み
`FirstAt`と一致する。修理は行っていない。

判断：collision型debt設計は同一candidate形（空虚）と集約形（反証）の双方で閉鎖。再開条件1は
`|E|`のstrict growth形のみ残し、再開条件3のcanonical-only invariantはnear-diagonal減算sourceを
許容する形に限る。registryへ`E-016`（`REFUTED`）と`E-017`（`COMPUTED`）を追加した。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/window_demand_provenance_probe.cpp -o /tmp/window_demand_provenance_probe
/tmp/window_demand_provenance_probe 2000000    # SHA-256 4e9e4653...
/tmp/window_demand_provenance_probe 20000000
bash scripts/check_research_registry.sh        # 17 entries; 5 PROVED-LEAN rows
lake build --no-build                          # 248 jobs up-to-date
```

### 第百十九ラウンド：supplied-demand provenance反例のkernel認証

第百十八ラウンドでprobeが返したH-A／H-Sの最初の証人を`DemandProvenanceCounterexample`として
Lean化した。`truncatedBirth_suppliedDemand_counterexample`は、clock 5の低supplied use
（`a 5 = 7`、candidate 1、forced addition、需要`a 5 - 1 = 6 ∈ valuesThrough 5`）の需要6が
clock 3のtruncated加算（`nextSubtractionCandidate 2 = 0`）で初出し`6 ≤ 2·3`であることを、
`nearDiagonalBirth_suppliedDemand_counterexample`は、clock 112の低supplied use
（`a 112 = 152`、candidate 39、forced addition、需要151既訪問）の需要151がclock 110のlegal
subtraction（`a 109 = 261`）で初出し`151 ≤ 2·110`であることを、`FirstAt`証人つきで`decide`により
認証する。direct importは`History`のみ（contract登録済み）。

これでH-20260902-02の`REFUTED`判定は、probeの`COMPUTED`証拠に加えてkernel認証された最小反例
（registry `E-018`）を持つ。corridor限定のlate addition contractionがcanonical prefixでは
成立しないことも同時に確定した。

検証コマンド：

```text
lake env lean Recaman/DemandProvenanceCounterexample.lean   # 1.1s
bash scripts/check_module_architecture.sh                   # 246/246 reach; 5 contracts
bash scripts/check_research_registry.sh                     # 18 entries; 6 PROVED-LEAN rows
./scripts/check.sh                                          # 249 jobs; 1,138 declarations audited
```

### 第百二十ラウンド：canonically admissible seed densityの検査

再開条件3（canonical-only invariant）の最初の具体候補として、kernel認証済みの2つのhistory
invariant `valuesThrough_length`（`|seen| ≤ clock+1`）と`a_le_upperTri`（`max seen ≤ upperTri clock`）
を`fixed_seed_supply_falsifier`の合成seedへ課した。第3引数`1`でseedをreplay前に
`inadmissible_history_density`／`inadmissible_history_height`として棄却し、引数なしでは
2026-09-01の記録をbyte-identicalに再現する（SHA-256 `209f96a0...`を確認）。

結果は`COMPUTED`：depth 1で合成に到達した3,563 planはすべて不許容（size 2,608、height 955）、
depth 2/3/4の357/104/15 planもすべてsize不許容で、admissible seedは0件。最小size超過は4
（boundary 5、candidate 5、2 intervalで10値必要）。arbitrary modeでは同じplanから
1,414/31/1/0のexact seedが得られていた。従って3-use記録（boundary 45に489値）を含む既知の
固定seed反例は、canonical historyが持ち得ないblocker密度に依存している。

これは無限no-goの証明ではない（samplerは非網羅、protocolはblockerをprefix内で生成しない）。
判断：history densityをgate 3の最初の拘束的候補として登録（registry `E-019`）。次のunitは
blockerをexact prefixで生成するadmissible synthesizer、またはadmissible seedのuse数の紙上上界。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/fixed_seed_supply_falsifier.cpp -o /tmp/fixed_seed_supply_falsifier
/tmp/fixed_seed_supply_falsifier 2000000 4096      # byte-identical to 2026-09-01
/tmp/fixed_seed_supply_falsifier 2000000 4096 1    # canonical-density mode
bash scripts/check_research_registry.sh            # 19 entries; 6 PROVED-LEAN rows
```

### 第百二十一ラウンド：preload-free generalized orbitのsupply chain検査

第百二十ラウンドの次の判断「blockerをpreloadせず生成する母集団」を最も単純な形で実装した。
`generalized_orbit_supply_probe`は単一初期値`v0`（history `{v0}`）からexact `Basic.step`則で
軌道を生成し、`fixed_seed_supply_falsifier`のcanonical scanと同じcounted-use意味論
（legal low entry、3 addition burst、内部初出需要、strict-high same-candidate link、chain）で
集計する。`v0 = 0`はfalsifierのcanonical scan（119 use、0 link、chain 1）を正確に再現した。

凍結命題H-G3（chain ≥ 3を持つstartは存在しない）をdiscovery `[0,1000]`、holdout `[1001,2000]`
（horizon 100,000）で検査し、いずれも未反証。実測は命題より強く、diagnosticの`[0,200]`@1M、
`[2001,20000]`@100kを含めた20,001 orbit・内部供給burst use 1,272,765件でstrict-high linkは
**0件**、全orbitのmax chainは1だった。既知のchain 2・3はboundary 45に489値をpreloadしたseedからしか
得られていない。

判断：`COMPUTED`（registry `E-020`）。exact命題「generalized orbitにstrict-high same-candidate linkは
存在しない」を`CONJECTURED`（`E-021`）として登録。許可されるformalization routeは、最初のlinkが
preloaded blockerを強制する紙上証明のみ。反証は1 startで足りる。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/generalized_orbit_supply_probe.cpp -o /tmp/generalized_orbit_supply_probe
/tmp/generalized_orbit_supply_probe 0 0 2000000        # canonical control
/tmp/generalized_orbit_supply_probe 0 1000 100000      # discovery, SHA-256 d0bfd13f...
/tmp/generalized_orbit_supply_probe 1001 2000 100000   # holdout,   SHA-256 7bc29ea1...
bash scripts/check_research_registry.sh                # 21 entries; 6 PROVED-LEAN rows
```

### 第百二十二ラウンド：cone excursion census と strict-high条件の意味監査

第百二十一ラウンドのlink 0件の理由を`cone_excursion_probe`で診断した。burst use（c ≥ 2）後に
最初にcandidate ≤ clockとなるbreaker clock `t`は、canonical 2Mと20,000本のgeneralized orbit
（100k）の全1,252,246件で倍化clock `2m+2`より前にあり、`t/m`の最大は1.44（m=25）、m ≥ 100では
1.098、canonicalでは1.033だった。breakerが常にsubtraction stepであることは算術的に自明
（addition後のcandidateは`a(t-1)-1 ≥ 2t-2`）。さらに`a t > 2t+1`のcone-exterior runを開始clock
`≥ max(16, 4v0)`で数えると、約85M本のいずれも開始の2倍へ届かず、最大比は1.222（canonical、
first=18）、clock 9,000以降は1.073以下だった。

意味監査：strict-high（candidate > clock）は2026-09-01のfixed-seed protocolが採用したuse間条件で、
corridorの実条件（candidate > 固定target）より強い。従って`E-021`（link no-go）と本ラウンドの
excursion bound（`E-023`）はcone-exterior excursion経由の自己供給のみを拘束し、corridor streamは
排除しない。この注意を`CURRENT_FRONTIER.md`と`H-20260902-04`に付記した。

判断：census `E-022`（`COMPUTED`）、excursion bound `E-023`（独立部分命題、`CONJECTURED`）を登録。
次のfixed-seed／preload-free unitは、use間条件を固定床型（candidate > floor）で再定義してから行う。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/cone_excursion_probe.cpp -o /tmp/cone_excursion_probe
/tmp/cone_excursion_probe 0 0 2000000 ; /tmp/cone_excursion_probe 0 1000 100000
/tmp/cone_excursion_probe 1001 2000 100000 ; /tmp/cone_excursion_probe 2001 20000 100000
bash scripts/check_research_registry.sh   # 23 entries; 6 PROVED-LEAN rows
```

### 第百二十三ラウンド：c-floor条件でのpreload-free link検査

第百二十二ラウンドの意味監査を受け、`generalized_orbit_supply_probe`にcorridor-faithfulな
use間条件（同一cの2回の内部供給burst useの間で中間candidateが全て`≥ c`、least recurring
candidate条件そのもの）をc-floor mode（第4引数`1`）として追加した。strict-high形より弱い条件で
linkは増え得るが、canonical 2M、discovery `[0,1000]`、holdout `[1001,2000]`、diagnostic
`[0,200]`@1M・`[2001,20000]`@100kのすべてでlinkは0件、全chainは1のままだった。

従って`E-021`をc-floor形（strict-high形を含意）へ強めて登録し直し、frontierの意味上の注意を
「`E-023`のみcone-exterior条件に依存」へ修正した。2026-09-01の固定seed 3-use記録はstrict-high形で
あり、c-floor形での固定seed探索は未実施であることも明記した。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/generalized_orbit_supply_probe.cpp -o /tmp/generalized_orbit_supply_probe
/tmp/generalized_orbit_supply_probe 0 1000 100000 1     # c-floor discovery, SHA-256 9f0af821...
/tmp/generalized_orbit_supply_probe 1001 2000 100000 1  # c-floor holdout,   SHA-256 a47871ba...
bash scripts/check_research_registry.sh                 # 23 entries; 6 PROVED-LEAN rows
```

### 第百二十四ラウンド：真偽を問わないロードマップと対角線近傍census

「全射性が偽でもよい」という方針転換を受け、`near_diagonal_rate_probe`でcanonical 3e9の
対角線近傍統計を取った（`E-024`）。sub-diagonal着地28.6%、interior 64.6%、時刻nで未訪問の値≤nが
約51%でいずれも安定。高さ≤1356のinterior時刻は1e7まで各decade約1000件だが[1e8,1e9)で47件、
[1e9,3e9)で0件。47件は高さ1355から1217へ2時刻ごとに3減る1本のchainで、B枝のcomb機構が
そのまま実軌道の遅延着地機構であることがexactに確認された。chainの小さなcandidateはmod 3の
1剰余類しか走らず、mex 1355（高さ1356、`≡0 mod 3`が必要）はこのchainでは着地できない。

紙上で二分定理D（`E-025`, `PROVED-PAPER`）を得た：無限個のnで`a n ≤ n+2`、または未訪問整数の
下密度≥1/4。証明は孤立補題（interior時刻の次はexterior）、凍結補題、`valuesThrough_length`による
計数の3段で、A枝は密度1/4の欠損を含意する。データは第一の選択肢側であり、A枝のsupply系解析は
実在しない対象を扱っていたことになる。

ロードマップ`RESEARCH_ROADMAP_2026-09-02_TRUTH_AGNOSTIC.md`に、T1（DのLean化）、T2（chain補題）、
T3（遅延着地の特徴づけ）、T4（chain侵入・生存の定量定理、真偽を決める本丸）、T5（非全射なら
欠損無限個）と、run-length simulatorによる1e12以上の侵入率判定を固定した。

検証コマンド：

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror experiments/near_diagonal_rate_probe.cpp -o /tmp/near_diagonal_rate_probe
/tmp/near_diagonal_rate_probe 3000000000   # 25秒、docs/NEAR_DIAGONAL_CENSUS_3E9_2026-09-02.txt
bash scripts/check_research_registry.sh    # 25 entries; 6 PROVED-LEAN rows
```

### 第百二十五ラウンド：二分定理DのLean化（T1）

`MissingDensityDichotomy`を追加し、ロードマップT1を完了した。`lowCount n bound`
（`valuesThrough n`のうち`bound`以下の要素数、重複込み）を定義し、`lowCount_succ`、`lowCount_le`
（`≤ n+1`）、`lowCount_le_add`を得る。法則`∀ k ≥ N, k+3 ≤ a k`の下で孤立補題
`exterior_succ_of_interior`（`a n ≤ 2n+1 → 2n+4 ≤ a (n+1)`）を`recurrence`の場合分けとomegaで示し、
`lowCount_two_step`（後半の連続2時刻は窓へ高々1値）と`lowCount_block`（帰納）で
`lowCount (s+2j) ≤ lowCount s + j`を得る。`missing_window_of_law`は`s = m/2+1`、`j = (m−s)/2`と置き、
`List.range (m+3)`を「未訪問filter ++ 窓内filter」の部分集合として`Nodup.length_le_of_subset`で
計数し、凍結は法則から直接（`t ≥ m+1 ≥ N`なら`a t ≥ m+4 > m+2`）出る。結論は
`m ≤ 4 * missing.length`まで締まった（当初の`+8`は不要だった）。

主定理`missing_density_dichotomy`は古典的場合分けで法則を取り出す。系
`EventualHighCandidateTail.missing_density`（`corridor_value_law`から法則を得る）と
`not_eventualHigh_of_recurrent_low`、および`recurrent_low_of_subDiagonal`を同梱。
`lake env lean`は初回で4件のエラー（`+0`の正規化2件、`m ≤ 1`での`s+2j ≤ m`破れ1件→仮定を
`2N+2 ≤ m`へ、`List.filter_sublist`は関数でなく項1件）を出し、修正後は無警告で通過した。
direct importは`EventualHighCorridorSecondMissing`のみ（contract登録済み）。
registry `E-025`を`PROVED-LEAN`へ昇格し、4定理をAuditへ追加した。

検証コマンド：

```text
lake env lean Recaman/MissingDensityDichotomy.lean
lake build                                   # 250 jobs
bash scripts/check_module_architecture.sh    # 247/247 reach; 6 contracts
bash scripts/check_research_registry.sh      # 25 entries; 7 PROVED-LEAN rows
./scripts/check.sh                           # 1,142 declarations audited
```

### 第百二十六ラウンド：chain補題と遅延着地の特徴づけ（T2/T3）

`DescendingChain`（direct importは`History`のみ）でロードマップT2/T3を完了した。
サブエージェントが初回コンパイル一発で通し、親が`lake env lean`と禁止語走査で再検証した。
定理：`chain_forced_addition`、`chain_landing`、`chain_exit_up`、`chain_late_landing`、
`chain_descends`（kに関する帰納、4つのomega正規化）、`chain_small_candidate_mod_three`、
`late_landing_iff`。証明はすべて`recurrence`の`CanSubtract`場合分けと、候補値の
`show a n − (n+1) = …; omega`による書き換えで閉じる。

OEIS確認：852655は10^612項まで欠損（Chaffin 2026-02-08、A064227）、1355の初出は第325,374,625,245項
（A057167 b-file、A064227の第8項）、19の初出は99734。Chaffinの計算法「ping-pong区間の先読み」は
本ラウンドのchainと同一機構で、区間長が指数的に伸びるため10^612項が到達できる。
Chaffinの新規列A393814/A393815（各下降弧の最小値とその添字、n = 1..5104）はchainの終点の
完全な台帳であり、T4の侵入率判定に直接使える。

検証コマンド：

```text
lake env lean Recaman/DescendingChain.lean
lake build                                   # 251 jobs
bash scripts/check_module_architecture.sh    # 248/248 reach; 7 contracts
bash scripts/check_research_registry.sh      # 26 entries; 8 PROVED-LEAN rows
./scripts/check.sh                           # 1,149 declarations audited
```

### 第百二十七ラウンド：Chaffinの10^612項台帳の解析（E-027）

OEIS A005132/A057167/A064227/A393814/A393815とChaffinのページから、852655が10^612項まで欠損、
1355の初出が第325,374,625,245項、Chaffinのping-pong区間がdescending chainと同一機構であることを
確認した。`rec-landings-1e612.txt`（5,104件の弧の底）と`rec-holes-2_32.txt`（10^612項後の2^32未満の穴）を
`experiments/chaffin_landing_analysis.py`で集計した（出力は`docs/data/`）。

弧の本数は600 decadeにわたり1 decadeあたり8.45本で一定だが、深さ比`r=(log n−log v)/log n`は
中央値0.027・99%点0.34・最大0.85で、10^41以降は10^7未満の着地が一度もない。穴は1,277,400個で
`1007255+3k`の等差列を含み、`chain_small_candidate_mod_three`の実軌道での痕跡である。

判断：真偽の見立ては非全射側へ。T4を「弧の発生率」から「弧の深さ＝chainの生存長が帯の未訪問run長で
決まる自己相似構造」の証明（landing floor ⇒ 852655の永久欠損）へ書き換えた。ロードマップ§2・§4・T4、
frontier、registry `E-027`を更新。

### 第百二十八ラウンド：landing floor カード（T4の凍結）

Chaffin台帳の絶対深さ`D = log₁₀ n − log₁₀ v`は添字のdecade区間によらず定常（中央値7.4、90%点14.5、
裾`P(D>d) ≈ exp(−3.17−0.037d)`）と判明した。固定値852655の着地には`D > k−5.93`が要り、経験分布の
外挿ではdecade 41〜612の期待着地回数1.12（実際0回）、10^612以降は1.6×10^-9。

T4を`H-20260902-05`（landing floor：ある時刻以降の弧の底は852655を超える）として凍結し、
registry `E-028`（`CONJECTURED`）に登録した。証明義務は「chainの生存段数が帯の未訪問run長で抑えられ、
run長は添字に比例するスケールでしか現れない」という自己相似invariantに集約される。
反証はChaffinの追加計算で852655未満の弧の底が現れること。

補遺：`chain_band_fresh_at_start`（k段のchainが消費する帯の値`n+h−1−i`は全て開始時刻`n+1`で未訪問）を
`DescendingChain`に追加し、Auditへ登録した。landing floorカードの受入条件2の局所半分にあたる。

### 第百二十九ラウンド：弧の底の検出器と generalized orbit の深さ分布

`landing_depth_probe`（Chaffin と同じ「`a n mod n` が増加するまでの区間の最小値」）を実装し、
canonical で A393814/A393815 の先頭 19 件（添字 1, 2, 4, 10, …, 99734、値 1, 3, 2, 11, …, 19）と
一致することを確認した。単一初期値 v0 の generalized orbit 27 本（v0 = 0〜10000）を 3×10^8 まで
走らせると、弧は各 decade 4 本、深さ `D = log₁₀ n − log₁₀ v` の中央値は 2.3〜3.3、90% 点は
3.6〜5.3 で、canonical（2.53、3.61）と同程度だった。深さ分布は `initial` 固有の性質ではなく、
この規模では初期値によらない。landing floor カード（`H-20260902-05`）の falsification plan の
「generalized orbit での定常性」の最初の測定として記録した（`docs/data/landing_depth_generalized_3e8_2026-09-02.txt`）。
Chaffin の台帳では弧の本数が 10^9 の 4 本/decade から 10^19 の 8.5 本/decade へ増えて一定になるため、
深さ分布の定常性の比較は 10^12 以上（run-length simulator）で続ける。

### 第百三十ラウンド：run-length simulator（10^13）

サブエージェントが`experiments/run_length_recaman_simulator.cpp`を実装した。訪問集合は極大閉区間の
sorted vector、`accel`モードはChaffinのping-pong区間（descending chain）を先読みで一括適用し、
census列を閉形式で更新する。親が`-Werror`で再コンパイルし、出力を確認した。`plain`は
`near_diagonal_rate_probe`（3e9）と共有列が一致、`accel`は`plain`と10^9/3×10^9/10^10で同一出力。
1355の初出325,374,625,245とmex推移（…→1355→2406）がOEISと一致した。

10^13まで471秒。区間数は1 decadeあたり約2.9倍（10^13で254万）。高さ≤1356のinterior時刻は
[10^9,10^13)で各decade 452〜2259件あり、[1e9,3e9)の0件は揺らぎだった。帯[1,1024]を掃いたchainは
1e9: 1本、1e10: 2本、1e11: 5本、1e12: 3本。2^20未満の遅延着地は1e9: 2309、1e10: 972、1e11: 430、
1e12: 30と約2.3分の1/decadeで減衰し、2^20未満の穴は10^13でほぼ固定されている。
registry `E-029`。10^14の走行は継続中。

### 第百三十一ラウンド：hole-hopping規則のLean化（HoleHopping）

`HoleHopping`（direct import `DescendingChain`）に`chain_lands_first_fresh`（自クラスの最初の未訪問
candidateへ着地）、`comb_after_landing`、`comb_sweep`（連続する穴の掃き）、
`chain_never_presents_other_class`を追加した。サブエージェントが初回で通し、親が再検証した。
registry `E-030`。250モジュール、252 jobs、1,154 declarations。

### 第百三十二ラウンド：剰余類ゲームの閉包（E-031）

hole-hopping規則から、小さい値の領域の力学は「穴 v に着地 → 次のクラスは v−1 (mod 3) →
そのクラスで v より下の最大の穴に着地」という決定的ゲームになる。穴 t（クラス c）を埋めるには
クラス c+1 の穴が (t, 次のクラス c の穴) に要る。852655（クラス1）の窓 (852655, 930058) には穴が
無いので現状では到達不能で、930058 の窓のクラス2の穴 930557 の窓にはクラス0の穴が無い。
しかし帯の生存を無制限とした閉包（`experiments/hole_hopping_closure.py`）は、入口クラスの順序に
よらず数百本のarcでChaffinの穴1,277,400個をほぼ全て（852655を含む）埋める。従って852655の保護は
剰余類の組合せだけでは説明できず、arcの深さ（帯の生存）に依る。

### 第百三十三ラウンド：区間先読みcensus（E-032）

simulatorに区間終端の理由と`log10(j_a/n)`、`log10(j_b/n)`のヒストグラムを追加した（10^12、43秒）。
終端は遅延着地（stopB）61%、帯の既訪問値（stopA）39%。`j_a`（帯の未訪問run長）と`j_b`（自クラスの
穴までの距離/3）はともに典型的に`n·10^−6〜10^−5`で、`j_a/n > 10^−2`は1 decadeあたり約100件。
深いarcの本数（8.45/decade）と同程度のオーダーであり、深いarcが大きな帯gapの直下で始まるという
見立てを支持する。実際の深いarcの降下と停止の規則はarc traceで確認する。

補遺：`late_landing_popup`（高さv+1から値vへ遅延着地し、v−1が既訪問なら次の3歩は全て加算で、
帯candidate v+i+1は軌道自身の直前の値なので塞がれている）を`HoleHopping`に追加した。孤立した
穴への着地の直後に軌道が時刻程度の高さへ跳ね上がる機構の局所部分である。

### 第百三十四ラウンド：深い弧のステップ trace（E-033）

`experiments/arc_trace_probe.cpp`（サブエージェント実装、親が再コンパイル）で canonical を
3×10^9 と 10^10 まで一歩ずつ再計算し、Chaffin の剰余増加で弧を検出した。`a(n)=k·n+r` と書くと
両ステップとも `r→r−k` で、弧の底は弧の最後の遅延着地である（39 弧で検証、A393814/A393815 と一致）。

深い弧（深さ>4）は 10^10 までに 6 本。6 本とも底 `v` は comb 末端で、+3 の候補 `c+v=a(c−1)` が
塞がれて `k=3` へ跳ね（`late_landing_popup`）、+4 の候補 `2c+v+2` も既訪問で `k=3/4` に固定され、
剰余が尽きるまで（689〜63,910 歩）遅延着地は起きなかった。simulator の watched 値で `2c+v+2` の
初訪問を測ると、6 本とも同じ弧が底の 2×10^4〜6×10^5 時刻前に `k=2` 値として訪問していた。

読み替え：`Φ=2·時刻+高さ`（`k=2` 上側値 −1）は `k=1/2` 段で 2 時刻に 1 増え、`k=2/3` 段で減る。
comb 末端での固定は「`Φ` が走行最大値から 3 以上下がっている」ことと同値なので、弧の底は
その弧で最初にこの落差が生じた comb 末端の高さである。landing floor は「落差 3 が初めて生じる
高さは 852656 を下回らない」と言い換えられ、カードの受入条件 3 をこの形に更新した。
`PopupLock`（k=3/4 固定の Lean 化）をサブエージェントに依頼中。

補遺：`PopupLock`（direct import `HoleHopping`）で k=3/4 固定を Lean 化した：`popup_lock_entry`、
`level34_pair`、`level34_lock`（1対ごとに k=3 offset が 5 減る）、`level34_lock_above_clock`、
`prelanding_upper_values`（k=2 候補 `2i+v+2−j` は着地前の chain の加算値）。サブエージェントが
初回で通し、親が再検証した。registry `E-034`。

### 第百三十五ラウンド：k=2/3 段の Lean 化（LevelTwoThree、E-035）

`LevelTwoThree`（direct import `PopupLock`）：`popup_return_level_two`（pop-up 後に `2c+v+2` が未訪問なら
着地して `k=2`）、`level2_to_level1`、`level23_pair`、`level23_phase`（offset −5/対）、`level23_exit`
（K 対後の出口の位置エネルギー `value+clock = 2m+s−K`）。サブエージェントは依頼文の出口の式
`2m+s−1−K` が偽であること（`a 7 = 20`, `K=0` で 20 ≠ 19）を見つけて `2m+s−K` に訂正した。
段の直前の `k=1` 時刻（高さ `s+1`、Φ `= 2m+s−1`）と比べると出口の Φ は `1−K`、すなわち
K 対の段で Φ は `K−1` 下がる。これが Φ を下げる唯一の局所機構であり、arc trace の
「comb 末端で `2c+v+2` 既訪問」による固定と合わせて、弧の底の特徴づけの全ての局所部品が
Lean 化された。

### 第百三十六ラウンド：Φ の落差の census と同値主張の撤回（arc_potential_probe、E-036）

`experiments/arc_potential_probe.cpp`（サブエージェント実装）で 10^10 までの全 comb 末端 44,422 件に
ついて blocked・continued・`Φ` の走行最大値からの落差を集計した。前ラウンドの「固定 ⟺ 落差 ≥ 3」は
偽：blocked かつ落差 < 3 が 318 件（test 値 `2c+v+2` は前の弧が `k=4` 値として訪問していた）、fresh
かつ落差 ≥ 3 が 2,745 件。39 弧で「底 = 最初の落差 ≥ 3 の comb 末端」は 0 本、「底 = 最初の blocked
comb 末端」も 0 本。`Φ` の減少 45,859 件は全て `k ≥ 3` を経由する区間で起こる。`ARC_TRACE` §5・§6 と
カードの Exact mechanism を訂正した。コミット bd5d1d2 は probe とデータのみを含み、文書訂正は
本ラウンドで着地した（前回の訂正スクリプトが全角括弧で落ちていた）。

### 第百三十七ラウンド：固定の破れと弧の死亡則（arc_death_rule_probe、E-037）

`experiments/arc_death_rule_probe.cpp`（サブエージェント実装、10^10、216 秒）で blocked な comb 末端
19,386 件の固定の結末を分類した：break 15,926、固定のまま剰余尽き（wrap）8、`k=3` 値が既訪問で
`k=5` へ 3,452、遅延着地による中断 0。`k=3→2` の候補 `2c+v−1−3i` は `i ≤ T−2` で先行する歯の
test 値、`i ≥ T−1` で `k=1/2` run の掃引値 `2c0+v0−(3(i−T+1)+1)` に一致し、run を越えた最初の候補
`i_gen = (T−1)+⌊(J_eff+2)/3⌋` で破れる（12,777/15,926、`i_obs < i_gen` の 2,551 件は全て先行する歯の
test 値が未訪問）。wrap 条件は剰余の算術から `v < 13+7·i_pred`（`k=4` 時刻 `v−6−7i ≥ 4`、`k=3` 時刻
`v−10−7i ≥ 3`）で、予測 7・見逃し 1（`c=101762018`、run の先も既訪問）・誤警報 0。36 弧の底は全て
comb 末端で、弧の終わりは wrap 8・break 後に帯を掃いても穴がない 11・fresh 後に穴がない 15・`k=5` 後 2。
`v/h_prev ≥ 0.95` が continued 42,627/42,863。深い弧 6 本のうち wrap は 35・36・37 の 3 本、30・38・39 は
`i = i_gen` で破れた後に穴なしで死んだ。landing floor は「剰余の残量と帯の run で費用が決まる
hole-hopping の降下が 852656 に届かない」命題に更新し、カードの受入条件 3 を書き換えた。

### 第百三十八ラウンド：剰余則と固定の予算の Lean 化（LockResidue、E-038）

`LockResidue`（direct import `PopupLock`）：`a n = q·n + r`（`r<n`）の座標で、両ステップとも `q ≤ r` なら
`(q, r) → (q±1, r−q)`（`residue_add`/`residue_sub`）、`r < q ≤ n` なら次の剰余は `r+(n+1)−q > r`
（`residue_wrap`、ステップ種によらない）。これが Chaffin の弧（剰余非増加区間）の終端事象である。
固定の 1 対（`a m = 3m+t`）は予算 `m+7 ≤ t` のとき剰余 `t−m → t−m−4 → t−m−7`（`level34_pair_residues`）、
`t < m+7` なら対の内部で剰余が増える（`level34_pair_wrap`、下側時刻の後のステップが加算でも減算でも）。
comb 末端座標（`m=i+5`、`t=i+v−1`）では予算が `13+7k ≤ v` になり（`popup_lock_residues`）、
`6+7K ≤ v < 13+7K` なら対 K で弧が終わる（`popup_lock_wrap`）。これは `E-037` の wrap 条件そのものである。
着地前の k=1/2 run が J 対なら `3k+1 ≤ J` の k=2 候補は `prelanding_upper_values` により軌道自身の値で
塞がれ、固定は `⌊(J+2)/3⌋` 対以上続く（`popup_lock_persists`）。これは T=1 の break 下界 `i_obs ≥ i_pred`
（10^10 の T=1 break 2,658 件は全て下界を満たす）。初回 `lake env lean` は `valuesThrough_mono` が import 外で
1 エラー、局所補題 `valuesThrough_mono_of_le` を足して通過した。残る局所部分は T≥2 の先行する歯の test 値
（経験的に 13,193/13,268 で既訪問だが定理ではない）と、固定が破れた後の降下が穴へ届く条件である。

### 第百三十九ラウンド：任意 level の ping-pong run の Lean 化（PingPongRuns、E-039）

`PingPongRuns`（direct import `LockResidue`）：`forced_addition_of_mem`（既訪問候補は加算を強制）、
`landing_of_fresh`（値未満の未訪問候補は減算を強制）、`pingpong_pair`／`pingpong_pair_residues`
（上側 `a m = (p+2)m + r` から 1 対で下側 `(p+1)(m+1)+(r−(p+2))`、上側 `(p+2)(m+2)+(r−(2p+3)) = a m + 1`、
剰余は `2p+3` 減る）、`pingpong_run`（候補形の仮定のもと K 対の run で上側値 `a m + k`、下側値
`a m − (m+k+1)`）。`DescendingChain`（p=0、剰余 −3）、`LevelTwoThree`（p=1、−5）、`PopupLock`（p=2、−7）の
共通形である。level 付きの K 対反復は `(2p+3)k` が omega の非線形項になるので候補形にとどめ、level と
剰余は 1 対の補題を各対に当てて得る設計にした。初回 `lake env lean` 一発通過。
同時に blocker provenance のカード `H-20260903-01`（test 値・固定候補・k=3 値・k=2→1 候補の初訪問の
level・弧・run 所属を 10^10 で全数調査：(A) level ≥ 2、(B) ping-pong run に属する、(C) 同じ弧なら q=2、
前の弧なら q ≥ 3）を起こし、2 パス probe をサブエージェントに依頼した。

### 第百四十ラウンド：comb が k=2/3 段の出口を塞ぐ（CombExit、E-040）

blocker provenance probe の 10^9 discovery で、fresh な comb 末端の k=2→1 候補 `c+v−3` の blocker は
85% が同じ弧の level-1 値で、gap `c−n = 7` が最頻だった。これは comb 自身の歯 `s=4`（着地 `v+4` at `c−8`）の
後の強制加算値 `c+v−3` である。一般に歯 `s` の後の加算値は `i+v+2−s`（`comb_addition_values`）で、k=2/3 段の
出口候補 `i+v−2−3k` は歯 `3k+4` の加算値なので `3k+5 ≤ T` なら既訪問（`level23_candidate_blocked_by_comb`）。
従って test 値未訪問の comb 末端の後の k=2/3 段は `⌊(T−2)/3⌋` 対以上続く（`level23_phase_of_comb`、
`popup_lock_persists` の fresh 側対応物）。`CombExit`（direct import `LevelTwoThree`・`LockResidue`）。
初回コンパイルは歯の値の上界 `v+2T ≤ i+1` が弱く omega が反例を出したので `v+3T ≤ i+1` に直して通過。
