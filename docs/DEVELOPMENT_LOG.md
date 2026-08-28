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

1. 負債位相で初出値 `y` の実軌道を解析し、目標出現、さらに早い初出時刻、
   または `anchorParent` 未満の値のいずれかを得る。
2. anchor下降の出口定理を負エポックへ輸送し、従来仮定していた
   `DiagonalSuccessorProperty` を除去する。
3. 局所前線を、座標・親の初出証明・探索地平を保持する全域的な
   `HistorySearchOracle`へ統合する。
4. `m≤n+1` を満たさない有限初期領域を、全ての可変目標について
   一様に処理できる。
5. 任意の初出値に対して、符号エポックまたは着地面機構を必ず適用できる。
6. 全ての正整数 `m` について `CoverageOracle m` を構成できる。
7. レカマン数列が全ての非負整数を含む。

したがって、全射性証明はまだ完成していません。ただし符号をまたぐ局所軌道は
三成分のwell-foundedランクへほぼ接続されました。負エポック内の唯一の
非接続分岐では、対角後継値そのものを仮定する必要はなくなり、
「値は増え得るが初出時刻が厳密に下がる blocker」を既存ランクへ輸送する問題へ
縮約されました。

## 次の証明エポック

次の主対象は、今回抽出した対角 blocker の輸送です。有望な順に、

1. `FirstAt a y fy`, `m≤y`, `fy<debtTime` から始まる負債ノード用の局所二分法を作る。
2. 新しい早期blockerなら `debtTime` を下げ、`y<anchorParent` なら通常位相へ戻す。
3. この負債オラクルを負エポック前線へ差し込み、`DiagonalSuccessorProperty` を除く。
4. 位相付きランクを全域 `PhaseSearchOracle` へ接続する。

単純な `(時刻,値)` の「どちらかが下がる」関係は循環し得るため、そのままでは
well-foundedではありません。次の設計上の核心は、時間下降を許す局面を対角負債の
一方向フェーズに限定し、通常の値下降との交互増加を防ぐ必要があります。この
位相ランク自体は今回形式化済みで、残る核心は負債ノードの局所二分法です。

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
- `Recaman/Examples.lean` — 小さい実例とfreshness反例
- `Recaman/Oracle.lean` — `+---` 局所脱出族
- `Recaman/Audit.lean` — 主要定理の公理依存監査
- `experiments/` — 10億項探索に用いた再現用C++コード（Lean証明とは分離）

`#print axioms` では、一部の証明がLean標準基礎の `propext`、
`Quot.sound`、`Classical.choice` に依存します。`sorryAx`、
ネイティブ評価公理、ユーザー追加公理への依存はありません。
