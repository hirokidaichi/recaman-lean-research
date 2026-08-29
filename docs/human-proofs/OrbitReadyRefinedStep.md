# OrbitReadyRefinedStep

**役割:** refined child domain `OrbitReadyRefinedInvariant` を定義し、broad semantic childの構成子検査でどこまで精密化できるかを確定して、欠けている情報が「horizon clock一つ」だけであることを正確な残余として切り出す。

## このモジュールの役割

`OrbitReadyComplete` の局所閉包は完全だが、子をbroadな `PhaseSemanticInvariant` として返すため、機構ごとの証明データ(現在性、horizonのclock条件など)を消してしまう。本モジュールは、その黒箱出力を構成子ごとにパターンマッチして回収できる限りを回収する。canonical子はorbit-ready、crossing recovery子はcrossing証明書ごと、debt子はhorizonがtarget-readyならready debt、ordinary normal子はhorizonがtarget-readyなら保存済みの初出をrepresentativeとするextended-history nodeへ昇格できる。昇格できないのは、broadなnormal/debt構成子がhorizon clock条件そのものを保持していない場合だけであり、その欠落を `OrbitReadyRefinedChildResidual` として明示する。これは未証明のrefined successorを主張するものではなく、「黒箱経由の精密化の限界がちょうどこの一フィールドである」ことの確定である。

## 主要な定義

### `OrbitReadyRefinedInvariant` (L27)

現在監査済みのnormal/debt/history機構から到達可能な、証明保持型のrefined child domain:

`ReadyCurrentOrDebtInvariant target node ∨ ExtendedHistoryNormalInvariant target node ∨ CrossingSearchInvariant target node`

すなわち、(1) orbit-readyな現在normalまたはhorizon-readyなdebt、(2) representative time(値と座標が実際に成立する軌道時刻)とhistory horizon(履歴予算を測る後の時刻)を分離しつつ両者のclock条件を持つextended-history normal、(3) 強制加算によるtarget横断を記録したcrossing recovery node、の三種である。

### `OrbitReadyRefinedChildResidual` (L51)

broad semantic childを検査した後に残る正確な証明データの欠落。二構成子を持つ:

- `normal_horizon_not_ready`: broadなnormal証明書とランク下降はあるが `child.horizon + 1 < target`。
- `debt_horizon_not_ready`: 強いdebt証明書とランク下降はあるが `child.horizon + 1 < target`。

normal子ではrepresentative dataは `NormalSearchCertificate` に全部あるので、欠けているのはhorizonでのtarget readiness一つだけである。debt子でも強い不変量は既にあり、同じclockフィールドだけが欠けている。

## 定理と証明

### `OrbitReadyRefinedInvariant.toPhaseSemanticInvariant` (L34)

**主張:** すべてのrefined childは既存のsemantic domainに埋め込まれる。

**証明:** 三枝それぞれの既存埋め込みを使う。extended-history枝は存在量化を開いて証明書の埋め込みを、crossing枝はsemantic domainの `crossing_recovery` 構成子を使う。

### `phaseSemanticChild_refine_or_horizonResidual` (L69)

**主張:** 一つのbroad semantic child(とその厳密ランク下降)は、refined domainへ昇格できるか、さもなくば上記の残余になる。この分類は `PhaseSemanticInvariant` の構成子について完全である。

**証明:** semantic不変量の四構成子で場合分けする。

1. `canonical_start`: canonical start証明書は時刻準備・値下界・座標を全て持つので、orbit-ready不変量へ直接変換し、refined domainの第一成分(current側)に入れる。
2. `normal`: 子のhorizonについて `target ≤ child.horizon + 1` かどうかで分ける。成り立つ場合、broadな `NormalSearchCertificate` が保存している初出時刻 `firstTime` をrepresentative timeに選ぶ。証明書のnode等式・`firstTime ≤ horizon`・目標下界・初出時刻での座標がそのままextended-history証明書のフィールドになり(値の等式は初出 `a firstTime = value` で書き換える)、horizon readinessは場合分けの仮定である。成り立たない場合は `normal_horizon_not_ready` 残余を返す。
3. `debt`: 同じくhorizon readinessで分ける。成り立てば強いdebt証明書と対にして `ReadyDebtInvariant` を作り、refined domainの第一成分(debt側)へ。成り立たなければ `debt_horizon_not_ready` 残余。
4. `crossing_recovery`: crossing証明書は失うものがなく、そのまま第三成分に入る。

いずれの昇格枝でも元のランク下降は変形なしに保持される。

### `OrbitReadyNormalInvariant.refinedStep_or_horizonResidual` (L124)

**主張:** 現在の黒箱orbit-ready step(`OrbitReadyNormalInvariant.phaseSemanticStep`)から得られる最大限の精密化。目標出現はそのまま、返されたsemantic childは、broadなnormal/debt証明書が子horizonのreadiness条件を欠いていた場合を除き、すべて証明保持型refined domainへ昇格される。

**証明:** まず黒箱stepを実行して出現か子を得る。子が得られた場合、目標の正値性をorbit-ready証明書から取り出し、L69の分類を適用する。昇格できればrefined child、できなければ残余をそのまま返す。

### `broadNormalChild_can_lack_horizonReadiness` (L149)

**主張:** 残余はbroadなnormal構成子の情報不足を実際に反映している。具体的に、目標 `6` に対する時刻 `3` の標準的normal証明書 `NormalSearchInvariant 6 ⟨3, a 3, .normal, a 3⟩` は成立するが、`6 ≤ 3 + 1` は成立しない。

**証明:** `NormalSemanticBoundary` の既存反例 `normalSearchInvariant_does_not_imply_time_ready` の言い換えである(`a 3 = 6` なので値の条件は満たすが、horizon `3` のclockは目標 `6` に達しない)。この定理は当該nodeがorbit-ready stepの実際の出力だと主張するものではなく、構成子検査だけではすべてのbroad normal childを昇格できない理由を分離するものである。

## 全体の中での位置づけ

証明地図の「refined child」段の入口である。ここで確定した残余(horizon clockの欠落)への解答が二方向に分かれる。第一に `ReadyDebtInvariant.lean`・`ReadyCurrentDebt.lean` は、clock条件を最初から持ち歩くdomainを整備する。第二に `OrbitReadyDirectRefined.lean` は、黒箱を経由せず生成分岐を忘却前に辿ることで、`OrbitReadyRefinedInvariant` のstepを残余なしで直接構成する(本モジュールのdomain定義はそこで結論の型として使われる)。この後、constructor監査で残る未処理は `CrossingSearchInvariant` 自身のみとなり、`RefinedOracleBoundary` 以降のcrossing解析へ引き継がれる。
