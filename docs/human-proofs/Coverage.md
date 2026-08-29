# Coverage

**役割:** 全射性予想を「各探索ノードで一段の進捗を返す」証明義務(`CoverageStep` / `CoverageOracle`)へ還元し、値に関する整礎帰納で停止性を証明する。

## このモジュールの役割

このモジュールは本研究の大域探索の背骨である。目標 `m` の出現証明を、
「`m` 以上の初出値 `v` を親として、`m` の出現そのものか、`m ≤ y < v` を満たす
より小さい初出値 `y` を返す」一段の証明 `CoverageStep` に分解する。親の値は
自然数として真に減り続けるので、この一段をすべての親について供給できれば
(`CoverageOracle`)、強帰納法により有限回で `m` に到達する。ここでのoracleは
外部の神託ではなく、局所機構が果たすべき証明義務を抽象化した名前である。
oracleを仮定した停止証明はこのモジュールで完結しており、oracleの構成そのものが
以降のモジュール群の課題になる。

## 主要な定義

### `TargetResolvable` (L8)

`TargetResolvable m` は、「`m` より大きいすべての初出値 `v`(初出時刻 `f`)に対し、
ある歩数 `k` で目標方程式 `TargetEquation f v m k` が成り立つ」という強い算術条件で
ある。目標方程式とは `v = m + k·f + upperTri k`、すなわち `k` 回の連続減算の予定が
ちょうど `m` に届くことを言う。blocker帰納に必要な算術条件を切り出したものである。

### `CoverageStep` (L17)

`CoverageStep m v f` は、大域証明の許容される一段である:

1. `∃ t, a t = m`(目標がすでに出現している)、または
2. `m ≤ y < v` を満たす値 `y` とその初出時刻 `fy` が存在する。

第二の場合、親の値が真に小さくなることだけが後の強帰納法に必要な条件であり、
blocker構成がしばしば与える初出時刻の降下は追加情報にすぎない。親の時刻引数 `f` は
この定義では使われない(値に関する再帰だから)。

### `CoverageOracle` (L24)

`CoverageOracle m` は、「`m ≤ v` なるすべての初出値 `v`(初出時刻 `f`)について
`CoverageStep m v f` を返せる」という柔軟な証明義務である。`TargetResolvable` と
異なり、直接下降・完全ゲート・局所脱出など、どの証明済み機構で果たしてもよい。

## 定理と証明

### `CoverageStep.mono_parent` (L29)

**主張:** `CoverageStep m v f` と `v < V` から `CoverageStep m V F` が従う。
親の時刻は任意でよい。

**証明:** 出現枝はそのまま。降下枝では `y < v < V` と推移律で親を差し替える。
大域再帰は値についてのものなので、時刻は関与しない。補助補題。

### `CoverageStep.lower_target` (L38)

**主張:** より高い中間目標 `M` を狙った一段は、`m ≤ M < v` なるすべての低い目標 `m` も
解決する: `CoverageStep M v f` から `CoverageStep m v f`。

**証明:** 出現枝で `m = M` ならそのまま。`m < M` なら、出現した `M` 自身が
`m ≤ M < v` を満たす初出値なので(出現する値は初出時刻を持つ)、降下枝の証人になる。
降下枝では `m ≤ M ≤ y` と下界を弱めるだけである。

### `exists_firstAbove` (L53)

**主張:** 任意の下界 `m` の上に、実際に出現する初出値がある:
`∃ v f, m < v ∧ FirstAt a v f`。

**証明:** 大域的な非有界性定理は不要で、二時刻だけ調べれば足りる。`m < a m` なら
`a m` 自身が証人である(現在値は履歴に属し、履歴の要素は初出時刻を持つ)。
`a m ≤ m` なら時刻 `m+1` の減算候補 `a m − (m+1)` は正でないため加算が強制され、
`a (m+1) = a m + (m+1) > m` となってこちらが証人になる。いずれの場合も
その値の初出時刻を履歴から取り出す。

### `targetResolvable_reaches_from` (L74)

**主張:** `m > 0` と `TargetResolvable m` のもとで、`m < v` なる任意の初出値 `v` から
出発すれば `∃ t, a t = m`。

**証明:** 値 `v` に関する強帰納法(初出時刻 `f` は一般化しておく)。仮定から
目標方程式 `TargetEquation f v m k` が得られるので、有限下降二分法
`targetDescent_lands_or_doubleDescent` を適用する。

- 着地枝なら `a (f + k) = m` で完了。
- 阻止枝なら `m ≤ y < v` なる初出値 `y`(初出時刻 `fy`)を得る。`y = m` なら
  `y` の初出がそのまま目標の出現である。`m < y` なら `y < v` なので帰納法の仮定を
  `y` に適用する。

値は各段で真に減る自然数なので、この再帰は必ず停止する。

### `coverageOracle_reaches_from` (L91)

**主張:** 本研究計画の背後にある汎用整礎帰納。`CoverageOracle m` のもとで、
`m ≤ v` なる任意の初出値 `v` から `∃ t, a t = m`。

**証明:** 値 `v` に関する強帰納法。oracleが返す `CoverageStep` の出現枝なら完了、
降下枝なら `m ≤ y < v` の子に帰納法の仮定を適用する。証明はこれだけであり、
局所機構の複雑さはすべて oracle の側に隔離されている。

### `coverageOracle_implies_occurs` (L102)

**主張:** `CoverageOracle m` ならば `∃ t, a t = m`。

**証明:** `exists_firstAbove` で `m` より上の初出値を一つ取り、
`coverageOracle_reaches_from` で降りる。

### `targetResolvable_implies_coverageOracle` (L109)

**主張:** `m > 0` のとき、`TargetResolvable m` は `CoverageOracle m` を構成する
ひとつの(意図的に強い)方法である。

**証明:** 親 `v` について `m = v` なら初出そのものが出現枝。`m < v` なら目標方程式を
取り、有限下降二分法の着地枝を出現枝に、阻止枝を降下枝に写す。

### `targetResolvable_implies_occurs` (L124)

**主張:** 目標ひとつ分の条件付き被覆定理。`m > 0` と `TargetResolvable m` から
`∃ t, a t = m`。

**証明:** `exists_firstAbove` と `targetResolvable_reaches_from` の合成である。

### `all_targetResolvable_implies_surjective` (L132)

**主張:** すべての正の目標について `TargetResolvable` が成り立てば、レカマン数列は
非負整数全体を被覆する: `∀ m, ∃ t, a t = m`。

**証明:** `m = 0` は `a 0 = 0`。正の `m` は前定理による。

### `all_coverageOracles_imply_surjective` (L144)

**主張:** 最終的な大域定理の雛形。各正の目標に対する `CoverageOracle` の構成が、
レカマン被覆予想の証明に十分である。

**証明:** `m = 0` は `a 0 = 0`、正の `m` は `coverageOracle_implies_occurs` による。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「大域値帰納」であり、状況一覧では「証明済み」に
分類される。入力側は `TargetDescent.lean` の有限下降二分法だけであり、出力側の
`CoverageStep` は本リポジトリの共通通貨になっている: `Mechanisms.lean` は各局所機構を
`CoverageStep` に変換し、`PrestateCoverage.lean` は借り付き遷移から pre-state の
`CoverageStep` を作り、さらに `HistoryBudget.lean` や `PhaseSearch.lean` の
多成分ランク探索も、最終的にはここで定義された一段の形へ帰着する。未証明として
残っているのは、`all_coverageOracles_imply_surjective` の仮定、すなわちすべての
局所状態に対する oracle の構成である。
