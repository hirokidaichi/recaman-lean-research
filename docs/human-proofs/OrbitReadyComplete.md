# OrbitReadyComplete

**役割:** orbit-ready normal node(現在軌道状態+時刻準備+座標を持つnormal node)のポテンシャル符号を完全分類し、低レベル帯 `0 ≤ G ≤ 2` も含めて残余のない局所semantic stepを与える。

## このモジュールの役割

broadなordinary-normal証明書には「現在値が本当に `a time` である」ことと絶対時刻条件 `target ≤ time + 1` が欠けており、そのままでは局所epoch定理を適用できない(`NormalSemanticBoundary` の反例)。`OrbitReadyNormalCertificate` はこの二条件を復元した証明書であり、本モジュールはそのような状態におけるポテンシャル `G = potential q r`(座標 `(q, r)` に対する `r − upperTri(q)`)のあらゆる符号を分類する。負ポテンシャルは完成済みの負normal定理で閉じ、目標以上の非負ポテンシャルは(商0の強制加算一歩の先読みを含めて)被覆へ落ち、非負アンダーシュートはまずレベル帯 `0, 1, 2` へ縮約され、最後にその帯自体も閉じる。結論として、orbit-ready normal nodeは「目標出現、またはsemantic domainの子への厳密ランク下降」という完全な局所two択(local totality)を持つ。

## 主要な定義

### `OrbitReadyLowLevelResidual` (L23)

orbit-ready normal nodeに対する正確な低レベル境界。強化されたnode証明書 `OrbitReadyNormalCertificate` と、非負エポック解析が返す完全な数値境界 `NonnegativeLowLevelResidualAt`(時刻準備、目標下界、座標、商の正値性、`potential q r = level`、`level ≤ 2`、`level < target`)の両方を保持する唯一の構成子 `low` を持つ。

## 定理と証明

### `zeroQuotient_potential_aboveTarget_phaseSemanticStep` (L38)

**主張:** 商0の座標 `(0, r)` を持つ時刻 `n` で `target ≤ potential 0 r` なら、目標が出現するか、semantic子への厳密ランク下降が存在する。

**証明:** 商0では `a n = r` かつ `potential 0 r = r` なので、仮定は `target ≤ r` を意味する。`a n = target` なら出現である。そうでなければ `target < r`。商0では減算候補 `r − (n+1)` が負になるため加算が強制され、遷移後の座標は `(1, r)`、すなわち `a (n+1) = (n+1) + r` である。この配置のポテンシャルは `r − 1` であり、補題 `lowQuotient_level_seen_next` により値 `r − 1` は時刻 `n + 2` までの履歴に必ず現れる(次の減算候補がちょうど `r − 1` で、合法なら実際に着地し、塞がれるなら既出だからである)。その初出時刻を取れば、`target ≤ r − 1 < r = a n` を満たすblockerとなり `CoverageStep` が得られる。これを `canonicalCoverage_phaseSemantic` でsemantic stepへ変換する。

### `quotientOne_forcedAddition_phaseSemanticStep` (L79)

**主張:** 商1の座標でレベル `level`(`potential 1 r = level`)を持ち、`target < a n`、減算不能なら、一遷移先で被覆が露出する。すなわち目標出現またはsemantic子への下降が得られる。

**証明:** 商1では `r = 1 + level`、したがって `a n = n + 1 + level` である。強制加算により `a (n+1) = 2n + 2 + level` となる。その次の減算候補は

`a (n+1) − (n+2) = n + level =: candidate`

である。この候補は目標以上である: `level = 0` なら `target < a n = n + 1` より `target ≤ n = candidate`、`level ≥ 1` なら時刻準備 `target ≤ n + 1 ≤ n + level` による。また `candidate = n + level < n + 1 + level = a n` なので、旧値よりちょうど1小さい。候補は正なので `n + 2 < a (n+1)` も成り立つ。ここで二歩目を場合分けする。減算が合法なら `a (n+2) = candidate` が新しい初出(freshな出現)となり、`(candidate, n+2)` がblockerになる。減算が塞がれるなら、値が正である以上その理由は「既出」しかなく、既出性から `candidate` の初出時刻が取れる。どちらの場合も `target ≤ candidate < a n` のblockerによる `CoverageStep` が得られ、semantic stepへ変換される。

### `OrbitReadyLowLevelResidual.phaseSemanticStep` (L137)

**主張:** 低レベル境界それ自体も局所完全である。すなわち残余からも目標出現またはsemantic子への下降が導ける。

**証明:** 残余の時刻 `n` で `a n = target` なら出現。そうでなければ `target < a n` である。次の減算が合法なら、above-target合法減算の既存閉包 `canonical_legalSubtraction_phaseSemantic` が直接子を与える。塞がれている場合は商で分ける: `q = 1` ならL79の強制加算先読み、`q ≥ 2` なら一般の二商履歴frontier `canonical_forcedAddition_twoQuotient_phaseSemantic` を使う(残余の `quotient_positive` により `q = 0` はあり得ない)。

### `OrbitReadyNormalCertificate.phaseSemanticStep_or_lowLevel` (L166)

**主張:** 一つのorbit-ready証明書に対する完全な符号分類。結論は、目標出現、semantic子への下降、または明示的な低レベル残余(レベル高々2)の三択である。

**証明:** ポテンシャルの符号で分ける。

1. `potential q r < 0`(負領域): 証明書から負normal不変量が組めるので、完成済みの `negative_phaseSemanticStep` が出現または子を返す。
2. `target ≤ potential q r`(目標面以上): `q = 0` ならL38を適用する。`q ≥ 1` なら、まず `time > 0` を確かめる(`time = 0` なら `a 0 = 0` が目標下界と矛盾)。すると `positiveQuotient_potential_aboveTarget_gives_coverageStep` が `CoverageStep` を与え、semantic stepへ変換できる。
3. `0 ≤ potential q r < target`(非負アンダーシュート): 非負エポックの完全分類 `nonnegative_epoch_phaseSemanticStep_or_lowLevel` を適用する。正則レベル `g ≥ 3` は閉じ、残るのはレベル `0, 1, 2` の数値境界だけなので、それを証明書と束ねて `OrbitReadyLowLevelResidual` として返す。

### `OrbitReadyNormalInvariant.phaseSemanticStep_or_lowLevel` (L216)

**主張:** 存在量化版。どの座標が readiness を証言していても同じ三択が成り立つ。

**証明:** 存在量化を開いてL166を適用する。

### `OrbitReadyNormalCertificate.phaseSemanticStep` (L228)

**主張:** 証明書レベルの完全局所閉包。目標出現またはsemantic子への下降の二択であり、残余はない。

**証明:** L166の三択のうち低レベル残余をL137で解消する。

### `OrbitReadyNormalInvariant.phaseSemanticStep` (L243)

**主張:** orbit-ready normal nodeの完全な現在状態局所semantic step。すべてのポテンシャル符号、商0、レベル0〜2が既存のsemantic domainと位相ランクの中で処理される。

**証明:** 存在量化を開いてL228を適用する。

## 全体の中での位置づけ

証明地図の「意味的探索domain」段の中核であり、`PROOF_MAP.md` にいう「`OrbitReadyNormalInvariant.phaseSemanticStep` は負・高ポテンシャル・非負undershoot・level 0/1/2をすべて閉じ、current-state normalの局所totalityを与える」がこのモジュールの成果である。ただしここでの子はbroadな `PhaseSemanticInvariant` として返るため、horizon clockなどの生成時データが失われる。`OrbitReadyRefinedStep.lean` はこの黒箱の出力を構成子検査で精密化して残余を特定し、`OrbitReadyDirectRefined.lean` は同じ分岐構造を忘却前に辿り直して残余のないrefined stepを構成する。L38・L79の二定理は後者でもrefined版(`zeroQuotient_potential_aboveTarget_refinedStep` など)の原型として再利用される。
