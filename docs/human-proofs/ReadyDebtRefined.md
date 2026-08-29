# ReadyDebtRefined

**役割:** ready debt(horizon-readyな強debt状態)の三種のstep障害をextended-history脱出とcrossing recovery子へ解消し、ready debtに残余のないrefined stepを与える。

## このモジュールの役割

`ReadyCurrentDebt` までで、ready debtの一歩は「目標出現/ready debt継続/`DebtStepObstruction`」に分類されていた。本モジュールは最後の障害枝を精密化する。障害は三種ある。二つの強制加算障害は、target未満の前者からtarget超の初出値へ跳ぶ真の厳密crossingなので、専用のcrossing recovery構成子へ直接入る。残る一つ、固定anchorに到達する合法減算は二時計(debtの局所時刻とhistory horizon)の中間境界であり、ここでだけ、debt値の初出時刻をrepresentativeとするhorizon-readyなextended-history証明書を使って脱出する。readinessを持ち歩いてきたおかげで、この脱出が安全に構成できる。結論として `ReadyDebtInvariant.refinedStep` は残余なしの局所stepである。

## 定理と証明

### `ReadyDebtInvariant.extendedHistoryExit` (L17)

**主張:** ready debtの値は、証明保持型のextended-history脱出を持つ。すなわちrefined domainに属する子とランク下降が存在する。旧来のbroad normal自己脱出と違い、この証明書はrepresentative time、その座標、固定history horizonでのreadinessを記憶している。

**証明:** debt値 `value` の初出時刻 `firstTime` は正なので(`debt_firstTime_pos`: 時刻0の初出値は0だが `0 < target ≤ value`)、座標 `CoordinatesAt firstTime q r` が存在する。子を

`child = ⟨horizon, a firstTime, .normal, a firstTime⟩`

とする。extended-history証明書の各フィールドを確かめる: representative `firstTime` はdebt不変量の `firstTime < horizon` からhorizon以下であり、horizon readinessはready debtの `horizon_ready` そのもの、目標下界は初出の等式 `a firstTime = value` とdebtの `target ≤ value` から従う。ランク下降は、`a firstTime = value < anchor`(debtの `value_lt_anchor`)により、debtからnormalへ位相が上がってもそれより先に比較されるanchorが厳密に下がることによる(`phaseSearch_exitDebt_of_anchorDrop`)。horizonは不変なので履歴予算も変わらず、辞書式第二成分の下降で進捗する。

### `ReadyDebtInvariant.obstruction_refinedStep` (L52)

**主張:** ready debtの各障害から、目標出現またはrefined子への厳密下降が得られる。強制加算障害は正確なcrossing証明書を保持し、合法のanchor到達境界だけが上のextended-history脱出を使う。

**証明:** 障害の三構成子で場合分けする。

**(1) `legal_reaches_anchor`:** debt値の初出が、anchor以上の前者からの合法減算で生じていた場合である。前者をanchorの下降に使えないため、debt側での前進は止まる。しかしdebt値の初出時刻はdebtの局所時刻に等しくhistory horizonより早い — まさに二時計の中間区間 — であり、readinessを持つ今はL17のextended-history脱出がそのまま子とランク下降を与える。

**(2) `addition_nonpositive`:** 初出が強制加算 `value = a n + (n + 1)` で生じ、前者は `a n < target`、減算不能の理由は候補の非正値性である場合。`target ≤ value` なので、これはtarget未満からtarget以上への上向き横断である。既存定理 `debtCrossing_enters_recovery` が、目標出現か、または横断後状態の座標付きcrossing recovery不変量とランク下降を返す。後者では子

`child = ⟨horizon, a n, .normal, a n⟩`

(anchorをtarget未満のpre-crossing値 `a n` に置いた数値的にはnormalなnode)が `CrossingSearchInvariant` を満たす: 旧anchor・crossing時刻 `n`・横断後座標を保持するcrossing証明書がそのまま組める。

**(3) `addition_seen_below_target`:** 同じく強制加算による横断だが、減算不能の理由がtarget未満の候補の既出である場合。処理は(2)と同一で、`debtCrossing_enters_recovery` により目標出現またはcrossing recovery子を得る。

### `ReadyDebtInvariant.refinedStep` (L101)

**主張:** ready debtはrefined domainで残余のないstepを持つ。すなわち目標出現、またはrefined子への厳密下降のいずれかが必ず成り立つ。

**証明:** `readyCurrentOrDebtStep_or_obstruction`(ReadyCurrentDebt)で三分類する。目標出現はそのまま。通常継続はready debtに留まるので、包含写像でrefined domainのstepになる。障害はL52で解消する。

## 全体の中での位置づけ

証明地図の「historical回避: refined閉包済み」と「refined child: 非crossing閉包済み」の両段に属する。`OrbitReadyDirectRefined.lean`(normal側)・`ExtendedHistoryDirectRefined`(extended-history側)と並んで、refined child domain三成分のうちdebt成分の局所totalityを担う。本モジュールの(2)(3)で生成されるcrossing recovery子は、constructor監査後に唯一残る未処理証明書 `CrossingSearchInvariant` の供給源のひとつであり、その後の解析は `RefinedOracleBoundary`・`CrossingRefinedBoundary` 以降のcrossingモジュール群に引き継がれる。
