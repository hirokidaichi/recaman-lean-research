# HistoricalDebtBridge

**役割:** parent-dropとcrossing frontierが生成する初出anchorを、初出時刻で二分して「current normal子」または「強いdebt子」へ送り、historical normal子を回避する。debt親特有の二時計区間だけが残余として明示される。

## このモジュールの役割

位相探索の弱い通常構成子は、過去に初出した値と後のhorizonを組み合わせた「historical normal node」を作れてしまい、そこからは局所エポック定理を適用できない(`NormalSemanticBoundary`)。本モジュールは、historical normal子を生成しかねない二つの機構 — 通常親のparent-drop(親のanchorより小さい初出値への降下)と、debt親のcrossing frontier(debt anchorより小さい初出値の発見)— について、見つかった初出値の初出時刻を親の時計と比較して分解する: 初出が未来ならorbit-ready(用語集: 局所値が実際に `a(time)` で座標と時刻条件を持つ)なcurrent normal子、過去なら強い`DebtInvariant`を満たすdebt子になり、どちらもhistorical normal子を経由しない。通常親は時計が一つなので分解は完全だが、debt親はhistory horizonとdebt局所時刻という二つの独立な時計を持つため、`debtTime ≤ firstTime < historyHorizon` の中間区間が本物の残余として残る。本モジュールはこの区間を `CrossingFrontierMiddleResidual` として正確に記録し、実軌道の実例を与え、さらに通常のdebt発展はhistorical self-exitを一切使わずに閉じられること(`debtStep_classify_without_normalExit`)も証明する。

冒頭の補助補題 `historicalBridge_firstTime_pos`(L7、private)は、正の目標以上の値の初出時刻が正であることを示す1行の補題である(時刻0の初出値は0に限るため)。

## 主要な定義

### `ParentDropCurrentChildCertificate` (L34)

parent-dropの未来枝の証明書。`target < value`、初出 `FirstAt a value firstTime`、`parentTime ≤ firstTime`(未来性)、`value < activeParent`(anchor下降)に加え、current開始ノード `targetStartNode firstTime = ⟨firstTime, a(firstTime), normal, a(firstTime)⟩` の`OrbitReadyNormalInvariant`と、親からの`PhaseSearchProgress`を保持する。

### `ParentDropDebtChildCertificate` (L44)

parent-dropの過去枝の証明書。`firstTime < parentTime` と、ノード `⟨parentTime, activeParent, debt, firstTime⟩` の強い`DebtInvariant`、およびnormal→debtの`PhaseSearchProgress`を保持する。

### `ParentDropCurrentDebtOutcome` (L58)

parent-dropの完全な結果: 目標出現、current子、debt子の三構成子。historical normal子の構成子は存在しない。

### `CrossingFrontierCurrentChildCertificate` (L166) / `CrossingFrontierDebtChildCertificate` (L175)

crossing frontier(debt親のanchor未満に現れた初出値)に対する、上と同形のcurrent枝・debt枝の証明書。debt枝では初出時刻がdebt局所時刻より真に早いこと(`firstTime < debtTime`)を要求する。

### `CrossingFrontierMiddleResidual` (L193)

debt親の二時計が残す正確な区間。`target < value`、初出、anchor下降に加え、`debtTime ≤ firstTime < historyHorizon`(debt時刻を下げられず、horizonより過去)であり、current子になれない理由 `current_failure` を保持する: 初出時刻の時計が目標に届かない(`firstTime + 1 < target`)か、初出時刻からhorizonまでの間に目標未満の履歴が消費されている(`missingBelowCount target historyHorizon < missingBelowCount target firstTime`)。

### `CrossingFrontierCurrentDebtOutcome` (L204)

crossing frontierの結果: 目標出現、current子、debt子、middle残余の四構成子。

### `DebtClosedOutcome` (L415)

`exit_normal`構成子を持たないdebt一歩の結果型: 目標出現、debt継続、crossing障害(`DebtStepObstruction`)の三構成子のみ。

## 定理と証明

### `normalParentDrop_currentOrDebt` (L71)

**主張:** 目標が正で、親が時刻準備済み(`target ≤ parentTime + 1`)のcurrent normalノード `⟨parentTime, activeParent, normal, a(parentTime)⟩` であるとき、parent-dropの証拠(`target ≤ value < activeParent` を満たす初出値)からは、目標出現・current子・debt子のいずれかが必ず得られる。

**証明:** `value = target` なら初出時刻が出現の証人である。以下 `target < value` とし、初出時刻を親の時計と比較する。

*未来の場合(`parentTime ≤ firstTime`)。* 目標が正なので初出時刻は正であり、時刻`firstTime`の商・剰余座標が存在する。`a(firstTime) = value` だから、`targetStartNode firstTime` は orbit-ready 証明書のすべての条項を満たす: 時刻条件は `target ≤ parentTime + 1 ≤ firstTime + 1` と親の準備性から遺伝する。ランク進捗は、horizonを前へ延ばすと履歴予算(`missingBelowCount`)は増えない(反単調)ことと、anchorが `value < activeParent` で真に下がることの辞書式合成である(`phaseSearchProgress_of_horizonAndAnchor`)。

*過去の場合(`firstTime < parentTime`)。* ノード `⟨parentTime, activeParent, debt, firstTime⟩` が強い`DebtInvariant`の六条項(位相・局所量は構成通り、`target ≤ value`、初出、`firstTime < parentTime = horizon`、`value < activeParent`)をすべて満たす。ランク進捗はnormal→debtの位相下降(`phaseSearch_enterDebt`)である。

### `NormalPhaseInvariantAt.parentDrop_currentOrDebt` (L136)

**主張・証明:** 既存の負ポテンシャルcurrent不変量 `NormalPhaseInvariantAt` から時刻準備性を読み出して前定理へ渡す直接のアダプタである。

### `ParentDropCurrentDebtOutcome.toCurrentOrDebtStep` (L147)

**主張:** parent-dropの結果は、精密化された一段インターフェース「目標出現、または `CurrentOrDebtInvariant`(orbit-ready normalまたは強いdebt)を満たす子への`PhaseSearchProgress`」へ忘却できる。

**証明:** 三構成子それぞれの証明書から対応する選言肢を組み立てるだけの場合分けである。

### `crossingFrontierFirstAt_currentOrDebt_or_middle` (L229)

**主張:** 強い`DebtInvariant`を満たすdebt親 `⟨historyHorizon, debtAnchor, debt, debtTime⟩` がhorizon準備済み(`target ≤ historyHorizon + 1`)のとき、frontier初出値(`target ≤ value < debtAnchor`)からは、目標出現・current子・debt子・middle残余のいずれかが必ず得られる。拡大されたhistorical normal子は作らない。

**証明:** `value = target` なら出現。以下 `target < value` とし、初出時刻を二つの時計と比較する。

*debt時刻より早い場合(`firstTime < debtTime`)。* 親の不変量から `firstTime < debtTime < historyHorizon` なので、同じhorizon・anchorのままdebt局所時刻だけを下げた強いdebt子が構成でき、debt時刻下降のランク進捗を持つ。

*horizon以後の場合(`historyHorizon ≤ firstTime`)。* parent-dropの未来枝と同様にorbit-readyなcurrent子 `targetStartNode firstTime` を作る。時刻条件は `target ≤ historyHorizon + 1 ≤ firstTime + 1`。ランク進捗は「horizon延長で予算は増えず、anchorが `value < debtAnchor` で真に下がる」ことによる(`phaseSearch_exitDebt_of_extendedHorizonAndAnchor`)。

*中間区間(`debtTime ≤ firstTime < historyHorizon`)。* current子 `targetStartNode firstTime` はhorizonを過去へ引き戻すため、二つの障害がある。第一に自前の時計が目標に届く必要がある(`target ≤ firstTime + 1`)。第二に、予算は反単調なので引き戻しで増えることはあっても減ることはなく、増えたら第一ランク成分が上がってしまう — したがって等式 `missingBelowCount target historyHorizon = missingBelowCount target firstTime` が必要である。両方成り立てば、第一成分は等しいままanchor成分が真に下がる辞書式進捗を直接構成してcurrent子とする。時計条件が破れれば `firstTime + 1 < target`、予算等式が破れれば狭義の予算ギャップとして、いずれも`CrossingFrontierMiddleResidual`に記録する。

### `CrossingFrontierCurrentDebtOutcome.toCurrentOrDebtStep_or_middle` (L354)

**主張・証明:** 前定理の結果を「目標出現 ∨ (`CurrentOrDebtInvariant`子と進捗) ∨ middle残余」の三選言へ忘却する場合分けである。

### `CrossingFrontierNormalProvenance.currentOrDebt_or_middle` (L378)

**主張:** 型付きprovenance(生成元証明)パッケージ `CrossingFrontierNormalProvenance` は、debt horizonの目標準備性を仮定すれば、上の四分類へ直接接続する。

**証明:** パッケージを展開して、その中のdebt親不変量・frontier初出・anchor下降を主定理へ渡すだけである。

### `crossingFrontierMiddleResidual_actual` (L395)

**主張:** middle区間は実在する: `CrossingFrontierMiddleResidual 5 4 7 3 6 3`。最初の厳密crossingのdebt状態で、`a(3) = 6` は目標5より上・anchor 7より下だが、時刻3は目標準備済みでなく(`3 + 1 < 5`)、debt horizonは4である。

**証明:** `FirstAt a 6 3` は`decide`と時刻0〜2の個別確認により、残りの数値条件もすべて`decide`で検証する。

### `debtStep_classify_without_normalExit` (L433)

**主張:** `debtStep_classify`の強化: 有効なdebtノードの一歩は、`exit_normal`構成子なしの `DebtClosedOutcome`(目標出現・debt継続・crossing障害)に必ず落ちる。

**証明:** 骨格は`debtStep_classify`と同一である。唯一の相違は強制加算で先行値が目標以上の場合の扱いで、そこで通常位相へ脱出する代わりに先行値をdebtに留める。これが可能な理由は、強制加算の先行値 `a(n)` が三つの性質を同時に持つからである: 初出時刻が旧debt時刻より真に早い(`predecessorTime < n+1 < horizon`)、固定anchorより真に小さい(強制加算では自動的)、目標以上(この枝の仮定)。ゆえに`DebtInvariant`の六条項が揃い、debt時刻下降の進捗付き`continue_debt`になる。他の枝(合法減算のanchor到達、目標未満へのcrossing二種)は元の分類と同じく`crossing`障害へ送る。この定理により、通常のdebt発展はhistorical normal子を作るself-exitを構造的に必要としないことが確定する。

### `DebtClosedOutcome.toDebtStep_or_obstruction` (L489)

**主張・証明:** `DebtClosedOutcome`を「目標出現 ∨ (debt子と進捗) ∨ `DebtStepObstruction`」の素の選言へ忘却する場合分けである。

### `debtSelfExit_is_middle_boundary` (L510)

**主張:** debtのhistorical self-exit(`debtInvariant_exitNormal_at_value`による自分の値での脱出)は、正確に二時計区間の境界に位置する: その初出時刻は `firstTime < horizon` を満たし、horizon以後でもなく(current子になれず)、自分自身より早くもない(debt時刻を下げられない)。

**証明:** debt不変量の `firstTime < horizon` と、`≤`・`<`の自明な算術による。内容は軽いが、self-exitが本モジュールの分解のどの枝にも入らない「まさに残余そのもの」であることを明文化し、self-exitを避ける設計(`debtStep_classify_without_normalExit`)の必要性を裏付ける。

## 全体の中での位置づけ

証明地図の「historical回避」段階(refined閉包済み)の中心モジュールである。`CoverageDebtBridge`(current親のCoverageStepの分解)、`TypedNormalProvenance`(生成元の型付け)、`DebtStep`をimportして構築され、`ReadyDebtInvariant`(horizon-ready debt)と`OrbitReadyRefinedStep`から使われる。ここで残余として単離された二時計middle区間は、後続の`CrossingFrontierRefined`が「ready debt源のhorizon準備性を継承するextended-history子」として収容し、これによりrefined child domainの構成子監査は`CrossingSearchInvariant`一つにまで縮約される。すなわち本モジュールは、「historical normal nodeを探索domainから排除する」というプロジェクト後半の方針を、parent-drop・crossing frontier・通常debt発展の三方向で実装した橋である。
