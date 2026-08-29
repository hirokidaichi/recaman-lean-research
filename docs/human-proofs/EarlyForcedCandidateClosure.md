# EarlyForcedCandidateClosure

**役割:** early representative 残余のうち forced-below-candidate 分岐を、将来の弱上方 crossing から crossing recovery 子を構成して既存の四成分ランクのまま閉じ、残余を legal downcross 一種類に縮約する。

## このモジュールの役割

extended-history 監査で残った early representative(代表時刻が `representativeTime + 1 < target` を満たし、epoch API には早すぎる historical ノード)の一歩分類 `EarlyRepresentativeOutcome` には、二つの残余分岐があった。本モジュールはそのうち forced_below_candidate 分岐、すなわち「強制加算で塞がれた減算候補 `a n − (n+1)` が正で target 未満、しかも既出」という配置を完全に閉じる。鍵は、既出の below-target 候補の出現時点から代表状態までの区間に必ず forced-addition の上方横断(weak upcrossing)が存在し、その pre-crossing 値が target 未満、したがって旧代表 anchor より厳密に小さいことである。crossing を `max node.horizon (time+2)` に載せることで旧履歴をすべて保ち、四成分ランクは anchor 成分で下降する。結果として early representative の残余は legal downcross 分岐だけになる。

## 主要な定義

### `EarlyLegalDowncrossResidual` (L114)

forced-candidate 分岐を除去した後の proof-relevant な残余。唯一の構成子 `legal_downcross` は、early representative 証明書に加えて

- 次の一歩が合法減算(`CanSubtract (representativeTime+1) (stateAt representativeTime)`)
- その着地が target 未満(`a (representativeTime+1) < target`)
- 代表時刻から次時刻への履歴予算の厳密下降
- ノード horizon での予算が代表時刻での予算より厳密に小さいこと(history-budget gap)

を保持する。

## 定理と証明

### `earlyForcedBelowCandidate_phaseSemanticStep` (L20)

**主張:** early representative 証明書(代表時刻 `n = representativeTime`、`target ≤ a n`、`n+1 < target`)のもとで、塞がれた減算候補 `c = a n − (n+1)` が `0 < c < target` かつ `c ∈ valuesThrough n`(既出)ならば、目標出現または「`PhaseSemanticInvariant` を満たす子とノードからのランク進捗」が成り立つ。残余はない。

**証明:** 候補が既出であることから、ある時刻 `start ≤ n` で `a start = c < target` が成り立つ。一方 `target ≤ a n` なので、区間 `[start, n]` は below-target から at-or-above-target へ至る。`exists_weakUpcrossingStep_between`(`DowncrossBudgetGap`)により、この区間のどこかに weak upcrossing、すなわち `a time < target ≤ a (time+1)` かつ時刻 `time+1` の遷移が forced addition(強制加算)である隣接対 `time` が存在する。

ここで三分岐する。まず target が `valuesThrough time` に既出なら、その出現時刻が目標出現の証人である。次に `a (time+1) = target` なら `time+1` 自身が証人である。残るのは厳密横断 `a time < target < a (time+1)` の場合で、強制加算の遷移式 `a (time+1) = a time + (time+1)` と合わせて `DebtCrossing target (a (time+1)) time` が成り立つ。

この厳密 crossing から crossing recovery(target 未満の値から強制加算で target 以上へ上向き横断した実遷移を保持する normal 状態)の子を作る。回復 horizon を `recoveryHorizon = max node.horizon (time+2)` と置き、子を `⟨recoveryHorizon, a time, normal, a time⟩` とする。`CrossingRecoveryInvariant` の各フィールドは、target 未出・forced addition・厳密 crossing・時刻 `time+1` での座標(正時刻なので存在)・`time+1 < recoveryHorizon`(max の右成分から)・`a time < a n`(pre-crossing 値は target 未満、旧代表値は target 以上)で満たされる。旧 anchor には代表値 `a n` を記録する。よって子は `PhaseSemanticInvariant` の crossing_recovery 構成子で意味的である。

ランク進捗は `phaseSearchProgress_of_horizonAndAnchor` による。horizon は `node.horizon ≤ recoveryHorizon`(max の左成分)で広義に増加し、anchor は `a time < target ≤ a n = node.anchorParent` で厳密に下降する。履歴予算が変わらなくても第二成分の anchor 下降で四成分ランクは厳密に下がる。

### `EarlyRepresentativeResidual.forcedBelowCandidate_phaseSemanticStep` (L93)

**主張:** `EarlyRepresentativeResidual.forced_below_candidate` 構成子が生成した形の仮定の組に対する、前定理の構成子形アダプタ。

**証明:** 引数を並べ替えて前定理を呼ぶだけである。

### `EarlyRepresentativeResidual.phaseSemanticStep_or_legalDowncross` (L133)

**主張:** early representative 残余は、目標出現・意味的な子とランク進捗・`EarlyLegalDowncrossResidual` のいずれかに分類される。

**証明:** 残余の二構成子で場合分けする。legal_downcross はそのデータのまま新残余型へ移す。forced_below_candidate は前定理で閉じ、目標出現または意味的な子のどちらかへ流れる。

### `EarlyRepresentativeOutcome.toPhaseSemanticStep_or_legalDowncross` (L157)

**主張:** early representative の一歩の完全分類 `EarlyRepresentativeOutcome` 全体が、同じ三択に落ちる。

**証明:** target_occurs はそのまま。forward_child(前進する extended-history 子)と debt_child(strong debt 子)はどちらも意味的な子と進捗を既に保持している。residual は前定理へ委譲する。

### `EarlyRepresentativeCertificate.phaseSemanticStep_or_legalDowncross` (L176)

**主張:** 証明書レベルの分類。任意の early representative 証明書から、目標出現・意味的な子とランク進捗・legal downcross 残余のいずれかが得られる。

**証明:** 証明書の一歩分類 `classify`(`EarlyRepresentative`)で outcome を得て、前定理を合成する。この時点で forced-candidate 分岐は分類から完全に消える。

### `earlyForcedCandidate_eight_six_actual` (L191)

**主張:** forced-candidate 分岐は空虚な場合分けではなく、実軌道に実例がある。target 8、ノード `⟨7, a 6, normal, a 6⟩`(`a 6 = 13`)について、(i) `EarlyRepresentativeResidual 8` が成立し、(ii) 子 `⟨7, a 5, normal, a 5⟩`(`a 5 = 7`)は `CrossingSearchInvariant 8` を満たし、(iii) 子はノードからのランク進捗を持つ。

**証明:** すべて Lean カーネルの `decide` で検証できる有限計算である。軌道は `0, 1, 3, 6, 2, 7, 13, 20, …` である。代表時刻 6 では `7 = 6+1 < 8 = target` なので時計未準備、`a 6 = 13 ≥ 8`、座標は `13 = 6·2+1` で `(q,r) = (2,1)`。減算候補は `13 − 7 = 6` で、`0 < 6 < 8` かつ時刻 3 に既出(`a 3 = 6`)、そして時刻 7 の減算は塞がれている(6 は既出)ので forced_below_candidate 残余が成立する。crossing recovery は `a 5 = 7 < 8 < 13 = a 6` の強制加算 `7 → 13`(ステップ 6)で、`CrossingRecoveryInvariant 8 7 13 5 2 1` の全フィールドが計算で確認される。進捗は anchor `7 < 13` の下降による。

## 全体の中での位置づけ

証明地図の「意味的探索domain」の行にある「early representative も crossing recovery へ接続して閉じる」縮約の実装であり、PROOF_MAP 本文の「early representative では次遷移または既出の減算候補から below-target 実出現を得て、future upcrossing を取り、crossing_recovery 子へ移る」という段落のうち既出候補側を担う。`EarlyRepresentative` の一歩分類を入力とし、`DowncrossBudgetGap` の weak upcrossing 存在定理を鍵に使う。残された legal downcross 分岐は `EarlyRepresentativeClosure` が同様に将来の crossing recovery で閉じ、`EarlyRepresentativeComplete`(本モジュールを import する唯一のモジュール)が両者を統合して early representative の無残余閉包を完成させる。その結果は extended-history normal の全分岐閉包 `EarlyRepresentativeComplete`・`ExtendedHistoryComplete` の行として証明地図に反映されている。
