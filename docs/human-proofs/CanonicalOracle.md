# CanonicalOracle

**役割:** canonical開始点(目標に紐づく標準的な探索開始ノード)を符号とポテンシャル水準で完全分類し、未解決部分を「ポテンシャル水準 2 以下」の帯だけに絞り込む。

## このモジュールの役割

全射性予想への攻略では、各正の目標 `m` に対して canonical開始点(canonical start)、すなわち時刻 `n = m-1` または `n = m` で `m ≤ a(n)` が成り立つ実軌道上のノード `targetStartNode n = ⟨n, a(n), normal, a(n)⟩` から探索を始める。本モジュールは、この開始点をポテンシャル `G(q,r) = r − upperTri(q)`(座標 `(q,r)` に対する符号付き整数の指標)の符号と大きさで場合分けし、負領域・目標以上の領域・水準 3 以上のアンダーシュート帯をすべて既存の定理で閉じる。閉じ残るのはポテンシャル水準が 0, 1, 2 の帯だけであり、それを `CanonicalLowLevelResidual` という証明付き残余として明示的に切り出す。以降の `CanonicalLevelZero`〜`CanonicalGrowthRecovery` がこの残余を順に解消していく。

## 主要な定義

### `CanonicalLowLevelResidual` (L126)

canonical開始点のうち、現時点の解析で閉じられない「低水準帯」を正確に表す残余命題である。構成子 `low` は次の証拠一式を保持する: 軌道時刻 `orbitTime` とその canonical 証明書(`TargetStartCertificate`)、現在時刻での座標 `CoordinatesAt orbitTime quotient remainder`、現在値 `a(orbitTime)` の初出時刻(`FirstAt`; ある値が初めて出現した時刻の証明)、`target < a(orbitTime)`、商が正であること、そしてポテンシャルがちょうど `level` に等しく `level ≤ 2` かつ `level < target` であること。つまり「なぜここで止まったか」の全データを後続モジュールが再利用できる形で残す。

## 定理と証明

### `targetStartCertificate_quotient_pos` (L17)

**主張:** canonical 証明書を持つ時刻 `n` の座標 `CoordinatesAt n q r` は必ず `q > 0` を満たす。

**証明:** `q = 0` と仮定すると座標方程式 `a(n) = n·q + r` より `a(n) = r < n` となる。一方、証明書の `near_target` から `n = target−1` または `n = target`、すなわち `n ≤ target` であり、`value_ready` から `target ≤ a(n)`。合わせると `a(n) < n ≤ target ≤ a(n)` となり矛盾する。よって `q ≥ 1` である。

### `canonicalCoverage_phaseSemantic` (L37)

**主張:** 正の目標 `target` と、canonical値 `a(n)` に対する `CoverageStep target (a n) n`(目標が出現するか、`target ≤ y < a(n)` を満たす値 `y` とその初出時刻を与える一段の被覆証明)が与えられれば、目標の出現、または位相探索ランク(4成分辞書式ランク: 履歴予算・anchor・位相・局所量)を厳密に下げる意味的 normal 子ノードのいずれかが得られる。

**証明:** `CoverageStep` の第一枝(目標出現)はそのまま結論になる。第二枝では値 `y` と初出時刻 `f` を得る。`y = target` なら初出そのものが目標の出現である。`y ≠ target` のときは子ノード `⟨max(n, f), y, normal, y⟩` を作る。horizon(履歴予算 `missingBelowCount` を評価する履歴時刻)を `max(n, f)` に広げるのは意図的である。素の `CoverageStep` インターフェースは `f ≤ n` を保証しないので、初出時刻を確実に horizon 内に収めるためである。`y` は `target ≤ y` かつ初出証明を持つので normal 証明書が成立し、horizon は `n` 以上(履歴予算は非増加)かつ anchor は `y < a(n)` と厳密に下がるので、辞書式ランクは厳密に低下する。

### `natPairLex_embed_normalValue` (L62)

**主張:** 自然数対 `(予算, 値)` の辞書式順序の下降は、値を anchor と局所座標の両方に使った normal ノードの 4 成分辞書式ランクの下降に埋め込める。

**証明:** 場合分けによる。第一成分(予算)が下がるなら 4 成分でも第一成分で下がる。第一成分が等しく第二成分(値)が下がるなら、4 成分では第二成分(anchor)で下がる。

### `historyBudgetProgress_to_phaseSemanticRank` (L77)

**主張:** 実状態間の履歴予算ステップ `HistoryBudgetProgress target ⟨a t, t⟩ ⟨a n, n⟩`(予算が下がるか、予算同値で値が下がる二成分辞書式下降)は、子が自分の値を新しい anchor に使うとき、`⟨t, a t, normal, a t⟩` から `targetStartNode n` への `PhaseSearchProgress` を与える。

**証明:** 前の補題 `natPairLex_embed_normalValue` をそのまま適用する。

### `canonicalHistoryFrontier_phaseSemantic` (L90)

**主張:** canonical ノード(`target ≤ a(n)`、`a(n)` の初出時刻 `f ≤ n`)から前向きの履歴予算ステップ `HistoryBudgetProgress target ⟨a t, t⟩ ⟨a n, n⟩`(ただし `n < t`)が得られたとき、目標の出現、またはランクを下げる意味的 normal 子ノードのいずれかが成り立つ。

**証明:** 到達先の値 `a(t)` で場合分けする。

*`target ≤ a(t)` の場合。* `a(t)` は時刻 `t` の履歴に含まれるので初出時刻を持ち、子 `⟨t, a t, normal, a t⟩` は normal 証明書を満たす。ランク下降は `historyBudgetProgress_to_phaseSemanticRank` による。

*`a(t) < target` の場合。* 軌道は `n` から `t` の間に目標水準を上から下へ横断している。下方横断の一般定理(`orbit_downcrossing_occurs_or_budgetDrop`)により、目標がその区間で実際に出現するか、さもなくば履歴予算 `missingBelowCount` が厳密に減少する。前者なら結論。後者なら、証明書付きの旧値 `a(n)` を新しい horizon `t` で再利用した子 `⟨t, a n, normal, a n⟩` を作る。`a(n)` の初出時刻は `f ≤ n < t` なので horizon 内にあり normal 証明書が立ち、ランクは第一成分(予算)で厳密に下がる。

### `targetStartInvariant_phaseSemanticStep_or_lowLevel` (L149)

**主張:** 正の目標 `target` の canonical開始ノードは、(1) 目標が出現する、(2) ランクを厳密に下げる意味的子ノードが存在する、(3) `CanonicalLowLevelResidual`(水準 2 以下の残余)に入る、のいずれかである。

**証明:** これが本モジュールの中核定理であり、開始点の完全な符号分類を行う。証明書から座標 `(q,r)` と初出時刻を取り出し、`targetStartCertificate_quotient_pos` で `q > 0` を確保する。まず `a(n) = target` なら即座に (1)。以下 `target < a(n)` として `G = potential q r` で場合分けする。

*負領域 `G < 0`。* 開始ノードは強い負normal不変量 `NormalPhaseInvariantAt`(時刻条件・値の上下界・座標・負ポテンシャルを束ねた証明書)を自分自身を anchor として満たす。証明済みの負normal局所オラクル `negativeNormal_phaseSemanticStep` により (1) または (2) が従う。

*目標以上 `G ≥ target`。* 正の商と高ポテンシャルから `CoverageStep` を与える既存定理(`positiveQuotient_potential_aboveTarget_gives_coverageStep`)が使え、`canonicalCoverage_phaseSemantic` で (1) または (2) になる。

*アンダーシュート帯 `0 ≤ G < target`。* 水準 `level = r − upperTri(q)` を定めると `G = level` かつ `level < target`。`level ≥ 3` なら非負エポックの履歴フロンティア定理 `nonnegative_epoch_historyFrontier` が三分岐を返す: 被覆(→ `canonicalCoverage_phaseSemantic`)、商 0 の例外(`q > 0` と矛盾するので起きない)、または前向き履歴予算ステップ(→ `canonicalHistoryFrontier_phaseSemantic`)。いずれも (1) または (2) に落ちる。

*残余 `level ≤ 2`。* ここまでで使ったすべての証拠(証明書、座標、初出、`target < a(n)`、`q > 0`、ポテンシャル等式、水準の上下界)をそのまま `CanonicalLowLevelResidual.low` に詰めて (3) とする。

### `canonicalLowLevelResidual_two` (L221)

**主張:** 残余は空虚な命題ではない。目標 2 の canonical開始点は時刻 2 であり、`a(2) = 3` は商 1・剰余 1、すなわちポテンシャル水準 0 で実際に残余に入る。

**証明:** `a(2) = 3` の初出が時刻 2 であることを有限検査(`decide`; Leanカーネルによる計算検証)で確かめ、証明書と座標 `(1,1)` を具体的に構成して `low` を適用する。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「canonical開始」段階の入口である。ここで確立した分類定理と補助定理(特に `canonicalCoverage_phaseSemantic` と `canonicalHistoryFrontier_phaseSemantic`)は、`CanonicalLevelZero`・`CanonicalLevelOne`・`CanonicalLevelTwo` が各水準の残余を解析する際に繰り返し使われ、`CanonicalComplete` と `CanonicalGrowthRecovery` で「canonical開始点の局所オラクルは全分岐で閉じる」という最終形(`targetStartInvariant_phaseSemanticStep`)へ統合される。
