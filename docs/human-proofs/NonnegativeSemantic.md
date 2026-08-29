# NonnegativeSemantic

**役割:** 非負ポテンシャル帯の履歴フロンティアを意味的探索 domain の言葉に翻訳し、水準 3 以上を完全に閉じて、残余を水準 0・1・2 の帯 `NonnegativeLowLevelResidualAt` に限定する。

## このモジュールの役割

非負エポック(`0 ≤ potential < target` の帯を追跡する有限区間)の既存定理群は、「生の」履歴探索ランクの下降を返すが、そのままでは意味的探索 domain(証明を運ぶ normal ノードの集合)への所属や 4 成分位相ランクの下降にならない。本モジュールはこの翻訳を行う。鍵となるのは再anchor定理 `normalProgress_reanchorAtValue` であり、旧 anchor のままのランク下降を、子自身の値を新 anchor とするランク下降に変換する。これにより水準 `g ≥ 3` の非負帯は、目標出現または意味的ランク子へ完全に閉じ、商 0 の例外も「目標以上の値」という前提と矛盾するため消える。残るのは文字どおり三水準の帯 `g = 0, 1, 2` だけであり、これは `CanonicalLevelZero/One/Two` の canonical 解析、および将来の一般 orbit-ready 解析が引き受ける。

## 主要な定義

### `NonnegativeLowLevelResidualAt` (L176)

一般の orbit-ready normal ノード(local 値が実際に `a(n)` で、時刻・値・座標条件を証明付きで持つノード)に対して、現在の非負エポック API が閉じ残す正確な境界を表す構造体である。`target ≤ n + 1`(時刻準備)、`target ≤ a(n) ≤ activeParent`(値と anchor の挟み込み)、座標 `CoordinatesAt n q r`、`q > 0`、`potential q r = level`、`level ≤ 2`、`level < target` を保持する。商 0 は不在である: `target ≤ a(n)` と「水準が目標未満」は商 0 と両立しない。

## 定理と証明

### 補助補題 (L6, L16, L29, L41)

4 成分・3 成分・2 成分の辞書式順序に関する private 分解補題である。`nonnegativeSemantic_natQuadLex_fst_le` (L6) は辞書式下降の第一成分が非増加であること、`nonnegativeSemantic_natQuadLex_tail` (L16)・`nonnegativeSemantic_natTripleLex_tail` (L29)・`nonnegativeSemantic_natPairLex_tail` (L41) は第一成分が等しいときに下降が残り成分へ落ちることを言う。

### `normalProgress_reanchorAtValue` (L57)

**主張:** normal のランク step が旧 anchor を保ったまま成立しているとき(子 `⟨childTime, parentAnchor, normal, childValue⟩`、親 `⟨parentTime, parentAnchor, normal, parentValue⟩`、ただし `parentValue ≤ parentAnchor`)、子を自身の値で再anchorした `⟨childTime, childValue, normal, childValue⟩` も親に対するランク step になる。

**証明:** `childValue` と `parentAnchor` の大小で場合分けする。

*`childValue < parentAnchor` の場合。* 同一時刻で anchor を `parentAnchor` から `childValue` へ落とす step が作れる(horizon 不変・anchor 厳密下降)。これと仮定の step を推移律でつなげばよい。

*`parentAnchor ≤ childValue` の場合。* 仮定のランク下降を 4 成分辞書式で読む。第一成分(履歴予算)は非増加である(L6)。もし予算が等しいなら、下降は第二成分以降へ落ちるが、anchor(第二成分)と位相(第三成分)は両辺で等しいので、最終的に局所量の比較 `childValue < parentValue` に帰着する(L16, L29, L41)。ところが `parentValue ≤ parentAnchor ≤ childValue` なのでこれは矛盾である。よって予算は厳密に下がっており、再anchor後の子も第一成分だけでランクが下がる。直観的には、「anchor を大きく付け替えられるのは、履歴予算がすでに厳密に減っているときだけ」ということである。

### `nonnegative_epoch_phaseSemanticOutcome` (L105)

**主張:** 通常水準の非負帯の意味的版である。`target ≤ n + 1`、`target ≤ a(n) ≤ activeParent`、座標 `(q,r)`、`potential q r = g`、`3 ≤ g < target` のとき、目標の出現、または親 `⟨n, activeParent, normal, a(n)⟩` に対してランクを厳密に下げる意味的 normal 子が存在する。

**証明:** 生の履歴探索定理 `nonnegative_epoch_historySearchOutcome` は四つの結果を返す。それぞれを意味的に再構成する。

*目標出現。* そのまま結論。

*親下降(parent descent)。* `target ≤ y < a(n) ≤ activeParent` を満たす値 `y` と初出時刻 `fy` を得る。子 `⟨max(n, fy), y, normal, y⟩` は初出を horizon 内に持つ normal ノードであり、horizon 前進と anchor 厳密下降でランクが下がる。

*商 0 の例外。* `q = 0` なら座標方程式から `a(n) = r`、ポテンシャルから `r = g` である。すると `a(n) = g < target ≤ a(n)` となり矛盾。この枝は起きない。ここが本モジュールの表題的な観察である: 意味的 normal 開始は `target ≤ a(n)` を持つので、旧 API の商 0 境界は自動的に消える。

*前向き軌道 step。* 時刻 `t > n` への生のランク下降(anchor は旧値 `activeParent` のまま)を得る。`a(t)` の位置で分岐する。
  - `target ≤ a(t)` のとき、`normalProgress_reanchorAtValue` により子を `⟨t, a(t), normal, a(t)⟩` に再anchorしてもランク下降が保たれ、履歴からの初出で normal 証明書も立つ。
  - `a(t) < target` のとき、軌道は目標水準を下方横断している。横断定理 `orbit_downcrossing_occurs_or_budgetDrop` により、目標が出現するか履歴予算が厳密に減る。後者では証明書付きの旧値 `a(n)` を新 horizon `t` に載せた子 `⟨t, a(n), normal, a(n)⟩` がランク第一成分で下がる。

### `nonnegative_epoch_phaseSemanticStep_or_lowLevel` (L191)

**主張:** 目標未満の非負ポテンシャルの完全な意味的分類である。前提は L105 と同じ形(ただし水準の下限なし、`0 ≤ potential q r < target`)で、結論は (1) 目標の出現、(2) 意味的ランク子、(3) ある `level` について `NonnegativeLowLevelResidualAt target activeParent n q r level`、の三択である。

**証明:** まず `q > 0` を示す: `q = 0` なら `a(n) = r` かつ `potential 0 r = r < target` だが、`target ≤ a(n) = r` と矛盾する。次に水準 `level = r − upperTri(q)` を定めると、非負性から `potential q r = level` かつ `level < target` である。`level ≥ 3` なら `nonnegative_epoch_phaseSemanticOutcome` により (1) または (2)。`level ≤ 2` なら、前提をそのまま構造体に詰めて (3) とする。

## 全体の中での位置づけ

証明地図の「非負normal — 通常域閉包済み」に対応する。`3 ≤ potential < target` を意味的ランクへ接続し、残余を水準 0・1・2 に限定するのが本モジュールの成果である。再anchor定理 `normalProgress_reanchorAtValue` は `CanonicalLevelOne` の強制加算解析(商 2 以上の枝)でも直接使われる。また `nonnegative_epoch_phaseSemanticOutcome` は、orbit-ready normal ノードの局所 totality(`OrbitReadyComplete` 系)における非負アンダーシュート枝の基盤であり、canonical 系列が水準 0・1・2 を個別に閉じたのと同じ構図を、一般の anchor `activeParent` を許す形で提供する。
