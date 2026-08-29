# PhaseEpoch

**役割:** 負エポックの結果を四成分位相ランクへ接続し、対角仮定なしで「目標出現または位相ランクの厳密下降」を得る。

## このモジュールの役割

`HistoryFrontier` の負エポック定理は、商 1 の負債チャンバー(対角状態 `a t = t` に帰着する例外分岐)を残しており、それを消すには `DiagonalSuccessorProperty` という未証明の仮定が必要だった。一方 `PhaseSearch` は、対角状態から debt 位相への進入を無条件のランク下降として登録できるようにした。本モジュールは両者を接続する。まず三成分の履歴探索ステップを normal 位相固定で四成分ランクへ埋め込む一般補題を示し、次に負債チャンバーを `Diagonal` の二分法経由で debt 進入へ変換する。その結果、**仮定なしで**「負エポックは目標を出現させるか、位相ランクを厳密に下げる」という定理(`negative_epoch_phaseSearchOutcome`)が得られる。証明地図の「負エポック位相接続」(ランク証明済み)に対応する。

## 定理と証明

### `natTripleLex_embed_normalPhase` (L7)

**主張:** 位相成分を `normal.rank` に固定して挿入すると、三成分の辞書式減少 `(予算, 親, 軌道値)` は四成分の辞書式減少 `(予算, 親, 位相, 局所量)` に埋め込まれる。

**証明:** 分岐ごとの対応。予算の下降は予算の下降へ、親の下降は親の下降へ、軌道値の下降は「位相不変・局所量下降」へ写る。位相成分が固定値なので新たな比較は発生しない。

### `HistorySearchProgress.toNormalPhaseSearchProgress` (L30)

**主張:** すべての三成分履歴探索ステップは、両ノードを normal 位相に載せた四成分位相探索ステップになる。

**証明:** 前補題を `historySearchRank` と `phaseSearchRank` の対応に沿って適用するだけである。これにより `HistoryFrontier` で証明済みの豊富な進捗定理群が、書き換えなしで位相探索の語彙に持ち上がる。

### `qOneDebt_target_or_phaseSearchProgress` (L42)

**主張:** 負エポックの終端に残る商 1 の負債チャンバー(時刻 `t` で座標 `(1, r)`、一段借り `BorrowData t 1 r 1 s`、着地レベルが `0 ≤ potential 1 s < m`)は、目標を出現させるか、blocker `y`(`m ≤ y`、初出時刻 `fy < t`)とともに normal ノードから debt ノード `⟨t, activeParent, debt, fy⟩` への厳密な四成分ランク下降を与える。これはランクレベルの統合定理であり、子は早期 blocker のデータを明示的に運ぶが、追加の意味的 debt 不変量は仮定しない。

**証明:** `HistoryFrontier` の `qOneDebt_target_or_diagonalSuccessor` により、チャンバーの算術は `m = t`(既に `a t = t = m` として出現)か、`n = t` かつ `m = t+1` かつ `a t = t` の対角ケースに固定される。後者で `t` の大きさによる場合分けを行う。`t = 1` なら後継 `2` は `a 4 = 2` として出現する(`decide`)。`t ≥ 2` なら `t = k+2` と書き、`PhaseSearch` の `diagonal_successor_or_entersPhaseDebt` を適用する: 後継値 `k+3 = m` が出現するか、`m ≤ y`・`fy < t` の blocker とともに debt 進入のランク下降が得られる。

### `negative_epoch_phaseSearchOutcome` (L84)

**主張:** 完全な負エポックは、ランクレベルではもはや `DiagonalSuccessorProperty` を必要としない。`0 < m`、`m ≤ n+1`、`a n ≤ activeParent`、時刻 `n` の座標のポテンシャルが負であるとき、目標が出現するか、normal ノード `⟨n, activeParent, normal, a n⟩` より位相ランクで真に小さい子ノードが存在する。

**証明:** `HistoryFrontier` の `negative_epoch_historySearchOutcome_or_qOneDebt` の四分岐をそれぞれ変換する。

1. 目標の出現: そのまま。
2. blocker による親下降(三成分): `toNormalPhaseSearchProgress` で normal 位相の子 `⟨horizon, y, normal, a horizon⟩` へ。
3. 軌道値下降(三成分): 同じく normal 位相の子 `⟨u, activeParent, normal, a u⟩` へ。
4. 商 1 負債チャンバー: `qOneDebt_target_or_phaseSearchProgress` により、出現するか debt 位相の子 `⟨t, activeParent, debt, fy⟩` へ。

いずれの枝も「出現」か「厳密なランク下降を持つ子の存在」に帰着するので、結論の二分法が得られる。

## 全体の中での位置づけ

証明地図の「対角負債分岐」「極大後方鎖・早期blocker」から「四成分位相ランク」への接続点であり、状況一覧「負エポック位相接続」行(ランク証明済み)そのものである。`HistoryFrontier`(負エポックの三成分解析)、`Diagonal`(早期 blocker)、`PhaseSearch`(debt 進入規則)の三つを合流させ、負領域の解析を仮定なしの位相ランク下降として完成させた。ここで生まれた debt 子ノードの意味的内容(blocker の値・初出時刻・履歴条件)を証明書として保持し追跡するのが `DebtInvariant` 以降の負債局所解析であり、normal 子ノードの意味的内容を保持するのが `PhaseSemantic` の役割である。埋め込み補題 `toNormalPhaseSearchProgress` は `NormalPhase` などの後続統合でも繰り返し使われる。
