# PhaseProgress

**役割:** 四成分位相ランクの推移性を証明し、複数ステップの局所機構をひとつのランク下降として合成可能にする。

## このモジュールの役割

局所定理はしばしば「中間の意味的ノードを経由して二段でランクを下げる」形をとる。たとえば負エポックの前置区間で軌道値が下がり、その後の境界処理でさらに下がる、という合成である。これをひとつの `PhaseSearchProgress` として大域探索へ渡すには、ランク順序の推移性が要る。本モジュールは四成分辞書式順序の推移性と、それを引き戻した `PhaseSearchProgress` の推移性のみを提供する小さな補助モジュールである。

## 定理と証明

### `natQuadLex_trans` (L7)

**主張:** 位相探索が使う右入れ子の四成分辞書式順序 `Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))` は推移的である。

**証明:** 最外成分について左分岐(第一成分の厳密下降)か右分岐(第一成分不変・残りが下降)かで 4 通りに場合分けする。どちらかが左分岐なら合成も左分岐(必要なら `<` の推移性を使う)。両方とも右分岐なら第一成分は共通で、内側の三成分順序の推移性 `natTripleLex_trans`(`HistoryBudget` で証明済み)に帰着する。

### `PhaseSearchProgress.trans` (L32)

**主張:** `PhaseSearchProgress m` は推移的である。すなわち `x` が `y` より小さく `y` が `z` より小さければ、`x` は `z` より小さい。

**証明:** `PhaseSearchProgress` はランク写像 `phaseSearchRank` による四成分順序の引き戻しなので、`natQuadLex_trans` をランク値に適用するだけである。これにより局所機構は、中間の意味的ノードを露出しても大域のランク下降を失わない。

## 全体の中での位置づけ

証明地図の「四成分位相ランク」段階を支える技術的補助である。`HistoryBudget` の `HistoryBudgetProgress.trans` / `HistorySearchProgress.trans` の四成分版にあたる。`NormalPhase` や各エポック統合定理、`Crossing*` 系の多段遷移(強制加算とその返済、crossing 後の回復など)が二つ以上のランク下降を合成する際に、この推移性が暗黙の基盤として使われる。
