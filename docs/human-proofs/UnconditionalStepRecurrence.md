# UnconditionalStepRecurrence

**役割:** 敵対的監査が検出した2つの「無料の結論」を誠実な名前で記録し、回廊ブロック則を真に回廊由来の時計条件付きで復元する。

## このモジュールの役割

2026-09-01スプリントの敵対的監査は、回廊仮定つきで述べられていた2つの結論が実は無条件に
成立することを発見した。本モジュールはそれらを回廊なしの定理として記録し、あわせて
「回廊がforced additionに本当に加える内容」——時計条件の成立、すなわちブロックが純粋に
履歴由来であること——を復元する。副産物として、canonical軌道の**両ステップ種**
（合法減算は`exists_canSubtract_of_ray`、forced additionは本モジュール）が無条件に
無限再発することが揃った。

## 定理と証明

### `forcedAddition_candidate_historical` (L28)

**主張:** 任意のforced additionの減算候補は履歴内の値である（回廊仮定なし）。

**証明:** `CanSubtract`の不成立は時計条件の失敗か既訪問による。時計条件が失敗するときは
候補は自然数の切り詰めで `0 = a(0)` になり、これは常に履歴に入っている。

### `exists_forcedAddition_of_ray` (L43)

**主張:** forced additionは任意の限界の先で再発する（回廊仮定なし）。

**証明:** 時刻M以降ずっと合法減算だとすると、各減算は値を1以上下げる一方、`CanSubtract`の
時計条件が値を正に保つ。`a(M) + 1`ステップ後には値が負になるはずで矛盾。

### `corridor_forcedAddition_clock_and_seen` (L74)

**主張:** 回廊の真に内側でのforced additionでは、時計条件 `n + 1 < a(n)` が成立し、
候補は正で、かつ既訪問である。つまりブロックは時計不足からではなく履歴から来る。

**証明:** 回廊の高候補則により候補は正（したがって時計条件成立）、既訪問性は前定理。

## 全体の中での位置づけ

「生成証明書を保持しない忘却形は必ず捏造される」というプロジェクトの監査教訓の実践である。
`EventualHighCorridorSupply` の `corridor_infinitely_many_forcedAdditions` と
`EventualHighCorridorStructure` の `corridor_forcedAddition_candidate_seen` は結論が無料である
ことをdocコメントに明記した上で保存されている（`SharpCorridor` interfaceの互換用）。
回廊固有の内容は `candidate_high`・`value_law`・`fresh_landings`・供給窓のvalue law連言に限られる。
