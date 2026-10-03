# 02:00 週間最終判断候補 packet

- 対象時刻: 2026-09-24 02:00枠 JST
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- 性格: 既存証拠の分類と停止・再開案。新数学、新計算、Lean、登録、昇格ではない。
- 手続判定: **独立Sol監査前の草稿**。本packet自身を合格根拠にしない。

## 一問・合格条件・停止条件

一問: この週間計画内に残る未監査の計算、紙上/Lean候補、手続き欠落、数学的依存義務を、
確立済み・反証済みの範囲と混ぜず一覧化し、今週の探索を延長しない判断と、将来再開時の最小の一問を
正当化できるか。

合格条件:

1. 各項目を `PROVED-LEAN` / `REFUTED` / `STOPPED` / 有限計算 / 手続き未完了 / 数学的未解決に分ける。
2. H-04の限定反例を最小lag15や一般lagへ広げず、時間外未着手を数学的停止にしない。
3. 使用済み標本、読取だけのログ、対象0件、未保存source、有限周期語を証明として扱わない。
4. 再開質問は一般全域性でなく、既存E-359/E-360の直後にある一つの有限な境界へ絞る。
5. 別Solが根拠、漏れ、停止範囲、再開質問を合格とし、親が対象hashと原文を照合する。

停止条件: 期限内に由来または意味を独立確認できない項目は**未完了**として残す。新census、範囲延長、
反例の修理、研究Lean、一般lagルートへの新しい `STOPPED` label、登録・昇格を行わない。

## 既に確立・反証済みで、未監査一覧へ混ぜないもの

| 対象 | 正確な現状 | 越えてはいけない境界 |
|---|---|---|
| E-360 Q | `PROVED-LEAN`: 任意の正周期、最小P2 lag 3/7/11のtight B、最小lag11・SS2 donorのtrue-oldest回避 | lag15以上、一般Gate T6、実軌道ではない |
| E-360 W | `PROVED-LEAN`: 4-field `OwnerFamily` 条件付きの `w1_owns_oldest` / `w1_next_addition` | 無条件の周期定理ではない。E-351のnext-A仮定を逆用しない |
| short-supply deletion | `PROVED-LEAN`: Uの全要素が最小P2 lag 3/7/11である場合の直接系 | 完全all-lag Uからの削除ではない |
| H-04 p16 literal | 非最小lag15 donorへの延長だけ `REFUTED`、同じ延長ルートだけ `STOPPED` | 最小lag15、任意lag、一般Gate T6、実軌道の反例ではない |
| E-240 / E-069 / E-345 | 純AAS強制 / oldest-S単射 / SS>=3 true-oldest削除の既知反例 | E-360の限定Qを反証しない |
| 9/22 | 許可時間外のため未着手 | 数学的 `STOPPED` や失敗ではない |

既存の失敗枝も別に固定する。9/20 01:30の壊れた反証ゲート実装枝は、一回の修理後も重複period行・
負値相殺payloadを受理したため追加修理を停止した。9/20 02:00のproper-U probeはw1前件0件で未完了、
第2修理・範囲拡大を禁止した。後日得たp20の別のproper-U非空例を、旧probeの成功や実行済み反証へ
遡及変換しない。いずれもQ/Wや一般lag数学ルート全体の`STOPPED`ではない。

## 未監査・未完了一覧

### A. 計算と標本

| 項目 | 現在の証拠 | 未完了の理由 | 今週の扱い |
|---|---|---|---|
| p32/33各2000語、seed `2026091801` | 使用済み有限標本。p32 donor-bearing 147/Q 1347/W 326、p33 164/1598/341、違反0 | 同作者の別実装照合はあるが標本全体の独立認証は未完了 | E-360の証明理由にしない。再実行・再holdout化しない |
| matching-closure lag19 4 shard | 各末尾 `excluded 409/409, consistent 0, cap hit 0` を読んだ `OBSERVED` | revision、4分割の完全性・重複、生成条件、全原出力の独立監査がない。E-356行にはなお「実行中」の履歴文がある | 一般lagや無条件Tの根拠にしない。今週は監査も再計算もしない |
| H-04旧census | 32768語、P2/SS2 85、minimal 46、第二w1例という旧記録 | 9/23監査はp16一literalだけ。census、第二例、最小p/lagは対象外 | p16 literalを越える主張に使わない |
| H-05 donor census | 長さ11/15/19と、23/27/31のminimal SS2語647/1673/3605、compatible motif 0という旧記録 | 9/23監査は局所3宣言だけ。donor censusとAAS/w1全配置は未監査 | 任意長donor回避の証拠にしない |
| H-02 fixed shortOff collision | fixed selectorとdonor oldestの衝突3件という `OBSERVED` | inline exploratory実行で、selectorと3件の独立再計算が未完了 | そのshortcutの確定反証や一般不可能性に昇格しない |
| H-03 strict/full-P2/tight領域 | 指定済みp1..12,p15で該当0を独立再現 | 有限0件はglobal不存在でなく、正のstrict例もない | `CONJECTURED`維持。上限延長しない |

### B. Lean・紙上候補

| 対象 | 監査済みの限定部分 | 未監査・未完成部分 | 状態 |
|---|---|---|---|
| H-02 | `short_tight_avoids_ss2_window` の逐語statementと限定意味 | 形式化前独立入口、公式登録手続。任意donor長、lag15以上、all-lag Uへの拡張 | `CONJECTURED`、総合未完了 |
| H-03 | `tight_neighborhood_eq_of_p2_prefix` の広いLean文と元cardからの適用方向 | 元card strict領域の実現可能性・新規性。H-02依存の回避/削除2宣言 | `CONJECTURED`、総合未完了 |
| H-05 | `moment_ending_A_budget`、`moment_ending_AA_ss2`、`ss2_intervening_prefix` と紙§1-2 | `ss2_aas_oldest_has_prefix`、`ss2_no_w1_oldest`、oldest分解/cover宣言、紙§3-5、OwnerFamily・周期への接続、最終donor回避/削除定理 | `CONJECTURED`、総合未完了。全体を表す最終定理なし |
| `SS2OldestPattern` 統合 | root import、direct build、限定3宣言の明示的axiom確認 | Auditへの対象3宣言の直記、公式G5/registry、新規性判断 | build成功を登録・昇格としない |

### C. 修復不能な手続き履歴と、将来の必須手続き

- H-02/H-03/H-05は昼の形式化前に独立入口検査がなかった。後日の意味監査で遡及修復しない。
- H-02の失敗checker 2版は実行時source/hash欠落、H-05初回補助checker/Lean診断はprehash欠落。
  後日の再構成・byte一致再生は履歴を消さない。
- E-360昼工程にも入口検査・初回checker保存の歴史的欠落があるが、後続の正式な独立監査と登録は
  E-360の限定3 symbolに対して完了している。これをH-02/H-03/H-05へ流用しない。
- H-03/H-05の未監査宣言を将来扱う場合、対象を新カードで凍結し、形式化前入口、非空例、負対照、
  逐語statement、source hash、原stdout/stderrを初回実行前から保存する。

### D. 数学的依存義務

1. **lag15境界**: E-359/E-360はBの全窓をlag 3/7/11に制限する。最小lag15 memberを持つtight Bを
   除外する、または具体例を与える監査済み結果がない。H-04は非最小donorの反例で別問題。
2. **一般lag**: lag15の一段を越えても、任意offsetのowner配置を扱う一様な制約または帰納が必要。
   lag19 shardの有限排除を一般lagへ外挿できない。
3. **一般Gate T6のdonor包含枝**: 回避BのG2だけでは不足。donorを含む部分集合の削除後Hall保存は
   現在p<=11側の容量補償に依存し、一般pへの橋がない。
4. **完全all-lag Uと容量**: short-only UのHall/削除系を完全供給Uへ拡大する根拠がない。
   E-070/E-067は`CONJECTURED`。
5. **任意長donor**: H-05の局所語補題からAAS/w1全配置排除、true-oldest、周期OwnerFamilyへ接続する
   監査済み依存鎖と最終定理がない。
6. **実軌道**: 周期符号語の局所定理からRecaman実軌道、有限周期から無限、Gate T6から全域性への橋はない。

## 今週の停止判断

**週間計画は9/24の予約内で終了し、探索を延長しないことを推奨する。** 理由は、計画の成功条件である
限定新補題E-360と、非最小lag15延長の限定反例を既に得た一方、残りは上記の未監査候補・履歴欠落・
独立した数学的橋であり、短時間の範囲延長や既存census再実行では解消しないからである。

これは時間・運用上の終了であり、一般lagルート全体を数学的に `STOPPED` と新規判定するものではない。
数学的 `STOPPED` は、H-04の非最小lag15延長、9/20の壊れた反証ゲート実装枝、対象0のproper-U probe等、
既に個別に限定された枝だけに保つ。proper-U probe自体の数学的結果は未完了で、止めたのは第2修理・
即時範囲拡大である。p20別例を旧probeの成功にしない。H-02/H-03/H-05と一般lagは未解決/未完了である。

## 再開に必要な最小の一問

次の計画で最初に問うべき一問は、一般lag全体でも全射性でもなく、次のlag15境界である。

> 任意の正周期符号語で、nodup U上のHall、`B.Sublist U`、Bの緊密性、B各要素の範囲内current-A、
> 最小P2、`lag in {3,7,11,15}` を仮定したとき、Bはlag15 memberを持ち得ないか。

合格は、全量化子を固定した命題に対する非空の前提例を伴う紙上/Lean証明、または全前提を満たす周期反例。
入口で別SolがE-240/E-069、H-04非最小donor、位相同一視、任意offset、OwnerFamily実現を攻撃する。
旧10,026-node証明書の再実行・単なるビットマスク最適化・lag上限延長は合格にしない。

この一問が最小なのは、E-359の `{3,7,11}` 境界の直後を一段だけ動かし、H-04の非最小donor反例と
最小member問題を混同せず、真なら一般lagへの帰納に必要な形を具体化し、偽なら最小の新しい周期反例で
ルートを早く棄却できるからである。これに答えても一般Gate T6、all-lag容量、実軌道は別義務として残る。

## 監査待ち

本packet、週報追記、主カード追記、handoff追記の全候補は別Solの合格前には草稿である。
親の照合・適用前に文言、状態、停止範囲を確定しない。
