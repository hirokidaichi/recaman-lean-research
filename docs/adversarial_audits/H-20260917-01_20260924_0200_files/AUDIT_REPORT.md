# H-20260917-01 週間最終判断 独立敵対監査

## 結論

**最終凍結候補は合格。** 合格範囲は、週間内の未監査計算・紙上/Lean候補・手続き欠落・
依存義務の一覧と、今週の探索を延長しない運用判断、および再開条件が現時点で未充足だという判断に限る。
新しい数学、証拠ラベル変更、登録、昇格、一般lagルートの数学的 `STOPPED` は承認しない。

週間終了は日程・portfolio上の判断として妥当である。数学的 `REFUTED` / `STOPPED` は
H-20260920-04 の**非最小lag15 donorへの延長**と同じ限定ルートだけに保つ。
H-02/H-03/H-05、最小lag15、一般lag、完全all-lag U、一般Gate T6、実軌道は
`CONJECTURED` または未解決/未完了のままである。

## 対象版

- 監査開始: 2026-09-24 02:03:58 JST。最終候補凍結確認: 02:14 JST。
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`。既存dirty working treeを保持。
- `Recaman/ShortTightDonorAvoidance.lean`:
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`。
- `Recaman/SS2OldestPattern.lean`:
  `a9540f5f891198ec91eefd73f62f9e35d4e59f645936dc3a349504e529b325de`。
- 最終 `candidate_packet.md`:
  `e68be6a79dfa42ff4069357bfbe0899c0333636dd216f39bbc04bac05a42ce34`。
- 最終週間追記 / full:
  `45df01cff6716e4466cb8e6206ac8e998801f30758b0de55c9b5667db3b10839` /
  `00b149ea96eafdddcbfbe4a4e09031ca0779ab1ffdfd93fa941d02bb57dfd9d2`。
- 最終主カード追記 / full:
  `0dd3b60083a64395184c2de130189c4e58ca09f5474a452af283a55085d1adf0` /
  `7f73cc1ec105e699b571e5f0df78d5ddcef670dc304f44a9d5df9efee078b479`。
- 最終handoff追記:
  `6f1be22eacc70b30871035d737f9c49f97c06e2967e75240c0788ae9f977301d`。
- writer commands / review status:
  `eb5393a38c2e9aac96bd9f9a76388beadcc354a8e90f4bdf7c7e700cdd107634` /
  `633570a93c392c09f58635fcca750fc2334df558b5a66171512190a97694a313`。

最終候補のbyteコピーは `source/writer_final/`、開始時対象は `source/snapshots/`、
writerの原文3件は `source/writer_originals/` に保存した。週間fullと主カードfullはそれぞれ
開始時原文 + LF 1 byte + 最終追記に完全一致した（`raw/byte_compare_final.*`, exit 0）。

## 一問・合格条件・停止条件

一問は、確立済みの限定範囲と混ぜずに週間内の全未監査項目を分類し、探索非延長と将来の再開gateを
正当化できるか。合格条件は、各候補の正確な命題・証拠水準・手続き履歴・依存を区別し、有限計算を
無限定理にせず、限定反例/停止を一般化せず、未固定の再開案を承認済み新数学にしないこと。
停止条件は02:21までに新探索・新Leanを開始せず、再現不能/高価/由来不明を未完了として残すこと。

## 全候補の判定

| 対象 | 操作上の最終判定 | 正確な境界 |
|---|---|---|
| H-20260917-01 / E-360 Q | `PROVED-LEAN`維持 | 任意p>0、nodup tight B、全memberが最小P2 lag 3/7/11、donorが最小lag11・SS2、true-oldest非被覆。一般lag/T6/実軌道ではない |
| E-360 W 2宣言 | `PROVED-LEAN`維持 | `OwnerFamily` の `window/addA/own_mem/onto` を全て仮定する条件付き局所結論。周期側ではE-358/E-359からfamilyを構成する |
| H-20260921-01 deletion | `PROVED-LEAN`維持 | Uの全memberが最小P2 lag 3/7/11であるall-short系。完全all-lag Uではない。Q + short Hall +既存削除補題の直接系 |
| H-20260920-02 | `CONJECTURED`、総合未完了 | 固定donor長11でdonor最小性/current-Aを外す限定statementだけ意味監査済み。一般donor長/lag15/all-lag Uではない |
| H-20260920-03 | `CONJECTURED`、総合未完了 | `tight_neighborhood_eq_of_p2_prefix` の意味だけ限定合格。元strict/full-P2/tight領域は正例0、downstream 2宣言は未監査かつH-02依存 |
| H-20260920-04 | 非最小lag15だけ `REFUTED`、同ルートだけ `STOPPED` | p16 `SAAASSSASASASAAA`, u0=15, B=[3], proper P2 prefix3, true-oldest offset15/phase0, N=[0], 削除後1<=0偽。最小lag15/一般lag/T6/実軌道は未反証 |
| H-20260920-05 | `CONJECTURED`、総合未完了 | 紙§1-2に対応する局所3宣言だけ限定意味合格。紙§3-5、後続10宣言、周期接続、最終定理は未監査 |
| 9/20壊れた反証gate | 実装枝の追加修理停止 | 重複period行・負値相殺payload受理。Q/Wや一般lagの数学的 `STOPPED` ではない |
| 9/20 proper-U probe | 数学的結果は未完了 | w1前件0件。第2修理・即時範囲拡大だけ停止。後日p20別例で遡及成功にしない |
| 9/22 | 許可時間外の未着手 | 反証・失敗・数学的停止に数えない |

E-240のregistry labelは `PROVED-LEAN` であり、そのperiod18証明書が純AAS/lag3強制を反証する。
E-069は `REFUTED`、E-345はSS>=3対照を含む `COMPUTED`。ラベルと「経路を反証する証拠」を
混同しない。E-351はnext-A等を既に仮定するので、Wのnext-Aへ逆用しない。

## 未監査・未完了一覧

### 計算

1. p32/p33、seed `2026091801`、各2000 accepted wordsは使用済み有限標本。
   donor-bearing 147/164、Q_nonempty 1347/1598、W 326/341、違反0。同作者の別アルゴリズム照合はあるが、
   全標本の独立認証は未完了。新holdoutやE-360の証明理由にしない。
2. lag-max19の4 shardは各末尾 `excluded 409/409, consistent closure 0, cap hit 0` を読んだだけ。
   revision、分割の完全性/非重複、generator条件、全raw来歴は未監査。一般lagの排除ではない。
3. H-04旧censusの32768語 / P2-SS2 85 / minimal 46、第二w1例、最小p/lagは未監査。
   認証済みなのは上記p16 literalだけ。
4. H-05の11/15/19 discoveryと23/27/31 holdout（minimal 647/1673/3605、compatible motif 0）は
   有限・未監査。任意長donor定理にしない。
5. H-02 fixed shortOff衝突3件は同sessionの `OBSERVED`。selectorと3件の独立再計算がなく、
   shortcutの確定反証や一般不可能性へ上げない。
6. H-03 strict/full-P2/tight領域は指定済みp1..12,p15で該当0。有限0件をglobal不存在にしない。
7. 9/20初回 `python3 -u experiments/issue73_20260920/baseline_q_w.py 15` は
   exclusive-bound bugを含むまま60秒SIGINT、exit130、stdout空。後のinclusive p1..11成功は別実行で、
   初回失敗、p15成功、有限分類を遡及修復しない。

### 紙・Lean

`SS2OldestPattern.lean` の theorem 宣言は13本で、限定意味監査済みは次の3本だけである。

- `moment_ending_A_budget`
- `moment_ending_AA_ss2`
- `ss2_intervening_prefix`

残る未監査10本は次である。

- `moment_replicate_A_nonneg`
- `p2_append_A_tail_data`
- `ss2_aas_oldest_has_prefix`
- `ss2_no_w1_oldest`
- `oldestOffset_le_length`
- `oldestOffset_split`
- `ssCount_append_replicate_A`
- `past_oldest_split`
- `oldest_cover_clock_lt`
- `past_oldest_cover_decomposition`

したがって旧草稿の「残り7」は過少で、最終候補の10本列挙へ訂正された。lint 13/13は存在・形の
heuristicであり、この10本の意味監査ではない。H-05には全体を表す最終定理、公式G5、
`Recaman/Audit.lean` の対象3本直記がない。

H-03の未監査downstreamは `short_p2_tight_avoids_ss2_window` と `short_p2_ss2_deletion`。
前者/後者がLeanで存在しても、H-02総合未完了と元strict領域の非空性欠如を埋めない。

### 手続き履歴

- H-02/H-03/H-05は形式化前独立入口検査なし。後日の限定意味監査で遡及修復しない。
- H-02の初回失敗checker 2版は実行時source/hash欠落。H-05の初回補助checker/Lean診断はprehash欠落。
- 9/21初回checker source/rawも訂正前に保存されていない。後日再構成・byte一致再生は新しい再現性確認で、
  初回来歴にはならない。
- E-360昼工程にも入口/初回保存の歴史的欠落がある。ただし凍結同版に対する後続正式監査・G5・登録は
  限定3 symbolについて完了済み。この合格をH-02/H-03/H-05へ流用しない。

## 敵対攻撃と依存義務

- `OwnerFamily` は結論を隠した無条件定義ではなく4 fieldを持つ仮定構造。W単独を周期性だけの定理としない。
  `onto`除去の弱化例が壊れる。周期適用では具体的constructorを省かない。
- 登録E-360の3 symbolは同source hashの先行監査で、結論仮定化、矛盾前提、H→H、x=x、自由算術だけ、
  wrapper、新規性誇張を攻撃済み。constructor/refactorを新数学に数えない。
- E-351の既仮定、偽offset11、true-oldest offset、Nat phase aliasを混同しない。p16はoffset15/phase0で、
  offset11/phase4は別物。
- short-only Uと完全all-lag U、G2と一般Gate T6、任意pと有限p上限、周期語と実軌道、有限計算と
  無限定理を接続しない。
- lag15の一段を越えても、任意owner offsetを扱う一様構造または帰納が別途必要。
- donor包含subsetの一般p削除後Hallには既存p<=11容量補償の壁が残る。
- H-05にはword-to-stream分解、全AAS/w1配置、true-oldest座標、周期OwnerFamily liftが残る。

## 停止・再開判断

今週は延長しない。理由は、計画上の限定成果E-360と限定反例H-04を保存できた一方、残りが
短い範囲延長や旧census再実行では解消しない独立の未監査候補・履歴欠落・数学的橋だからである。
この判断で一般lagルートを新規 `STOPPED` にしない。

lag15 member排除はE-356の有限lag-max15排除と見送り済み10,026-node証明書に隣接する
**候補endpoint**にすぎない。単なる証明書再実行、checker改善、lag上限追加は再開条件を満たさない。
現時点ではlag非依存のowner-offset構造入力がなく、**再開条件は未充足**。

`delta=r-kx` とold A-tailを使う案は、量化子・式未固定の将来カード前gate/候補入力であり、
exactな仮説でも承認済み新数学でもない。再開には、具体的不等式・有限分類・単調量のいずれかを
exactに凍結し、E-240/E-069/E-345、p16非最小対照、既知lag3/7正例、弱化history、非空の
全前提例を通す別の独立入口監査が必要。それまでは探索を開始しない。実軌道は別カードとする。

## 実行・来歴

今枠では新計算、研究Lean、vacuity、lint、`./scripts/check.sh` を実行していない。
現source hashと同一の01:00/01:30保存結果を参照し、両archive manifestを今枠で検証した。

- 01:00同版結果: vacuity 0/21、lint 20/21、`check.sh` exit0、392 jobs / 2572 declarations。
- 01:30同版結果: vacuity 0/13、lint 13/13。同枠の限定意味監査範囲は3宣言。
- 今枠manifest検証: 01:00 39/39、01:30 63/63、各exit0。
- repo開始対象hash: 15/15、exit0。
- 最終所在/表記checker: 29/29、exit0。ただしsubstring・宣言数/名前の機械照合に限り、
  全宣言・全前件の意味監査を代用しない。

監査checker v1はE-240を誤ってregistry `REFUTED`と期待し、REPO_TARGETSを誤cwdで空にしたため
exit1。source/prehash/rawを `source/inventory_check.v1.py`, `raw/run_v1/` に保存した。
v2はE-240を `PROVED-LEAN`へ訂正して19/19、対象hash15/15。v2 sourceの別名保存を後で失念に気づき、
v1から事後復元した `inventory_check.v2.py` が実行前hash
`33d13afe3ffebf96f2d86ab60bcecf9f9fcc524aa1ccec55ff78ad3b7ccf2489` と一致した。
初めから別名保存済みだったとは扱わない。

v3はH-05の13実数/未監査10名を正しく数えたが、writerに「全13宣言中、残る10宣言」という連続文字列を
要求したため1件だけ誤ってFAIL。source/rawを `inventory_check.v3.py`, `raw/run_v3/` に保存した。
v4は実際の10宣言名を照合し最終版で29/29。これらのchecker修理は意味合格の根拠ではなく、
直接の原文・source・旧監査照合が判定根拠である。

正確なargv/cwd/timeout/exit/stdout/stderrは `COMMANDS.md` と `raw/`、source/prehashは
`source/` と `prehash/` に保存した。runner内4 jobには各30秒timeout。短いread-only探索コマンドと
byte比較には外部timeoutなし。toolのyieldをtimeoutとは呼ばない。

## 最終手続判定

**合格（最終凍結候補の一覧・停止/再開記述のみ）。** repoは読取専用とし、研究source、gate、
protected claims、registryを変更せず、stage/commitなし。親が適用する場合は上記full案とのbyte一致を
別のPOSTAPPLY記録で確認する必要がある。適用前の本監査は数学的昇格や週間全体の最終heartbeat閉鎖を
代行しない。
