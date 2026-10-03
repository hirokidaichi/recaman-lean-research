# 2026-09-20 昼の研究引き継ぎ（16:30期限）

## 結論（14:50 JST checkpoint）

**短い緊密集合の供出回避と、短い供給集合での供出減算削除について、Leanで検証できる証明候補を作成した。**
独立の担当による監査は未実施で、成果台帳・既存Q/Wカード・frontierはまだ昇格していない。
全射性、全lag容量 E-070、E-067、一般 Gate T6 は未解決のまま。

14:28開始、利用者の期限は16:30 JST。この文書は途中の再開用記録であり、2時間を実働したという報告ではない。
対象カード: [H-20260920-01](HYPOTHESIS_CARD_2026-09-20_SHORT_OWNER_FUTURE.md)。
研究前のHEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`。コミット・ステージなし。
開始時からあった夜間カード・週間計画・夜間実験/監査・lag19 shardは変更していない。

14:53に追加研究heartbeat `recam-n-16-30` を作成したが、利用者の意図は
このターンで実時刻を見ながら継続することだった。訂正を受け、14:57にその
heartbeatをPAUSEDへ変更し、この場で16:30まで研究を続ける。
既存の夜間週間研究は変更していない。未返答を独立監査の許可と解釈しない。
15:02から [H-20260920-02](HYPOTHESIS_CARD_2026-09-20_DONOR_WITHOUT_MINIMALITY.md)
でdonor最小性を外せるかを別の有界研究単位として検証する。

## 得られた候補の正確な範囲

`Recaman/ShortTightDonorAvoidance.lean`:

1. **局所W**: 既存OwnerFamily（最小P2窓3/7/11、現在A、窓内Sを一つ所有、全被覆Sの所有者あり）で、
   w1=SAAAASSのメンバーは最古Sを所有し、次の符号はA。
2. **短い窓のHall**: 既存のshortOff単射の対応先が、各々の実際のP2窓の内部にあることを証明。
   単に全S集合へ入ることではなく、任意の短い窓集合Aの近傍N(A)へ入るのでHallが従う。
3. **短い緊密集合のQ**: 任意周期p>0の符号語、重複のない加算位相の緊密集合Bで、
   Bの窓が全て最小P2・長さ3/7/11なら、最小lag11・SS=2 donorの真の最古SはN(B)に属さない。
   **pの上限、全供給Uの完全性、正ドリフト、Hall仮定は不要**。Bの短さ・最小性は残る。
4. **削除の系**: 全要素の窓が最小P2・長さ3/7/11である供給リストUについて、donorの真の最古Sを削除しても
   Uの全sublistでHallが保たれる。**全lagの供給集合Uについての主張ではない。**

`OwnerFamilyLagEleven.lean` / `PeriodicOwnerFamilyLagEleven.lean` は、既存証明の内部構成を
`ownerFamily_of_minimal` / `tight_owner_family` として抽出した。旧登録定理のsignatureは保持した。
この抽出自体を研究成果とは数えない。

## 証拠と検証

- `lake build Recaman.ShortTightDonorAvoidance` 成功。新moduleは約19秒。
- `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean`:
  10定理中9本がsubstantive。`tight_w1_next_addition`は局所Wと周期liftの系。
- `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean`: 0/10 flagged。
- `./scripts/check.sh`: 全391 jobs成功、**2561宣言**の公理が許可集合内。
- `git diff --check`: 成功。
- 主要定理は `Recaman/Audit.lean` に追加。研究registry、protected claims、frontier、proof mapは未変更。
- [逐語statement監査草案](data/issue73_20260920/daytime/statement_audit_draft.md)と
  [登録行草案](data/issue73_20260920/daytime/proposed_registry.tsv)を保存。E-360はまだ実台帳へ登録していない。

再現入口:

```sh
python3 -u experiments/issue73_20260920/short_owner_future.py
python3 -u experiments/issue73_20260920/short_owner_holdout.py --mode regression
python3 -u experiments/issue73_20260920/short_owner_holdout.py --mode holdout --seconds 1800
python3 -u experiments/issue73_20260920/verify_short_owner_holdout.py
python3 -u experiments/issue73_20260920/short_owner_negative_controls.py
python3 -u experiments/issue73_20260920/short_owner_nonpositive_boundary.py
python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
./scripts/check.sh
```

全原出力は `docs/data/issue73_20260920/daytime/`。凍結holdoutは実行前hashと生成方式を保存した。
周期32・33それぞれ2000語。次表は有限計算に限る。

| p | donorを持つ語 | Qの非空B検査 | W適用 | 違反 |
|---|---:|---:|---:|---:|
| 32 | 147 | 1347 | 326 | 0 |
| 33 | 164 | 1598 | 341 | 0 |

初回は逐次和＋マッチング、検算は周期のmass/momentの閉形式＋全sublist Hallで実装し、
標本hashを含むperiod summaryが完全一致。閉形式は小周期で23,190ケースを直接和と照合した。
これは**同じ担当内の独立実装**であり、独立担当による監査の代わりにはしていない。
既存カードのp32/33 holdoutはここで使用済みになった。同じ標本を新しいholdoutと呼ばない。
全体の現snapshotは `daytime/SHA256SUMS` と `task_owned_paths.txt`。
`PRE_HOLDOUT_SHA256SUMS` のLean sourceは拡張前の版を指すため、対応する完全同一のソースを
`ShortTightDonorAvoidance_pre_holdout.lean` に保存して原hashとの一致を確認した。
現在のsourceへの検証は `check_extended.log` を使い、旧buildの成功を流用しない。

## 失敗と反例

- 局所検査v1がw1の最新Sを覆うw2候補を誤って除外し、assertionで失敗。
  v1ソースと失敗出力を保存。修正版はw2を残し、E-357による大域的なw2排除を明示した。
  命題の修理ではなく、局所表の期待値の誤りの訂正。Wの前提・結論は変更していない。
- `scripts/lakew`はこのホストで参照toolchainが無くexit127。利用可能な`lake`で全検証した。
  ラッパー自体は変更していない。
- 緊密性を外す反例: 周期11 `AAAASASASSS`、donor3、最古S位相4、B={5}、N(B)={4,9,10}。
  Bのlag7窓はw1だが緊密ではなく、donorのSを覆う。
- SS=2を外す反例: 周期12 `AAAASAAASSSS`、donor3の最小lag11窓は`AAASSSSAAAS`（SS=3）、
  最古S位相4、B={7}はAASでN(B)={4}。
- donor最小性だけを外した検査はp=1..12の3458語で反例未発見。
  不要と結論せず、仮定を保持。探索範囲を事後変更していない。
- ontoを外した一メンバー局所モデル、所有者を多値関係へ弱めたモデルでは次符号Sを許す。
- E-240の非AAS緊密例と、最古Sを誤ってoffset11に固定するとAを選ぶp15例は保たれる。
- 正ドリフトを仮定しないことの境界確認: p14/15/16で周期質量0/-1/-2、donor11と非空tight B={10}を持つ
  明示語を検査。短い窓だけを扱い、非正ドリフトで全lag探索上界が有効だとは主張しない。

## 残る不確実性と次の判断

1. 独立Sol監査の可否を利用者へ確認中。許可が来たら、別担当にsource・仮説カード・原ログを渡し、
   定義・signature・周期境界・hF供給・反例・全検証を攻撃させる。監査対象のhashを固定する。
2. 独立監査が通った場合だけ、登録草案を実台帳へ移し、正式statement監査・frontier・proof mapを同期。
   元の夜間資料は書換えず、本日の結果への追補で履歴を保存する。
3. 未許可・未完了なら、Lean検証済み候補として残す。独立監査合格とは書かない。
4. lag15以上を含む緊密集合は扱っていない。既存有限探索の範囲延長や検査器最適化だけを次の研究単位にしない。
5. 16:30に終了。進展のない時間埋め、無目的な再ビルド、恒真式の追加、中心claimの昇格はしない。
