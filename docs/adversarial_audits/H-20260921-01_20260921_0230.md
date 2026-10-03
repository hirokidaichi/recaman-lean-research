# H-20260921-01: 2026-09-21 02:30 短い供給集合の削除系監査

## 結論

**正確な限定系の独立意味監査は合格。新しい数学的入力ではない。**
`short_supply_donor_deletion` は E-360 のQ、短窓Hall、E-188の削除補題を合成した既存の系である。
現行Leanで受理され `Recaman/Audit.lean:2701` に収載済みのため、カードは `PROVED-LEAN` が正確。
新規台帳行・E番号・frontier更新は行わない。一般Gate T6への解決宣言はしない。
親は訂正後の独立報告、正確なsource、再現scriptと未加工出力、full checkを照合してカード適用を許可する。

- 開始実時計: 2026-09-21 02:31:20 JST。日本時間の許可期間内。
- 候補整理担当: `/root/sol_20260921_deletion0230`。
- 独立敵対的監査担当: `/root/sol_20260921_deletion_audit0230`。
- 両者 `gpt-5.6-sol` / `xhigh` / `fork_turns="none"`。既存workerは全てcompletedを確認。
- 監査者はrepo読取専用、実験・原記録は `/tmp/recaman-audit-20260921-0230-sol/`。
- 02:50に担当・処理を終了し、03:00までに親がまとめる。新規数学探索・Lean実装はしない。

## 一問と対象版

一問: 全Uのメンバーが最小P2 lag 3/7/11の加算位相という制限を保った削除系が、
非空で実際の削除を扱い、一般T6や新しい数学的入力へ誤解されず認証できるか。
合格条件は全仮定・量化子・定義・依存と日本語の一致、非空/実削除/弱化対照、逐語資料、
原証拠の再現、Lean/意味監査の区別。source修理、空虚性、意味不整合、期限なら昇格せず止める。

HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`。

| 対象 | SHA-256 |
|---|---|
| ShortTightDonorAvoidance.lean | `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85` |
| TwoSSAvoidTight.lean | `59650732f2253c9f1b76cfebc80dd7c935b7bd347887a88e504a67ec2c703e01` |
| TwoSSTightDisjoint.lean | `06186b6fc55f343cfe5dab332fdfd76cce31aef02b6fba8027af1db9acebbd81` |
| TrueOldestGateT6.lean | `b02048eced0c2251f7587306cd288157fc834205b64811d255709949255aff19` |
| registry (不変) | `012c7e42974931c115efc2e64d9a254deaeb58ff78ac440af713cdb1a497a076` |
| 承認済み最終カード案 | `c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb` |

正確な対象は `Recaman.ShortTightDonorAvoidance.short_supply_donor_deletion`。
任意のe、p>0、周期性、nodup U、各uの範囲内/current-A/minimal-P2 lag 3/7/11、
任意u0の最小P2 lag-11 SS=2窓、任意 `B.Sublist U` から、
`B.length <= (deletedNeighborhood e p B lag (trueOldestPhase e p u0 11)).length`。
逐語と定義展開は [statement資料](../data/issue73_20260921/slot0230/statement_audit_draft.md)、
原source引用は [独立snapshot](H-20260921-01_20260921_0230_files/target_signature.repo_snapshot.raw.log)。
U完全性・donorのU所属・positive driftは仮定しない。complete Uであっても全員all-shortなら適用できるが、
無制限lagのcomplete supply setへの適用は認められない。

## 攻撃と証拠

`deletedNeighborhood`を実近傍から1位相を除くfilterへ、`trueOldestPhase`を真のoldestOffsetへ展開。
結論の仮定化、矛盾、H→H、x=x、自由算術だけ、定義済みPropへの隠蔽、循環を点検。
短窓Hallから緊密/余裕ありに分け、前者でE-360の非所属、後者でE-188の1要素削除を使う。
構文lintではsubstantiveでも、新しい数学的入力ではないと判定した。

- p8 `SSAASAAA`、U={3,7}、donor3。B={3}と{3,7}の近傍{0,1,4}から真の最古位相0を除き、
  {1,4}になっても不等式は成立。donor含有・非ゼロ削除を確認した。
- 同じp8のB={7}は緊密で近傍{4}、真の最古0を回避する。
- p11 `AAAASASASSS` のB={5}は {4,9,10}から4を実削除して成立。これはQの非緊密対照だが本系の反例ではない。
- E-240 p18では非純AASの既知緊密集合を保持し、短いfullUの全32sublistが成立。
- p15の偽offset11はA位相7を選ぶため削除はno-op。誤った位相でもHall自体は通り得るので、
  Boolean結果だけで意味監査を代替しない。真のoffset10・位相8で全16sublistを確認。
- SS=2を外したp12 `AAAASAAASSSS`、U=B={2,5,7}は残る全仮定を満たし、近傍{4,10,11}から4を除くと3<=2が偽。
  これは弱化の反例であり、対象定理の反証ではない。
- 空B、重複U、donor条件を満たさないp10/p20を境界・非適用対照として区別。

独立checkerは新規に書かれた固定既知例用。seedなし、最小lag走査は1..p(p+1) inclusive。
発見範囲の拡張や新holdoutはなく、使用済p32/33の独立認証はしない。
検査は両担当のfull check exit0、392 jobs、公理監査2572、registry360/PROVED-LEAN155。
vacuity0/21、lint20/21、独立直接Lean検査exit0。数学source・台帳・ゲート・保護ラベルは不変。

## 差戻しと修復

執筆初稿はASCII変換した引用をraw/逐語と呼び、inline実行のsource全文を欠き、fullcheckの抜粋をrawと呼んでいた。
独立監査と親の照合で差戻し、旧誤版・summaryを保存したうえでsource逐語、保存scriptの再実行、
未加工stdout/stderrへ置き換えた。研究の数学を修理したのではなく、証拠記録の誤表示を直した。

独立監査報告にも「真のoffsetだけで不等式が成立」との過剰表現があったため、親が原資料と照合し差戻した。
監査者が「偽offsetはAを削除するno-opで、Hallは通り得るが意図した削除の証拠でない」へ訂正。
旧報告を残し、訂正後の報告hashは `7181437282ffc3874598186a73d4f1f05201d0275820a0e2037f736d11156e07`。
適用前確認用コピーは [audit_report.approval.md](H-20260921-01_20260921_0230_files/audit_report.approval.md)。

## 未解決と判断

本系だけを認証し、新規E行・新たな研究成果数として加算しない。Q/W(E-360)の登録範囲を一般化しない。
ss2Windows以降、SS2OldestPattern、無制限lag、一般Gate T6、E-070/E-067、実軌道、数列全射性は対象外。
昼の事前独立入口検査欠落と01:00初回checker資料欠落は未解決の履歴として保持する。
カード適用版と最終manifest・終了確認は以下に追記する。

## 適用と保存

親の照合後、承認版カード `c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb` を適用。
独立監査者は適用カードと提案版のbyte同一、数学source/registry/protected不変を再確認した。
適用前のカードは `24b36a...` として執筆資料に保持。原比較は
[source_state.raw.log](H-20260921-01_20260921_0230_files/source_state.raw.log) にある。

親は最終独立報告・checker・原出力・旧報告/commandsを17件byte同一で保存し、全件hash一致を確認。
最終監査manifestは `e38ff1d99b5ea2d7668cbe18756698ac50fd855afc153164e0067cf889cf0f97`、
[原報告](H-20260921-01_20260921_0230_files/audit_report.md)は上記 `718143...` のまま。
checkerコマンドのcwd/絶対パスも監査者が明記し、旧commandsを保存している。

親の執筆manifest照合は最初にcwdを誤ってpath不在となり、正しいrepo rootでの再試行時には
カード適用中の旧manifestに対してカード1件が不一致だった。後者は承認版への適用を反映する前の
manifestだったため、最終凍結版で再検証する。未確認の時点を成功とは記録しない。

## 最終照合と終了

最終凍結後、repo rootで
`shasum -a 256 -c docs/data/issue73_20260921/slot0230/SHA256SUMS`
を実行し、22件全てOK、exit0を確認した。02:51 JSTの再確認でも同じ結果。
執筆manifestのSHA-256は
`7263d334c1c813a2e332123df1a4952b463aac4d58728cef28f2ff0a430c83b5`。
独立監査archiveもそのディレクトリから `shasum -a 256 -c SHA256SUMS` を再実行し、17件全てOK、exit0。
上記の途中の照合失敗は最終凍結版の不一致ではなく、履歴として残す。

02:48:34 JSTまでに両Solのcompletedと残処理なしを親が確認し、02:50の担当期限を守った。
02:51 JSTにもcompletedを再確認した。新たな探索・計算は開始していない。
ステージ・commit・予約変更は行わず、親の監査記録と引継ぎの追記だけで本枠を閉じる。
