# 2026-09-21 Sol 夜間研究引継ぎ

## 結論

01:30枠で全体検査を回復し、Q/W の登録前 statement 資料と既存 E-359 の証明説明を整えた。
**限定修復は独立監査で合格。正式な新規登録・証拠ラベル昇格は未完了。**
Q/W カードは `CONJECTURED` のまま。数学sourceや台帳は変更せず、Lean変更は通常importの1行だけ。
一般 lag の新探索、commit はまだ行っていない。以下の01:00枠の差戻しは当時の履歴として保持する。

## 01:00枠の開始と担当

- heartbeat: 2026-09-20T16:02:11.080Z。実時計: 2026-09-21 01:02:25 JST。
- 実行中の既存 worker がないことを確認して、新規 Sol を2人起動。
- 再現: `/root/sol_20260921_core0100`、敵対監査: `/root/sol_20260921_adversary0100`。
- 両者 `gpt-5.6-sol` / `xhigh` / `fork_turns="none"`。親は数学探索・Lean実装を代行していない。
- worker は01:13:44までに補助 build と残プロセス確認を終了。監査者も報告訂正後に全処理停止を報告。
- 各担当の期限は01:25、親の枠は01:30まで。時間を埋める追加探索を開始しない。

## 今回の一問と版

昼に追加された局所 W と元の短い緊密集合の donor 回避 Q は、元カードの意味と依存を満たすか。
対象は `Recaman/ShortTightDonorAvoidance.lean` の `short_tight_avoids_ss2_donor` までの10定理と
必要な OwnerFamily 構成2件。量化子・全仮定・結論は
[逐語 signature](data/issue73_20260921/slot0100/core_signatures.txt)、対応は
[候補記録](data/issue73_20260921/slot0100/core_candidate.md)にある。

HEAD `08c08565c743f39350c9b959e1df7d30aa1cae5d`、未コミット source の SHA-256:

- ShortTight: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- OwnerFamily: `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`
- PeriodicOwnerFamily: `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`

## 最も強い証拠と失敗

[正式な親監査記録](adversarial_audits/H-20260920-01_20260921_0100.md)の総合判定は **差戻し**。
[監査者原報告](adversarial_audits/H-20260920-01_20260921_0100_files/audit_report.md)
の SHA-256 は `377f3a361ff85471c5ad6beaef6f9839a432d805d5194870b18dd03e633ea406`。

- 対象単体 Lean は両担当 exit 0、依存込み target build は110 jobs成功、source hash不変。
- vacuity 0/21 flagged、lint 20/21 substantive。自動検査を意味監査の代用にしない。
- 独立 Sol が OwnerFamily の全フィールド、短い Hall 構成、周期への移送、E-351循環不在、
  最小 lag、真のoffset、非空例と弱化モデルを直接検査。元 Q の結論を弱めていないとの限定判定。
- `./scripts/check.sh` は exit 1: `module is outside the Recaman root closure: Recaman.SS2OldestPattern`。
  対象外の昼の変更を削除・改変したり、ゲートを緩めたりしなかった。
- 公式 G5 audit は未完成。昼の草稿は7引用であり、今回 core の全宣言は網羅していない。
- 昼は独立の形式化前入口検査を未実施。今回の事後監査で履歴を遡及変更しない。
- 監査 checker 初回の E-240 assertion の誤りを修正したが、旧 source と raw log は未保存。
  最終版は保存済み。監査工程の証拠欠落として残す。
- 候補を破る新反例は報告されなかった。SS3、非緊密、onto除去等は弱化に対する既知対照であり元 Q/W の反証ではない。

[実行コマンド・timeout・exit](data/issue73_20260921/slot0100/commands.md)と raw log を保存した。
主なコマンドは `report_vacuity.py --all`、`harness_gate.py --lint-module`、`lake env lean`、
`lake build Recaman.ShortTightDonorAvoidance`、`./scripts/check.sh`、既知の p<=11 回帰、局所対照。
独立 checker は監査ファイル群に保存し、原ログの B と報告の B の不一致は監査者が訂正した。

## 旧夜記録からの訂正

9/20夜の終了記録は当時の履歴として保持する。その後の昼の別セッションで Lean 候補が追加され、
p32/33、seed `2026091801`、各2000語の元 holdout も使用済みとなった。
同作者の別アルゴリズム比較はあるが、本枠は当該 holdout 全体を独立認証していない。
従って旧カードの「holdout・Lean未実施」は9/20夜時点の記述であり、現在の未使用宣言ではない。
今回 holdout は再実行していない。

01:30の壊れたゲート実装枝、02:00の前件0件だった proper-U probe の停止は保持する。
再修理・上限延長による再開は行っていない。p20の新しい別の非空対照があっても、旧probeの成功には読み替えない。

## 未監査の候補

[対象外一覧](data/issue73_20260921/slot0100/pending_candidates.md)を次回も読む。
`short_supply_donor_deletion`、donor最小性除去、prefix reduction、length15反例、
任意長 minimal donor pattern、`SS2OldestPattern` は今回の意味監査の対象外。
H-20260920-04 の昼カードには自己ラベル `REFUTED` があるが、本夜の独立承認ではない。
他の昼カードや成果物は改変していない。すべて登録や後続の確立根拠として使用しない。

## 変更ファイルと次の判断

本枠の変更は元夜カードへの日時付き追記、本引継ぎ、`docs/data/issue73_20260921/slot0100/`、
`docs/adversarial_audits/H-20260920-01_20260921_0100.md` とその `_files/`。
Lean source、台帳、保護ラベル、ゲート、frontier、proof map は変更していない。

次枠は独立検査の未解決事項を優先する。限定した一問は「昼の変更を保持したまま、core候補の
正規の検査・登録前資料を整え、別 Sol が差戻し事項の解消を確認できるか」。
対象外モジュールの統合修正をする場合は担当範囲を事前固定し、修正者と合否判定者を分ける。
全体 check を成功させるために未監査の定理を確立済みにしない。変更した依存先は再監査する。
既存の限定意味監査だけを根拠に台帳登録しない。新しい一般 lag 探索は、この残務と別のカード・入口監査を必要とする。
一般 Gate T6 の donor を含む部分集合、一般 lag の容量、実軌道は依然別義務である。

## 親の終了確認

2026-09-21 01:20 JST、両 Sol の状態が completed であることと、各担当の残処理なし報告を確認。
監査7ファイル、再現16ファイルの `shasum -a 256 -c SHA256SUMS` は全件 OK。
監査 manifest の SHA-256 は `7705c578fa4fed4cd3a8d80bbff39efbd6332309bb83a834bb55f2c035283048`、
再現 manifest は `67a561b2b986dcde61209b9b4f86f7f84a969e71205ec29c84fe7206244964c7`。
開始時と終了時の対象3 source、SS2OldestPattern、Recaman root / Audit、台帳、保護ラベル、計画書の
hash は不変。他作業の変更を保持し、ステージ・commit・予約延長なしで01:00枠を閉じる。

## 01:30枠: 限定修復の合格

開始実時計 01:32:14 JST。新規修正 Sol は `/root/sol_20260921_repair0130`、
新規独立監査 Sol は `/root/sol_20260921_repair_audit0130`。
両者 `gpt-5.6-sol` / `xhigh` / `fork_turns="none"`。既存実行workerとの重複なし。

一問は、凍結 W/Q の数学を変えず全体checkとstatement資料の不足を正規手順で修復できるか。
独立入口点検後に root へ `import Recaman.SS2OldestPattern` を1行追加した。
開始時からの ShortTight import は保持。通常の到達性契約を満たすための統合であり、
SS2OldestPattern を数学的に承認した操作ではない。

さらに既存 E-359 公式auditが抽出前の証明本体を説明していたため、親が担当範囲を明示的に追加し、
証明の所在地・wrapper分類・9/21同期注記だけを修正。構成は `tight_owner_family` に残り、
呼出側はcomposition wrapper。既存proofの抽出を新規成果に数えていない。
旧版、各修正前版、diff、失敗checker source/rawを保持した。

監査記録: [H-20260920-01_20260921_0130](adversarial_audits/H-20260920-01_20260921_0130.md)。
判定は限定修復 **合格**、新core登録 **未完了**。
数学3sourceのhashは01:00から不変。変更対象版:

- root `Recaman.lean`: `119a3d2a02a4d486f63077f37112f2ae81a7122d20d7633596c77d45b3c0d2be`
- `docs/statement_audits/E-359.md`: `0706d92df9ed5a93dd3f7d08ebcc27e20fb03b7d82a0a65330b2838bcf5e2a4c`
- [登録前packet](data/issue73_20260921/slot0130/statement_audit_pre_registration.md): `7b0c3da12f240e5d2a5b4f56bfe11ed08f435bf3cc3cb6a7af3d4e8372149af9`
- [独立監査原報告](adversarial_audits/H-20260920-01_20260921_0130_files/audit_report.md): `836ee4d62527e1b93cf9cb37f7a626173969d2a9dc5ef85b364ed420ec06e47f`

検査は両担当の fresh `./scripts/check.sh` exit 0、392 jobs、公理監査2572。
module到達389/389、import contracts110、既存registry359行と保護4行が通過。
coreの vacuity 0/21、lint20/21、10定理と構成2件の逐語82行が一致。
このG1-G5成功は既存登録行に対するもので、未登録coreの新規行検査が済んだとは言わない。
独立対照は固定周期8語・7donor・局所配置、seedなし、cutoff `p(p+1)`。
v1でp8 Bを誤記してKeyErrorになったが、失敗版を保存して訂正。v2/v3は成功し、仮説修理や新holdoutとは扱わない。

今回の変更はroot1行、E-359文書、slot0130資料、親の本引継ぎ・元カード追記・監査保存。
数学モジュール、Audit.lean、registry、protected、gate、frontier、proof mapは不変。
修正 [manifest](data/issue73_20260921/slot0130/SHA256SUMS) はrepo root相対30件、
独立 [manifest](adversarial_audits/H-20260920-01_20260921_0130_files/SHA256SUMS) は自身のディレクトリ相対33件。
親の検証はいずれも全件OK。親の最初の修正manifest検証はcwdを誤ってexit1、その後正しいrootでexit0。

次の一問: 正式な登録用symbol list・新規行・G5文書を隔離草稿に固定し、別Solが
主張と既存証拠を照合して、未監査候補を混ぜず登録可否を決められるか。
監査合格前の実台帳編集・昇格はしない。履歴の入口欠落と01:00の初回checker欠落も明示し続ける。
新しい人間承認条件や永久停止条件を追加したわけではない。実行時は適用直前の版を再確認する。
後半定理・SS2OldestPattern・使用済p32/33 holdout・一般lag/T6/実軌道は別の未監査対象のまま。

監査担当は01:47:19、修正担当は01:49:21 JSTに残処理なしと報告し終了。
親は監査と原ログ・hashを照合してこの枠を閉じ、期限を延長しない。

01:53 JSTの親最終確認: 両担当 completed、`git diff --check` exit 0。
rootとE-359文書は上記最終hashに一致し、数学3source・SS2OldestPattern・Audit.lean・台帳・保護ラベルは開始時hashと一致。
ステージ・commit・予約変更なしで01:30枠を終了した。

## 02:00枠: 凍結 core W/Q の E-360 登録

結論: 3-symbol の限定 E-360 登録案は独立意味監査と隔離 G1-G5 を通過した。対象は
`w1_owns_oldest`、`w1_next_addition`、`short_tight_avoids_ss2_donor` のみ。W は4フィールドの
`OwnerFamily` を明記した条件付き局所定理、Q は正周期・nodup/tight/current-A・最小 P2
lag 3/7/11 の B と最小 lag-11 SS=2 donor に限る。一般 lag/Gate T6、後半定理、
`SS2OldestPattern`、実軌道、E-070/E-067、Recamán列の全射性へ広げない。

初稿の2-symbol行は W の `own t=t-7` を引用しなかったため文書不整合として差戻し、旧版とhashを
保存した。`w1_owns_oldest` を加えた修正版は数学source・仮説・結論を変えておらず、数学的な修理ではない。
昼の形式化前入口監査欠落と01:00 checker初回source/raw欠落も解消したことにしない。

隔離 `/tmp/recaman-registration-0200.WgTYMy/repo` に提案 registry、公式配置形 G5、frontier、
proof map を配置して検査した。G1-G5 11行、protected 4行、registry 360行 / PROVED-LEAN 155行、
module reachability 389/389、import contracts 110、full check 392 jobs、公理監査2572、全て exit 0。
vacuity は0/21、lintは20/21 substantive。後半21定理全体の意味認証とは扱わない。

カード2本、registry、G5、CURRENT_FRONTIER、PROOF_MAP、本handoffの適用前全文と提案全文、source
hash、正確な command/timeout/output、独立監査判定を slot0200 に保存した。保護ラベル、Lean source、
gate は変更しない。次の判断は、適用版の全hashを独立監査者が再照合した後にこの限定登録を確定するか、
不一致ならカードを `CONJECTURED` のまま保つこと。一般 lag の探索は別の入口監査を要する。

### 02:00枠の親による適用後確認

**E-360登録を完了、独立敵対監査の最終判定は合格。**
両カード H-20260917-01 / H-20260920-01 は限定したQ/Wについて `PROVED-LEAN`。
担当は `/root/sol_20260921_registration0200` と、別の
`/root/sol_20260921_registration_audit0200`。両者Sol/xhigh/fork none。
監査記録は [H-20260920-01_20260921_0200](adversarial_audits/H-20260920-01_20260921_0200.md)。
そこに全対象版・変更ファイルhash・3本の逐語signatureへの参照・攻撃・反例・残義務を保存した。

親は適用前承認 `485e1bac1f7c9a496b98133f3d77e0b82eb5d6bc53dfadd4e748d8f74b816660` と
隔離検査を照合してから適用許可。02:20:47適用後に7/7 payloadが承認版とbyte同一であることを
独立監査者が確認。実台帳のG1-G5/protected/diff-check/全体checkも両担当でexit0。
最も強い証拠は有限計算ではなく、正確な3定理のLean証明・逐語監査・独立意味監査。
全体結果は360行/PROVED-LEAN155行、392 jobs、公理監査2572件。
新Leanやゲート変更はなく、他セッションの数学変更を保持した。

最終独立報告hash: `1356c0cd73692939cbae161f13c0012300b829d88cea68b4338e6abb66e2adcf`。
監査28件manifest: `e8c4d1ef56556f196a1a04547e78c61215207de21db27ccb698d44205bbef8f4`。
執筆35件manifest: `cea01ab4661643495e42afc2303bd531f10caaf24c2bc0a577decbbaa0303c95`。
適用後6件manifest: `f32568b017503901845f1db6b12730e5f5b63956d8cdad3b0b53ab14cd516757`。
親の各hash検証は全件OK。適用直後handoffhashは `a202f522...`、本節はその後の親の記録追記である。
G5のapplication pendingは適用前承認時点の文言で、適用完了は本節と原記録で確認できる。

未解決の指摘: 昼の形式化前独立入口検査欠落、01:00初回checker資料欠落は履歴として残る。
E-360の範囲外には登録権限を与えていない。使用済p32/33の再認証、後半定理、SS2OldestPattern、
一般lag・一般Gate T6・実軌道・全域性は別義務。初稿2symbolの引用不足は修正済みで旧版を保持。

次の02:30枠では、新探索ではなく未監査候補を優先する。一問の候補は、
`short_supply_donor_deletion` の既存候補が「全Uの窓が短い」という制限を保った正確な削除命題かを、
入口点検と別Solの独立監査で判断できるか。今回のQ合格だけでこれを自動昇格しない。
02:50 worker終了、03:00親終了を延長しない。登録済みQ/Wの同じ検査を成果として反復しない。

02:24:36 JST 親最終確認: 両 Sol は completed。`ps` に今回の隔離実験・Lean/check の残処理なし。
数学3source、登録6ファイル(親追記handoffを除く)、protectedのhashは承認版と一致。
`git diff --check` exit0。監査記録・引継ぎの親追記以外に承認後の変更なし。
ステージ・commit・予約変更をせず、02:00枠を終了する。

## 02:30枠: 短い供給集合の削除系を認証

**既存の `short_supply_donor_deletion` は限定された系として独立監査に合格した。新しい数学的入力ではない。**
新カード [H-20260921-01](HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.md) を
`PROVED-LEAN` に更新した。E-360のQ、短窓Hall、E-188の緊密/余裕ありの削除補題の直接的な系であり、
新規registry行・E番号・frontier/proof-map更新は行っていない。Leanも変更していない。

開始実時計02:31:20 JST。執筆Solは `/root/sol_20260921_deletion0230`、
独立監査Solは `/root/sol_20260921_deletion_audit0230`。両者gpt-5.6-sol/xhigh/fork none。
前workerのcompletedを確認して起動し、担当期限02:50・親期限03:00とした。
監査者はrepo読取専用で、反例実験を `/tmp/recaman-audit-20260921-0230-sol/` に隔離した。

一問は、全Uの窓が最小P2 lag3/7/11の加算位相という制限を保ち、実際のS削除後の
Hall不等式を全 `B.Sublist U` に与える非空の系かを判断すること。
Uは必ずしも全供給集合でなくてよい。complete Uであっても全員all-shortなら適用可だが、
無制限lagのcomplete supply setには適用できない。donorは最小P2 lag11かつSS=2。

監査記録: [H-20260921-01_20260921_0230](adversarial_audits/H-20260921-01_20260921_0230.md)。
手続判定は合格。target source hashは引き続き
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`。
承認された適用カードhashは `c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb`。
独立監査者がliveと承認案のbyte同一を確認した。
registryは `012c7e42974931c115efc2e64d9a254deaeb58ff78ac440af713cdb1a497a076` のまま。

最も強い証拠は、既存 `Recaman/Audit.lean:2701` のexact定理、逐語・定義・依存の意味監査。
両担当の全体checkはexit0、392 jobs、公理監査2572、registry360/PROVED-LEAN155。
vacuity0/21、lint20/21も確認したが、新規性の証拠にはしていない。
実行コマンド・timeout・source・未加工原ログは [slot0230](data/issue73_20260921/slot0230/MANIFEST.md) と
[独立commands](adversarial_audits/H-20260921-01_20260921_0230_files/commands.md)にある。

独立反例対照では、p8でdonorを含むBの近傍{0,1,4}から真の最古S位相0を実削除して{1,4}となり成立。
p11の非緊密Q対照は本削除系では正例であり、混同しなかった。
SS=2を外したp12、U=B={2,5,7}は残る全仮定を満たすが、3近傍から4を除くと3<=2が偽。
空集合だけの検査ではない。これらは固定既知例で、新holdoutや無限範囲の計算証明とは数えない。

失敗と訂正: 初稿はASCII変換した引用を逐語/rawと呼び、inline計算sourceを欠き、check抜粋をrawと呼んでいた。
全て差戻し、旧版・summaryを残して実source引用、保存再現script、未加工出力へ修正した。
独立報告の「真のoffsetでだけ不等式成立」も親が差戻した。偽offset11がAを選べば削除no-opで
Hall自体は通り得るため、意味の誤りと不等式の真偽を区別する文へ訂正した。

独立最終報告hashは `7181437282ffc3874598186a73d4f1f05201d0275820a0e2037f736d11156e07`。
親保存の17件manifestは `e38ff1d99b5ea2d7668cbe18756698ac50fd855afc153164e0067cf889cf0f97`、全件OK。
旧報告・旧commandsも保存した。昼の事前独立入口検査欠落と01:00初回checker資料欠落は履歴として未解決。

次の判断: この系を新しい研究成果として再登録・量産しない。週間計画後半の一般lag所有者配置へ進む場合は、
任意所有offsetと最古Sのずれを保持した一問を新カードに固定し、座標変換だけを新規性にしない入口監査から始める。
既存の非最小donor/prefix/length15/SS2OldestPattern等の未監査拡張を確立済み前提に使わない。
一般lag探索は最大2晩、9/24は週間監査という上限を変えず、今夜は追加探索を開始しない。
一般Gate T6のdonorを含む部分集合、全供給容量、実軌道、数列全射性は別義務として残す。

最終照合: 執筆manifest `7263d334c1c813a2e332123df1a4952b463aac4d58728cef28f2ff0a430c83b5`
をrepo rootから検証し22/22 OK、独立監査archiveは17/17 OK。ともにexit0、02:51 JSTにも再確認した。
途中のcwd誤りと適用中の旧manifest不一致は監査記録に残し、最終凍結版の成功と区別した。
02:48:34 JSTまでに両Solのcompleted・残処理なしを確認済み。担当期限02:50を越える研究処理は残していない。
親は03:00前に保存して終了する。ステージ・commit・予約変更なし。
