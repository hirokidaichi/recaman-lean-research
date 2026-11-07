# 毎日6:00〜8:00の研究スケジュール

最終更新: 2026-11-08。以下を2026-10-23以降の現行ルールとする。

- 毎日、日本時間（Asia/Tokyo）の06:00〜08:00。このチャットで研究・反証・形式化・監査・記録を継続する。
- 対象: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`。
- 予約ID `recam-n-6-8`、heartbeat、同じチャット。06:00開始、06:30/07:00/07:30は復帰用。
  **30分の境界は途中保存の時刻であり、研究やターンの終了時刻ではない。**
- 06:00前の配信は、数学を始めず1回60秒以下の待機と実時計確認で06:00まで待つ。待機は研究実績に含めない。
- 08:00以降は研究を始めない。遅延・中断があっても08:00を延長せず、不足分を正直に残す。
- 進行中の同じrunを初期化・重複実行しない。カード完了や途中保存だけを理由にfinalで当日の研究を終えない。
- 新しい数学探索は07:45まで。以後は必要な検証・意味監査・保存を行い、自分の計算も08:00までに終了する。07:59:40を目安にjournalを閉じ、終了報告用の余裕を残す。

## 再開する問いと参照順

2026-11-09の現行入口は[H-20261109-01](HYPOTHESIS_CARD_2026-11-09_UNIT_SECOND_S_ACTUAL_BOOTSTRAP.md)。[11/08 DAILY](RESEARCH_HANDOFF_2026-11-08_DAILY.md)末尾→[同target/source予算](RESEARCH_NOTE_2026-11-08_SOURCE_CLOCK_BUDGET.md)→同カード。E599/E601で第二A開始以降の全actual targetの元fullgapを供給済み。E603第二S残余1のsource6を元actual counterへ内部消費しM8/L7又はfullgapを供給する15分gate。E604 PAPER結論やbandを新Prop入力せず、全oldmass/源以前prefixを保持。進まなければq2 counter-conditioned source除去25分、任意runのfree課金20分へ。
11/08 H26一般第二A band/H39一般第二S band/H52小平方helper及び継承STOPを保持。H26の限定scopeは独立E600による新proof E601で閉じたが旧jobを再開しない。H52再開は三非負項の独立factor certificateと測定改善が必要。旧r4 E412/E427同表2回削減0/0は別保持。CPU探索当初0、07:45探索終了、確定journalとmain通常publication、必須日次報告を継続する。
以下の初回計画と日付付き履歴は当時の記録であり、最新の入口を優先する。

初回（2026-10-23）は[C1深さカード H-20261023-01](HYPOTHESIS_CARD_2026-10-23_C1_DEPTH.md)から始める。
問いは「padded BlockWord prefix後の正不足excursionで、d(q0)=1・a_z≤3から深さ≤4が一様に従うか」。
全量化子・仮定・反証・受入・停止条件はカードに固定した。C2の旧初日計画やPの入力監査からやり直さない。

開始時はAGENTS、AI_RESEARCH_PROTOCOL、本書、CURRENT_FRONTIER、当日カードを読む。
前日以後の最新DAILYから、その末尾で指定する追加handoff（2026-10-22は[MAKEUP](RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)）も読む。
必要なREADME/STATUS_REPORT/ROADMAP、GLOSSARY/PROOF_MAP、PORTFOLIO/REGISTRYの停止・反証経路を照合する。
翌日以降は直近の判断と未完了unitから選び、C1深さの一問も完了後は自動反復しない。

E-379〜E-381はPROVED-LEAN、E-382/E-383はCOMPUTED、E-384はPROVED-PAPER。
Q/C1/H/SL全体は未解決。Az独立非負・自由tag・同じUNKNOWNソルバの時間延長は再開しない。

## 時間割と継続の規則

| JST | 予定 | 作業 |
|---|---:|---|
| 06:00〜06:10 | 10分 | 実時計・前回handoff・作業木・journal、当日の問いと費用を確認 |
| 06:10〜06:25 | 15分 | 最新カードの最初の入力を反証・紙上診断し、継続か切替を判断 |
| 06:25〜07:10 | 45分 | 通過時は同じ未知edgeを攻める。不通過ならカードの別機構へ再配分 |
| 07:10〜07:40 | 30分 | 次の判断を変える局所探索。完了/反証unitを再実行しない |
| 07:40〜07:50 | 10分 | 別passの意味監査・必要検証。07:45以降は新規数学探索なし |
| 07:50〜08:00 | 10分 | 日次handoff・カード・frontier・briefと実績を保存、journalを閉じて終了報告 |

開始10＋研究・監査100＋引き継ぎ10＝120分。研究・監査は活用60・探索30・監査10。
表は定刻開始時の目安。遅延時は実開始と残り時間へ各unitの上限を縮め、過ぎた枠を遡って実行扱いにしない。
配分は予定であり、実績は時計で測る。検証超過は研究枠から差し引き、終了を延長しない。
15分で一つの方法が止まっても、残り時間の次の問いを固定して研究を続ける。
2 cycle連続して同じ障害でedgeも候補集合も変わらなければ活用40・探索50・監査10へ移し、
探索25分以上を別機構に使う。停滞回数を日付でリセットせず、停止枝の再開条件を守る。

未知の補題や一つの方法のSTOPPEDは、一日全体の終了理由にしない。別候補・弱化モデル・必要仮定の監査へ切替える。
利用者にしか供給できない資料/権限など外部入力が欠け、他の有用な研究・監査も進められない場合や、
利用上限・ツール障害で継続不能な場合のみ、
具体的理由と未消化時間を保存して終了する。同じ検査や待つだけで時間を埋めない。
早期終了や中断は後続の復帰予約で再確認するが、完了unitは繰り返さない。

## 実績journalの使い方

`python3 scripts/research_session.py`は実時計を使い、日次の確認済み区間を
`docs/data/daily_research/YYYY-MM-DD.json`へatomicに保存する。CLIの時計上書きはない。
これは担当が確認した作業区間のjournalであり、CPU profilerでも自動研究workerでもない。
journal未作成はnot_started/journal_exists=falseと表示し、過去の研究が0だったとは解釈しない。
導入前の朝18分51秒・追加98分13秒は元handoffのまま保持し、このjournalへ遡って追記しない。

```sh
python3 scripts/research_session.py status
python3 scripts/research_session.py start --phase setup --unit R-20261023-01/start
```

startのJSONにある`cursor.session`を保持し、以下の`SESSION_ID`をその実値に置き換える。
当日のcycle/unitも実際の値を使う。例のIDは10/23の開始点であり、毎日固定して使わない。

```sh
python3 scripts/research_session.py checkpoint --session SESSION_ID --phase research --unit H-20261023-01/input-1 --note "問いと停止条件を固定"
python3 scripts/research_session.py checkpoint --session SESSION_ID --note "仮定供給と最初の不等式を確認"
python3 scripts/research_session.py checkpoint --session SESSION_ID --phase audit --unit H-20261023-01/audit
python3 scripts/research_session.py checkpoint --session SESSION_ID --phase handoff --unit R-20261023-01/save
python3 scripts/research_session.py stop --session SESSION_ID --note "検証・handoff保存と計算終了を確認"
```

- 5分以内を目安に、少なくとも各unit/phaseの切替・06:30/07:00/07:30・終了前にcheckpoint。
  checkpointは直前のphase/unitの区間を確定し、次の区間を開く。open区間はstatusで実績へ先取りしない。
- setup/research/audit/handoffの確認済み区間の和集合を実績にする。重なりは二重加算しない。
  待機はwaiting、必須入力や障害待ちはblockedへ切替え、実績から除外する。
  有用な推論や実行中の計算監視は研究区間に含むが、純CPU/純思考時間とは呼ばない。
- 早い配信なら`start --phase waiting --unit prestart`、06:00にcheckpointでsetupへ切替える。
  07:45以降は新しいresearch区間、08:00以降は新しいactive区間を拒否する。遅いstopの時間はovertimeとして別記し、枠内実績へ加算しない。
- startが`already_active`なら、二つ目の研究を始めない。同じ継続中のturnなら既存tokenで継続する。
  新しい起動で前runが中断済み、または継続の実態が確認できない場合は以下で未確認区間をgapにする。

```sh
python3 scripts/research_session.py recover --session SESSION_ID --note "前runは中断。最後の確認以後を実績にしない"
python3 scripts/research_session.py start --phase setup --unit R-20261023-01/resume
```

recoverは過去のopen区間を研究時間に変えず、cursorを閉じる。未完了unitはカードから再開する。
単位の完了ではstopせずcheckpointを使う。finalでturnを終了する前にはstopまたはrecoverを必ず保存する。
前日journalは`status --date YYYY-MM-DD`で読めるが、過去へ時刻を遡らせて実績を追記しない。

## 保存・検証と運用条件

毎日`docs/RESEARCH_HANDOFF_YYYY-MM-DD_DAILY.md`とカードへ、開始/終了・journal参照・
確認済み実績秒・待機/中断/不足・予定と実績・CPU別計上・cycle/unit・新証拠・反例・継続/切替/停止・
変更ファイル・commands・不確実性・次の一問を保存する。CURRENT_FRONTIERとmake briefも同期する。
途中の通知は意味のある新証拠、失敗、判断が必要な場合だけ。日次の終了報告は進展の有無にかかわらず必須とする。
設定しただけで将来の120分を達成扱いにしない。

### 毎日の終了報告

通常は08:00までに検証・保存・自分の計算の終了とjournalのstopを済ませ、確定結果をこのチャットのfinalで日本語で報告する。
進展なし・不足・早期終了でも報告を省略せず、SKIPにしない。短い報告に以下を含める。

1. 日付、実開始/終了、`confirmed_work_seconds`からの作業時間（分秒）、120分に対する不足。待機/中断は除外する。
2. 今日わかったことを平易に説明し、証拠水準（PROVED-LEAN/COMPUTED/REFUTED等）と仮定・適用範囲を示す。新証拠がなければ「新しい数学的証拠なし」と明記する。
3. C1全体のどの未解決部分につながったか、何がまだ証明できていないか。証明数や作業時間だけで進展の大きさを表さない。
4. 進まなかった方法・失敗や不足の具体的理由。
5. 次回の一問、当日DAILYとjournalへのリンク。

06:30/07:00/07:30の途中保存では終了報告を先取りせず、同日の最終結果が既にこのチャットで報告されていれば後続配信で重複させない。
08:00以降の遅延配信では研究を始めず、当日journal/DAILYと報告履歴を照合し、未報告の当日結果だけを報告する。
終了済みjournalへstart/stopを追加せず、記録が欠ける場合は「実績を確認できない」と報告する。予定から実績やゼロ作業を推定しない。

AGENTSの役割分離と7 evidence labelを守る。CPU探索は当初0、必要時だけ実行前に予算・command・
discovery/独立holdout・revision/dirty source hashを固定して再配分する。
Lean変更は`./scripts/check.sh`、新規Leanはlint、必要なAudit/逐語statement auditを省略しない。
gate変更はmake test-tools。sorry/admit/native_decide/独自axiom、保護label・ゲート・commit間隔の迂回は禁止。
他セッションの変更を保持する。2026-11-01の利用者指示により、この研究で進めた範囲を
毎日commit・pushすることは継続して許可されている。個別の再確認は不要。

### 毎日のcommit・push（2026-11-01追加）

- 開始時のHEAD・branch・remoteとdirty差分から対象を固定し、自分の研究成果と必要な
  引き継ぎ・証拠だけを明示パスでstageする。他セッションの変更、lock/cache、認証情報は含めない。
- 07:45以降の検証・保存枠で必要なcheck/lint/Audit/statement auditを完了する。
  未検証Leanを採用せず、失敗・STOPPEDの記録は証拠水準を保持して保存する。
- journalをstopし、確定実績をDAILY等へ保存してから最終commit・通常pushする。
  08:00を延長せず、期限内に終えられない場合は未保存対象と具体的理由を報告する。
- `git add -A` / `git add .`、force push、hook/gateの無効化は禁止。
  2026-11-01に利用者が「今回と日次保存に限り許可」と明示承認したため、今回および
  今後の日次の検証済みsnapshotのcommitに限り、単一commandで`RECAMAN_ALLOW_BURST=1`を使う。
  module本数・30分間隔以外のG1〜G5・保護claim・逐語audit・反証の手順は維持する。
  flagを環境へ常設せず、同じ範囲について再確認しない。
- 2026-11-01の追加指示で研究branchをmainへ統合したため、継続する保存先は`origin/main`。
  開始時にfetchし、既存のremote更新を保った通常pushを行う。分岐があれば検証付きで統合し、
  安全に統合できなければforceせず未保存対象と理由を報告する。
  push後は`git ls-remote`で対象refとSHAを照合し、日次finalでcommit SHA、push先、成否、
  hosted CIの状態（未確認を含む）と未保存対象を報告する。差分なしなら空commitは作らない。
- 終了・報告済みの日を遅延heartbeatで再commitしない。publicationの失敗は次の許可された枠へ引き継ぐ。

このローカル研究には、実行時にMacを起動してCodexアプリを実行し、repoへアクセスできることが必要。
同じchatで継続するheartbeatとローカル実行条件は[公式Scheduled tasks](https://learn.chatgpt.com/docs/automations#schedule-a-task-inside-a-chat)で確認した（2026-10-22）。
アプリの停止・スリープ・利用上限をpromptだけで解消できるとは主張しない。実績の不足として記録する。

## 初回の失敗と設定履歴

2026-10-22の朝は18分51秒。早い配信を破棄し、30分の途中保存を終了期限にした実行制御が原因だった。
旧C2計画・予定枠を実績に足さず、[当日DAILY](RESEARCH_HANDOFF_2026-10-22_DAILY.md)の履歴は保持する。
元の06:00/06:30/07:00/07:30予約へ戻して継続指示を訂正後、今回の更新でC1の最新開始点と実時計journalを追加した。
期限付きの旧研究予約2件はPAUSEDのまま。新しい別chat/重複予約は作らない。
今回の追加研究98分13秒も朝と別計上し、[MAKEUP](RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)の結果を引き継ぐ。

## 2026-10-24の確定実績

06:00:14〜07:59:53 JST、confirmed_work_seconds=7178.944（119分38.944秒）。
待機68.233秒は除外、不足21.056秒。前日実績/予定/CPUの加算なし。
[DAILY](RESEARCH_HANDOFF_2026-10-24_DAILY.md)、[journal](data/daily_research/2026-10-24.json)。

## 2026-10-25の引き継ぎ

実績の正本は[当日journal](data/daily_research/2026-10-25.json)と[DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)。
6:01:21開始で起動遅れを遡及補填しない。予定setup10/活用60/探索30/監査10/handoff10分は実績ではない。
研究と並行するLean検証CPUを実時計へ加算しない。監査超過分は研究枠から支払い、8時延長はしない。
自動実行は同じID/ACTIVE/6:00,6:30,7:00,7:30/同じthreadを保持してH-20261026-01へ更新し、必須final報告も保持してreadback済み。

10/25のjournal確定値: 06:01:21.862027〜07:59:10.380882、117分48.519秒、不足2分11.481秒。正本は当日DAILY/journal。

## 2026-10-26の引き継ぎ

正本は[当日journal](data/daily_research/2026-10-26.json)と[DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)。次回はE416の実count接着から始め、元H01直接free-count/C2/P/完了二run/r3の再実行に戻らない。
CPU探索は0から。検証済み計測はcooperative single-Python worker（子を禁止）で、一般process-tree累積上限は未解決。Lean検証は別計上。

10/26のjournal確定値: 06:02:22.120877〜07:59:56.352321、117分34.231秒、不足2分25.769秒。正本は当日DAILY/journal。

## 2026-10-27 継続記録

実setup開始06:01:46.075185、session9b9ab67f-4cfe-4465-aa39-e3cd4b1ee012。予定setup10/活用60/探索30/audit10/handoff10分。起動遅れを8時以後へ延長せず、setupを実読取に合わせて縮め、次unitへ継続。親cycleはR-20261027-01一つで、card数/CPUを別cycleへ加算しない。正本は[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)。
07:44:59以降は新数学を始めずaudit/保存。終了時計/実績はstop後の確定値だけを下記へ追記する。

10/27のjournal確定値: 06:01:46.075185〜08:00:04.411787、118分13.925秒、不足1分46.075秒。待機/未確認/CPU/旧日加算なし。正本は当日DAILY/journal。

<!-- 20261028 actual -->
## 2026-10-28 実績と引き継ぎ

実開始 2026-10-28T06:00:23.396597+09:00、実終了 2026-10-28T07:59:36.524907+09:00。確認済み119分13.128秒、120分への不足0分46.872秒。waiting/blocked除外{}、gap0秒、CPU/前日分を加算しない。phase実績: setup 1分13.295秒 / research 70分32.302秒 / audit 34分47.446秒 / handoff 12分40.086秒。

正本は[DAILY](RESEARCH_HANDOFF_2026-10-28_DAILY.md)/[journal](data/daily_research/2026-10-28.json)。次は[H-20261029-01](HYPOTHESIS_CARD_2026-10-29_OLD_TARGET_TAIL.md)。07:59:40目安のstopで8時の余裕を確保し、予定120分を実績扱いしない。

## 2026-10-29 実績と引き継ぎ

当日journalの実開始06:03:24〜実終了07:58:49、confirmed 115分25.230秒、不足4分34.770秒。待機/未確認gapを研究時間へ加えていない。詳細な予定/実績・CPU/失敗は[10/29 DAILY](RESEARCH_HANDOFF_2026-10-29_DAILY.md)と[journal](data/daily_research/2026-10-29.json)。E451三run全長free-gapがPROVED-LEAN、四runE456は供給19/数値残余のみ。一般Q/C1は未解決。次は[H-20261030-01](HYPOTHESIS_CARD_2026-10-30_FOUR_RUN_OLD_TARGET.md)。

<!-- 20261031 confirmed -->
## 2026-10-31 実績と翌日入口

実開始 2026-10-31T06:03:36.178178+09:00、実終了 2026-10-31T07:59:49.141812+09:00。confirmed_work_seconds=6972.964、確認済み116分12.964秒、120分への不足3分47.036秒。待機/blocked除外{}、未確認gap0件。open区間は含めない。


次は[H-20261101-01](HYPOTHESIS_CARD_2026-11-01_MASS_THREE_ACTUAL_CHARGE.md)。E482の完了帯を再実行せず、E483の帯外mass3 target/old4をactualfreeへ接続する。自動実行の同ID/ACTIVE/6時・6時半・7時・7時半/同chat/必須final報告をreadback済み。未来の2時間完遂は未確認。正本は[DAILY](RESEARCH_HANDOFF_2026-10-31_DAILY.md)/[journal](data/daily_research/2026-10-31.json)。

## 2026-11-02 確定実績と次の入口

実開始2026-11-02T06:03:32.373375+09:00、実終了2026-11-02T07:58:30.167815+09:00。confirmed_work_seconds=6897.794、114分57.794秒、不足5分02.206秒。待機/中断/gap0、openなし。CPU/過去実績/stop後の公開時間を加えない。配信時点06:02:01.693からの実開始遅れを遡及補填しない。

正本は[DAILY](RESEARCH_HANDOFF_2026-11-02_DAILY.md)/[journal](data/daily_research/2026-11-02.json)。次は[H-20261103-01](HYPOTHESIS_CARD_2026-11-03_SHORT_SUPPLY_BAND_KERNEL.md)。E520/E522のactual source/last供給を利用し、factored-circleから新しいstrict候補削減を先に得る。五bandはPROVED-PAPERのまま。旧monolithへ時間/メモリを追加しない。自動実行の同ID/ACTIVE/同schedule/chatと次cardをreadback済み、未来の完遂は未確認。

2026-11-03確定: 実開始2026-11-03T06:00:02.472588+09:00〜終了2026-11-03T07:58:52.893434+09:00、confirmed 7130.421秒（118分50.421秒）、不足1分09.579秒、waiting64.987秒/gap0は除外。E535/R6未解決、H13 cap STOP、main研究snapshot8e3e14d＋後続確定metadata、hosted CIは未完了。[DAILY](RESEARCH_HANDOFF_2026-11-03_DAILY.md)を正本とし、翌日の実績へ加えない。

## 2026-11-08 確定実績と次の入口

実開始 **06:01:51.912245 JST**、実終了 **07:56:27.555859 JST**。`confirmed_work_seconds=6875.644`、**114分35.644秒**。120分に対する不足 **5分24.356秒**。待機/blocked除外0秒、未確認gap0秒、overtime0秒。開始遅れとstop後のcommit/push・remote/hosted CI確認時間を研究実績へ加えない。

phase実績: setup 1分27.657秒 / research 94分32.083秒 / audit 9分29.231秒 / handoff 9分06.672秒。終了済みjournalへstart/stopを追加しない。

[当日DAILY](RESEARCH_HANDOFF_2026-11-08_DAILY.md)と[翌日カード](HYPOTHESIS_CARD_2026-11-09_UNIT_SECOND_S_ACTUAL_BOOTSTRAP.md)へ続く。
