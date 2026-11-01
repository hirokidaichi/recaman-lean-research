# 日次研究の自動実行の見直し

## 結論

既存の`recam-n-6-8`を更新した。毎日06:00〜08:00 JST、同じチャットで継続し、
06:30/07:00/07:30は復帰・保存用のまま。新しい予約や別チャットは作らない。
2026-10-23は[C1深さカード](HYPOTHESIS_CARD_2026-10-23_C1_DEPTH.md)から再開する。
予定だけで120分を達成扱いにせず、実時計journalで確認済み実績・不足・中断を保存する。

今回の作業は研究運用の設定変更であり、6〜8時の数学研究や新しい数学的証拠として加算しない。
明日の120分の実行結果は未検証。設定変更とその実績を区別する。

## 原因と変更

朝18分51秒の原因は、早い起動の破棄、30分境界を終了期限とした指示、unit完了後の早期終了だった。
既に継続指示へ直した予約にも、古いC2初日計画が残っていた。今回それを取り除いた。

- [今回のMAKEUP](RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)とE-379〜E-384を引き継ぐ。
- C1「a_z≤3から深さ≤4を一様に導けるか」の全量化子・仮定・受入・15分判定を次カードへ固定。
  反例が強い補助入力だけを反証した場合、親Q/C1を反証扱いにしない。
- 30分保存や一枚のカードの完了でfinalにせず、次の有用なunitへ続ける。遅延は残時間へ再配分し、8時を延長しない。
- 7:45以降は新規探索を始めず、監査と保存。進行不能時は具体的理由・不足を残し、待機で埋めない。
- `research_session.py`で確認済み区間を記録。待機・障害待ち・中断の未確認区間を実績から除外。
  区間は和集合で集計し、同じrunや並行CPUを二重計上しない。
- 未作成journalはnot_startedであり、過去の研究が0だったとは解釈しない。
  朝18分51秒と追加98分13秒は元の記録のまま保持し、遡って新journalへ作らない。
- 初日のC2/Pや同じUNKNOWNモデルを毎日最初から反復しない。停滞・停止条件は日付でリセットしない。

## 実装と保存先

- 現行スケジュール: [DAILY_RESEARCH_SCHEDULE.md](DAILY_RESEARCH_SCHEDULE.md)
- アプリへ反映したprompt本文: [DAILY_RESEARCH_AUTOMATION_PROMPT.md](DAILY_RESEARCH_AUTOMATION_PROMPT.md)
- 次のカード: [H-20261023-01](HYPOTHESIS_CARD_2026-10-23_C1_DEPTH.md)
- 実時計journal: `scripts/research_session.py`、出力`docs/data/daily_research/YYYY-MM-DD.json`
- 回帰: `scripts/test_research_session.py`、`make test-tools`からCIの既存targetにも含まれる。
- 設定読み戻し・ログ: [daily_research_setup_20261022](data/daily_research_setup_20261022/)

startで返るsession tokenを保持し、各unit/phaseと5分程度の確認点でcheckpointする。
中断時はrecoverで最後の未確認部分をgapとして閉じ、新しいstartを実時刻から記録する。
CPU profilerやアプリが実行しなくても働くworkerではないため、担当が確認した区間であることも記す。

## 検証と運用条件

アプリの更新結果とautomation.tomlの読み戻しで、同じID・chat・時刻・ACTIVEを確認した。
promptの本文一致を検査し、期限付きの旧研究予約2件もPAUSEDのままであることを確認した。
時刻境界・中断・二重計上・未作成状態の12件、brief7件、gate18件の計37件が通過。
make brief、研究registry384行、14リンク、git diff --checkも通過した。
未知補題や一つの方法の停止だけで一日を終了しないことを、最終promptにも明記した。
Leanと保護対象を変更せず、数学的証拠labelも変えない。stage/commit/pushなし。

[公式Scheduled tasks](https://learn.chatgpt.com/docs/automations#schedule-a-task-inside-a-chat)を参照した。
同じchatの文脈で継続するheartbeatを使い、ローカルrepoには実行時にMacとアプリが起動していることが必要。
アプリ停止・スリープ・利用上限の解消や、将来の連続120分の達成を設定のみで確認したとはしない。
翌朝のjournalとDAILYに、実際の開始/終了・確認済み実績・不足理由を残して効果を評価する。
