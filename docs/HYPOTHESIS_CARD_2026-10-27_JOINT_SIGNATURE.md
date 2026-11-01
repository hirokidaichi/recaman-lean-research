# Hypothesis card: 全mass共通old signatureのexact小商

- ID: H-20261027-10
- Status: COMPUTED（R5/7/11閉集合）、STOPPED（R19の小商方式）
- Parent: R-20261027-01/E422/E423。Mode: 局所探索、06:58開始、15分継続gate。初期CPU0、実行は別protocol固定後のみ。

E423で実future A20と必要old mass<=19/old半径47を導出した。任意BlockWordの全suffixから(mass,area)で1<=mass<=Rだけを保存した同じ集合をstateとし、全atom A/SAAA/SSAAAASAAA追加で正確に更新できるか。全massを同じprefixで同時保存し、自由old tagや各mass別代表にしない。
exact更新は新atom内suffix集合と、旧pair(r,a)→(r+mass v,a+len(v)r+area v)の和。各full atom massは正なので、旧r>Rから将来r<=Rへ戻らない。語長/areaを勝手に切らない。R<=4の既知代表初期評価を再実行せず、R5/7/11/19で初めてclosed state数を測る。各gate3000、超過時はそのR以降を止める。

紙上chain: area_append式、mass加法、suffix split、positive atom massから全長exact state更新。old窓のmass/area条件はstateに対する同時queryとなる。小商が供給されなければ大表/既存r4jobへ時間追加しない。旧N32 spectrum緩和とは新しい入力E422/423とexact共通prefix保存を区別する。
反証: trip内の複数suffixが同mass、同mass異areaも保持。mass0/負のsuffixはBlockWord suffix positiveで存在しない。R境界/empty prefix/長いholdouthistory、各tagを別prefixへ持上げない。
受入: 独立suffix replayとclosed automaton<=3000で初めてkernel candidate。計算のみならCOMPUTED、全長exact更新の証明は別にLeanが必要。上限超過/時間で方法STOPPED、追加予算/範囲は再開しない。
CPU契約は今日検証済みsingle cooperative Python/子process禁止だけ。費用/argv/source/discovery/holdoutはJOINT_SIGNATURE_PROTOCOL.jsonを実行前に正本とする。

06:58実worker discovery0.061239/holdout0.383701CPU秒、controller別。R5/7/11=22/68/647閉集合、R19は3001で停止（全state数ではない）、独立1600照合不一致0。最長BFS witness R11 30/R19部分50、holdout123〜369でdiscovery witnessと重ならない。R19追加予算なし。次H11で任意長exact update/実EndN保存をLeanへ移す。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-10/explore/joint-old-signature: 6分10.234秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
