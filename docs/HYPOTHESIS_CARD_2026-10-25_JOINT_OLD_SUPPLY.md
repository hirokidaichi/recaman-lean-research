# Hypothesis card: 固定joint-prefixを使うr4モデルの候補削減

- ID: H-20261025-01
- Status: COMPUTED
- Owner: Codex（提案・反証・形式化・監査は別pass）
- Parent: C1/Q、E-390/E-394/E-398/E-399、R-20261024-01の継続
- Mode: C1活用、最初15分gate。完了した実low-mass EndN同値/r3/深さ/C2/Pを再証明しない。

## 一問・全量化子

E-399は既に任意padded BlockWord prefixについて同じr∈jointOldRootsを全clockで共有し、
必要mass Rb=1+Fn−Fbが3/4なら、実old窓の存在/実endpoint A付きEndNを双方向に供給した。
このrを各runの初期に一つ固定したA-event r4モデルは、従来12837状態の独立old-signatureモデルから
どの状態/path/tagを除けるか。全root合計・各root最大・rootを忘れた状態射影・endpoint集合を別々に測る。

S<19の正確な語でRb∈{3,4}なら、E-399のlocal-or-exact-oldを使いtrue/false両tagを正確化する。
他のRbは従来必要oldSignatureとfalseの!localに留める。S=19の飽和状態では実語全体のmassが
trim語のmassと異なるので、この低mass分岐をtrim語から計算しない。E-385/E-390でold供給なしと
local trimのsoundnessを使い、長gap後の非供給Aと第11A停止線を必ず残す。
同じrをclockごとに選び直さず、全長A≤10を仮定して第11Aを除外しない。

## 反証・受入・切替

対照: root空語/AAA/ASAAAA/trip（mass4 area9/13併存）、E-395の実5供給連鎖、
j0/18/19/20、S飽和後のnonsupplied A、A11。実historyのタグと必要条件モデルのタグを混同しない。
新graphの全closure、同じモデルをreverse mass/momentで独立照合し、旧モデルへの包含と
具体な候補削減を記録する。実prefix4語は既知対照でfresh holdoutとは呼ばない。
新しい未使用長gap holdoutは実行前protocolで固定（以前の20/37/257/4097だけを再使用しない）。
既知E-395の4prefix ASAAA/AASAAA/SAAASAAA/SSAAAASAAAは、それぞれ同名の候補代表を持つ。
各々が同じ5供給tailを許すことを対照にし、root名だけで実EndN tagを置き換えない。

最初15分gateの合格はactual transitionを落とさない接続と新候補の除去、または明確な反例。
有限結果はCOMPUTED、kernel未検査の分類をPROVED-LEANへしない。
定義だけ/同じ集合/同じ資源障害ならこのモデル改善方法をSTOPPEDとし、残り45分を
run-family multi-run分解25分と小finite certificate20分へ再配分する。一unitの終了で一日を終えない。

## 費用・監査

予定setup10/C1活用60/局所探索30/別pass監査10/handoff10分。実績は当日journalのみ、親子二重計上なし。
CPU探索当初0。実行前にsource/dirty revision/argv、全体CPU・wall、各job上限、state guard、
discovery/独立checker/未使用holdoutをfresh protocolへ固定して研究枠から再配分する。
新しいquotientの資源削減を測らず大規模r4表の時間/メモリ上限だけを増やさない。
同じ障害でedge/集合が2cycle変わらなければ40/50/10へ、探索25分以上は別機構へ。
2026-10-24終了の連続無変化0は新edgeによる更新で日付resetではない。一般C1/az≥5は未解決。

## 2026-10-25 実行前固定

06:02:53 JSTに研究unit開始。最初15分gateは06:17:53まで。CPU0から親140 CPU秒/140 wall秒へ変更し、活用枠の最大3分を計算・監視へ再配分。各job70 CPU秒/65 wall秒、各root150000状態guard。source/dirty Lean hash・argv・独立reverse checker・未使用gap23/41/263/4103のholdoutを[data protocol](data/joint_old_20261025/PROTOCOL.json)へ実行前に凍結。全A上限で第11Aを切らずwitnessとして停止。新graphが旧graphの部分集合であることと具体な候補除去を受入にし、計算のみを証明へ昇格しない。

## 判定（06:06 JST）

全10rootのclosureが完了し、逆moment DFSで全state/edge/16終端語が一致。未使用長gap対照5200件、既知E-395の4実prefix/5供給、飽和後free A、第11Aを落とさない境界対照が通った。
root合計128149状態、各root最大12828。rootを忘れた射影は12837→12836状態、40024→40023辺。削除はSSSSSSSSAAASAAAASA（A8/S10/free4）とそこへ供給される1辺だけ。全rootの16終端語は不変。
最初15分gateは具体削減1件により通過。ただし証明書圧縮としては各root最大9状態減、合計は約10倍であり、同方式を大表kernelへ投入する方法はSTOPPED。量化された低mass接続は既証明E-399、全graphの結果はCOMPUTEDのみ。一般r4分類/C1へ昇格しない。
探索2jobはtimeログから約14.5 CPU秒/14.5wall秒、上限140内。現在の実績はjournalの確認区間だけ。再開は新しい共有/商または独立な記号的pruningで、同じ10rootの表を再計算しない。
次は任意prefixのmass障壁でlocal窓を切る入力と、長S後のmulti-run継続を扱うH-20261025-02へ。残り活用枠はこの別機構へ移し、監査10分を保持する。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
