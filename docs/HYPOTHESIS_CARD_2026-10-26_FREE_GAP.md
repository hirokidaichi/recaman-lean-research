# Hypothesis card: 実供給gapを非供給A数で評価する

- ID: H-20261026-01
- Status: CONJECTURED
- Parent: R-20261026-01（新しい日次cycle）。E-407、2026-10-25 DAILY。
- Mode: C1活用15分gate、失敗時はkey-return/multi-runの別機構へ。

## 一問と全量化子

任意 f : Nat → Bool、n,a,b,j : Nat、BlockWord β に対し、
seg f 0 n = β ++ A^a、元0基点の不足 d(n)=0、n<b、
∀u, n<u≤b+j → d(u)≥1、[b,b+j)は全S、EndN f 0 (b+j) とする。
d(u)=cN(S) 0 u−cN(EndN f 0) 0 u（整数差）、
r=cN(fun t => f t=true ∧ ¬EndN f 0 t) n (b−n) は同じ元0基点の実非供給A数。
語長・総A・r・jに上限を置かず、j+1≤r が成立するか。
p基点Int版はf(i)=e(p+i)による同じ問い。実EndNの代わりに自由tagや必要oldSignatureだけを置かない。

## 紙上chainと未知edge

E-407は2j+2≤先行全Aを供給する。全Aは供給Aも含み、rとは異なる。
目標はpositive deficit/元基点zero/真の供給履歴からrを評価する独立edge。
全A≤2r、指数rank、今回の結論を定義したPropを仮定して埋めない。
成立しても一般rank、任意rの終端分類、一般Q/C1/H/SLの証明には追加chainが必要。

## 反証pass・既知の境界

空語/最初のfree、j=0、同じprefixのlocal/old重複、長S、直前freeで攻撃する。
既知portfolioのprefix SAAA、tail S^4 A^4 S A はfree2/全A5/不足2を実現する。
最後のgap j=1でr=2なので、強い j+2≤r は破れるが本問は等号。この既知例を新しい反例や独立holdoutと呼ばない。
実供給ledgerは実EndNで再照合し、修理rankや自由tagモデルの停止を迂回しない。

## 受入・継続・停止

最初15分で、新しいkey/count不等式・実prefixまで持ち上げた反例・候補集合の削減のどれかを得る。
受入は上記全量化子の紙上chainと最弱edge、または具体f/prefix/全EndN ledger付き反例。
単なるwrapper、範囲の延長、結論の仮定化ならこの方法をSTOPPEDにし、残り45分を
key-return分解25分と最後のfree後のmulti-run十分条件供給20分へ移す。一日全体は終えない。
数学的な修理は一回まで。補助命題の反例と親C1/Qの反例を区別する。

## 費用・証拠

CPU探索は当初0。必要なら実行前にargv/費用上限/dirty source hash/独立holdoutを固定して研究から再配分。
10/25 guardのRLIMIT_CPUはprocess単位でgroup累積を強制しない。新CPU許可前にgroup計測/累積停止の仕組みを検証し、未計測CPUを見積りで実測扱いにしない。
既存r≤4 graphはdiscoveryのみでfresh holdoutではない。単なるr/長さ上限の延長は再開しない。
2026-10-25の全表single-file法はRSS4GiBで停止。時間/メモリ追加だけで再開しない。
翌日は最新DAILYの最終kernel結果を先に確認し、完了済みr3/r4部分や低mass代表入力を再実行しない。
予定setup10/活用60/探索30/監査10/handoff10分、実績は翌日の実時計journalのみ。
新しいedgeが得られたため10/25終了時の連続無変化は0（成果による更新で日付resetではない）。

## 2026-10-26開始

実setup06:02:22.120877、研究gate開始は当日journal参照。初回15分で独立入力または実history反例を要求し、CPU探索は0のまま紙上反証から始める。予定の不足は遡及補填しない。

## 06:14前の判定・再配分

命題はCONJECTURED。直接free countを供給する方法はSTOPPED（独立edge未供給）。
固定した新しい二run-family actual-history反証はdiscovery5000組（positive4376/supplied gaps2343）、
独立holdout405組（positive405/supplied4）で違反0。有限COMPUTEDで、一般証明や探索延長の根拠としない。
予算0から実行前にworker CPU20秒/各10秒、wall各15秒+controller予備2CPUへ再配分し、実worker0.342841秒。
先にguard契約をnormal/fork/exec/wall kill/thread CPU killで検証（1.121683CPU秒）。一般process-tree累積の解決とは呼ばず、
子processを禁止したcooperative single-Python workerに限る。wait4で成功/失敗/killを正確計測。
既知S4A3のsuffixAAAはmass3/free2で、全suffix最大mass<=freeという補助案を破る。元free-gap命題の反例ではない。
最初15分以内で早期切替し、残り45分を新key-return25分（H02のA-run平方signature）とmulti-run供給20分へ移す。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
