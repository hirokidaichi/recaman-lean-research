# Hypothesis card: 三A-runの実供給予算と残余free4〜9

- ID: H-20261027-01
- Status: PROVED-LEAN（E-416、2026-10-27。一般三run free-gap/C1は未証明）
- Parent: R-20261027-01予定。前cycle R-20261026-01終了時連続無変化0（E-414など新edgeによる更新、日付resetではない）。
- Mode: C1活用60分の最初15分gate。CPU探索予算0。

## 一回の問い・正確な全量化子

最初のbounded unitは、E-416の紙上chainのうち**三A-run実供給count<=11と反例残余4<=r<=9/A<=20/j<=9を元0の全長Leanへ移せるか**。
任意f:Nat→Bool、n,h,M,m,L,s,T,j:Nat、BlockWord w。seg f0n=w、以後実tail Sh AM Sm AL Ss AT、長さB>0。
同じ元0でd(n)=0、全n<u<=n+B+jでd(u)>=1（cN S-cN EndNの整数差）。続くSj後のAはEndN f0(n+B+j)。
r=cN(fun x=>f x=true∧¬EndN f0x)nB、A=cN(fun x=>f x=true)nB、E=cN(EndN f0)nB。
一つもrun長/総長/free数の上限を**入力**にしない。結論はE<=11と、j+1>rなら4<=r<=9、A<=20、j<=9。Int元p adapterも用意する。
relative positive版を部品にする場合は、元zero/positiveから実cN加法で供給し、元p/0のEndableを途中基点へ交換しない。

## 紙上chain・最弱edge

前二A-runのS>=3ならE414で実供給<=5、S<=2ならpositive不足から<=1（空tailは0）。次S-runは供給0。
第三A-runの前のlocal tailは5個の定符号runなのでE410のgeneric run予算<=5。共通BlockWord oldはS>=3ならE411で<=1。
合計供給<=11。総S<=2の枝は全positive不足から全供給<=1、E407で直接free-gap。
free<=3はpositive_r3_free_gap、free>=10はA<=free+11<=2free+1とE407。残余だけを得る。
最弱の未知edgeはこの実count接着のLeanと、残余における**次供給条件と同じsource再利用の制限**。

## 反証と停止済み経路

E415: 第三A-rayのlocal<=2と一回修理<=3はREFUTED。四clock例はS10 A24 S21 A3 S4の2/3/9/11でLean確認。さらに空BlockWord/元0/全正不足の実履歴としてliteral監査済みCOMPUTED。親free-gap/C1/Qの反例ではない。
全prefix A<=2r+1は既知A10/r4 terminalで偽。『次供給可能なら』という補助候補はCONJECTUREDで、本unitの入力にしない。
E412: old-only budget付きr4の削減0/0、12837states/40024edges。kernel gate不通過、同じ表への時間/メモリ追加なし。
過去のr3分類/Q、二runfree-gap、実old接続を再証明しない。新しいr3 count射影は既存定理として使うだけ。

## 受入・継続・切替

15分で実元0の三run供給countまたは反例残余の新しいkernel入力が閉じれば継続。G5/Audit/lint/check後にだけPROVED-LEANへ。
全長のsource/cN接着が閉じずwrapper/結論仮定/同じ検査の再実行だけなら、この形式化unitをSTOPPEDとして、残り45分を
**残余r4〜9で次供給条件からsource再利用を制限する新不等式25分**と、**局所窓/old窓の共通prefix十分条件の別pass20分**へ切替える。
既に得たA<=20/j<=9を単なる大きい有限probeの根拠にしない。必要な探索は事前の新しいpruning、費用上限/argv/dirty hash/discoveryと独立holdout、process管理を固定してから。
数値範囲だけの拡大、r4未完了jobへの時間追加、local定数の追加修理はしない。数学修理は一回まで。
予定setup10/活用60/探索30/audit10/handoff10分。実績は新しい当日journalだけ、前cycle/CPUを二重加算しない。

実績精度: 活用/探索の切替もcheckpointでunit名にmodeを明示し、混合unitの秒数を後から推定分割しない。検証超過は研究枠から差し引く。

## 2026-10-27開始・反証pass

実setup開始06:01:46.075185、session9b9ab67f-4cfe-4465-aa39-e3cd4b1ee012、R-20261027-01。初期dirty sourceとrevisionをthree_run_20261027/START.jsonへ固定。CPU探索0。
ゼロrun/空B2、総S2/3境界、r3/4/9/10、j0を紙上攻撃。B>0を保持し、B2=0では供給0。
既知四clock例は第三A-run内供給4（合計11を破らない）。既知A10/r4 terminalは次供給条件を持たずfree-gapの反例にならない。
弱化history負例: (S^m A^m)^3で各A-run先頭だけfree、残りを自由Endable tagとすると、全不足は正、free3、供給3(m-1)>11（m>=5）。真のEndNが必須で、自由tagモデルを新しい研究経路として再開しない。
紙上chainは前二run供給5/第三generic5run+old1、local/old重複は和集合上界。各源をrunを越えて一度しか使えないとは仮定しない。新規moduleはThreeRunSupplyBudget、既存四moduleを再証明/編集しない。

## 06:08 gate判定

初回research06:03:20から15分以内に元0実供給11/残余4〜9をkernel入力として供給し、Int元pと実zero/positive adapterまで成功。全体check417jobs/2857公理宣言、G1〜G5/保護label成功。数学的修理0、最初のLean/adapterとも一回で成功。CPU探索0。
E416の証拠強度を紙上からLeanへ更新した仕事で、同じ主張を新しい別数学成果として二重計上しない。残余排除は未供給のまま。次unit H-20261027-02の実履歴surplus/次供給の共有制約へ継続する。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-01/exploit/three-run-gluing: 3分10.368秒、H-20261027-01/audit/G5-and-full-check: 1分49.491秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
