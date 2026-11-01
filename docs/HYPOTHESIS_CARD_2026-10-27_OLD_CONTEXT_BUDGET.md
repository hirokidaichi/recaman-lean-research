# Hypothesis card: 全A予算からold履歴の必要半径を導く

- ID: H-20261027-08
- Status: PROVED-LEAN（E-422）
- Parent: R-20261027-01/E416/E421。Mode: 活用、06:50開始、15分gate、CPU探索0。

任意f、padded BlockWord全prefix境界n、未来endpoint b>=n、ones(seg f n (b-n))<=B、B>=1。
実old窓t<nなら2(n-t)<=5(B-1)を導き、元0/pの実EndNをq=n-floor(5(B-1)/2)以後の開始だけで双方向保存できるか。
任意future wordの全prefix/実供給とfree count/relative positiveを同じqで保存し、qへのclock移動後のBlockWord prefix長をfloor(5(B-1)/2)以下にする。B20では47。depthやQ/rankを入力にしない。

紙上chain: E407前段のold_window_count_barrierでS<=2A-2。窓mass1よりBlockWord suffix mass R=S-A+1<=A-1<=B-1。既存suffix density 2len<=5Rを合成。b=nはBlockWord末端がEndableでない既存補題で処理。窓の全開始を保持し、実EndN同値を先に証明してからcountを移す。
反証pass: B1ならold窓なし、n<47はq0で何も切らない、b=n/endpoint S/空future、local開始t>=n、q境界、長いSを含むfuture。自由old tagや初期depth仮定は導入しない。
受入: 全長窓半径/同じqの実EndN iff/count保存、G5/Audit/lint/check。定義wrapperだけは不受理。
15分でactual iffに届かなければSTOPPED。有限半径だけで三run/C1排除とは呼ばず、大表の時間追加へ戻らない。修理1回まで。

06:53全体check421jobs/2892宣言成功、G5/lint/Audit済み。実窓半径と固定qの全count/relative positive移送を受理。数学修理0（Leanのdsimp進捗エラーのみ修正）。次H09のactual有限代表接着へ。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-08/exploit/old-context-radius: 2分28.397秒、H-20261027-08/audit/old-context-radius: 1分44.100秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
