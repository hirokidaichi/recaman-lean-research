# Hypothesis card: 三run残余の最後一つ前A-runからtarget窓を排除

- ID: H-20261027-14
- Status: PROVED-LEAN（E-428）
- Parent: R-20261027-01/E416/E427。Mode: 別機構の局所探索、07:20開始、15分gate、CPU探索0。

r4表への新しい同mass幅4入力は削減0/0でSTOPPED。次は共同old表ではなく、target窓のrun形からの平方因子条件を調べる。小定数local<=2/<=3の修理を再開しない。

任意d,s,T,j:Nat、1<=d、d+T<=20、4<=j<=9で、具体窓A^d S^s A^T S^jがmass1/area0にはならないか。sは無制限、d/T/jの有限性はE416の実反例A20、r>=4かつr<j+1、j<=9から供給する。
紙上chain: mass式からs=d+T-j-1、runKey/area式からd^2=T(T-2(j+1))。d/T<=20とj4..9の有限平方条件を通常Lean decideで検査し、実seg/Winへ接着。三run中の最後一つ前A-run内からtargetへ届く局所窓だけを排除する。first A/三つのS/old源は残す。
反証: A4 S9 A8 S2とA3 S8 A9 S3はj下限外のP2、A8 S18 A16 S5はA24で予算外のP2。これらを保持して仮定の必要性を確認。d0（S開始に変わる）を除外、T0/emptyrun/endpoint符号/半開窓を監査する。
受入: all-length square identity、有限small-budget排除、actual Win源排除とoutside-budget controlsをLean/G5/Audit/check。有限Nat不等式だけのmoduleは不受理。
新規bounded検証はper-process10CPU/20wallとLean -M512（Lean自身のallocation cap、OS AS/tree全体capではない）。資源上限/15分gate失敗ならpacketへ退避しSTOPPED、時間/メモリ追加しない。数学修理1回まで。

07:19の直接21×21×10 checkerはLean512MBで資源STOPPED。sourceをpacketへ保存。独立した因子分解でx=T-R-d、y=T-R+d、xy=R²、x+y偶数、R<yかつR+y<=20へ縮約し、30組だけのdivisor/parity判定へproof方法を一回修理する。数学主張は同一、CPU/wall/Memoryは追加しない。別の修理/資源追加はしない。

07:24全体check425jobs/2909宣言成功、G5/lint/Audit確認。4410tuple checkerの資源停止後、因子divisor/parityへ一回変更して同512MB/10CPU/20wall内成功。数学主張変更0、二回目の修理なし。実E416反例から必要全boundsを供給し第二A内sourceを排除。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-14/explore/target-square-factor: 4分15.963秒、H-20261027-14/audit/target-square-factor: 1分17.426秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
