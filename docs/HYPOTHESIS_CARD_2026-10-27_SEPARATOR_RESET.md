# Hypothesis card: 明示A予算つき長S separatorで実履歴を切る

- ID: H-20261027-04
- Status: PROVED-LEAN（E-418）
- Parent: R-20261027-01 / E402/E407/E416。Mode: 局所探索（別機構の数学的pruning）、最初15分gate。

## 正確な一問

任意f:Nat→Bool、n,a,m,B:Nat、任意Bool語u,x、BlockWord β。
seg f0n=β A^a、seg f n (|u|+m+|x|)=u S^m x、1<=B、ones u+ones x<=B、m>=2B-1とする。
endpoint b=n+|u|+m+|x|の実EndNについて、EndN f0b iff EndN f(n+|u|)bが語長/x長無制限で成立するか。
これは基点交換を仮定するのではなく**同値を証明**する課題。xのS個数/総長に上限を入れない。元Int p版も供給する。

## 紙上chain・反証

old t<nならE407で用いたold_window_count_barrierのS_total<=2A_total-2がm>=2B-1に反する。
n<=t<n+|u|はmass(S^m x)+ones u<=0からlocalSupply_erase_prefixで消える。残る窓はseparator開始以後で両方向に保存。
B0は除外、m=2B-1境界、空u/x、Sを任意長含むx、endpointがSなら両辺false、local/old重複を攻撃。
無予算future erasureはE405 REFUTEDであり再開しない。本問は明示budget Bを入力に残すE402型の別の実EndN接続で、有限A<=20を勝手に仮定しない。

## 受入・停止

受入は上記全長の実EndN双方向・Int元pの同値とG5/Audit/check。新しいS cutoffをC1残余から供給するのは後続unit。
CPU探索0、紙上とLean検証のみ。15分でold/local両窓を保持できなければSTOPPEDとして不足edgeを記録、次は残余の共同窓条件を監査。数学修理1回。

## 06:25受入

E-418 PROVED-LEAN。endpoint/全future prefixの元0⇔separator開始の実EndN同値、全future供給/free count一致、Int元pの同値を供給。G5/全体check418jobs/2867公理宣言成功。
B予算を保持し、未来S/総長無制限。既知old count sharp族によりthreshold2B-2ではglobalと切断後が不一致（既存族の境界対照で新C1反例と数えない）。数学的修理0、take長の型補修のみ。
次はH05で長い最終S-gapを持つ三run候補の排除へ接着し、E416残余B20のS39を使う。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-04/explore/budgeted-actual-separator-reset: 3分46.853秒、H-20261027-04/audit/reset-equivalence: 4分10.369秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
