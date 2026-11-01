# Hypothesis card: 長い最終S separatorをC1候補から排除する

- ID: H-20261027-05
- Status: PROVED-LEAN（E-419）
- Parent: R-20261027-01/E418/E416。Mode: 活用（実pruning接着）、最初15分gate、CPU探索0。

任意BlockWord全実prefix後の任意u S^m A^T、全A予算ones u+T<=B、B>=1、m>=2B-1とする。
最後にS^jの次の実供給Aがあるなら、T=2(j+1)かつj+1<=最後A-run内の元基点実free数を全長で供給できるか。
zero/positive不足を追加仮定しない。対象は実EndNで、old/localの両始点を保持し、基点切断はE418の証明済み同値でのみ使う。

紙上chain: E418で元EndNをseparator開始へ移すとpure S^m A^T S^jのE393 exact分類を使える。A-run内の供給clockはi=2のみ（i0も分類で排除）、全供給<=1。実partition T=供給+freeよりfree>=T-1=2j+1>=j+1。
反証: T0/j0、B1、u空、endpoint S、known T2clockはtargetであって先行供給数に含めない。E405無予算反例を再開せずBを残す。
受入は実元0/p free-gapとE416残余A20への適用（最終S>=39の反例不可）。必要なA20は反例残余から供給し、勝手に仮定しない。
15分で実free数へ接着できなければSTOPPED/未解決箇所を保存、次は第二S separatorの切断とpositive不足の供給へ。修理1回まで。

## 06:31受入

E-419 PROVED-LEAN。最後A-runの実供給<=1、実targetからT=2(j+1)、最後runの元free>=2j+1を供給。E416のactual A20を導いて長separatorへ適用し、三run反例の最後S s<39を得た。全体check418jobs/2872公理宣言/G5成功。数学修理0、Nat長/assocのtactic修正のみ。
0630途中保存は実時計06:31:28（遅れ1分28秒、timestamp正本）。新規run/終了なし。次は第二Sの切断後二runと相対positive不足の供給。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-05/exploit/long-final-S-free-gap: 3分34.451秒、H-20261027-05/audit/last-S-pruning: 1分44.359秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
