# Hypothesis card: 同じ基点のrun chargeを供給する

- ID: H-20261027-03
- Status: PROVED-LEAN（E-417）
- Parent: R-20261027-01 / E416、H02有限probe STOPPED。Mode: 活用（共通prefix供給位置の入力）、最初15分gate。

任意BlockWord全実prefix w後のSh AMで、実元0/pのA-run内free数r1に対しM<=2r1が成立するか。
任意二A-run Sh AM Sm ALで全relative positive不足なら全A<=2実free+1が成立するか。元zero/全positive不足からのIntp接続を保つ。
語長/run長/free数上限は入力にしない。後者はE414のgapに消費されたcountを独立に使える形へ取り出すもので、既存二runfree-gapを再証明して別成果と数えない。

紙上chain: 第一A-run内の最初二Aは供給不可。i>=1ではE407のj0が供給前A数i>=2を要求し、i0はno_window_after_S_run。全供給<=2（E413の既存count）と最初二freeから第一charge<=0。
二run全供給<=5（E416のtwo_run_supply_of_positive）、r>=4ならE-r<=1、r<=3なら既存positive_r3_additions_free_bound。数学的未知入力は第一二Aの実供給不可能性とcount接着だけ。

反証: M0/1/2/3/4、h0、old/localの同clock重複、known SAAA|S4A4がM4/free2の等号。弱化自由tagは除外する。新CPU探索0。
受入: 実EndN/元基点のcount不等式、既存free+2予算とは異なる入力、G5/Audit/lint/check。Intp adapterだけを独立成果に数えない。
15分で新しい実供給位置/count edgeなしならSTOPPED、命題CONJECTUREDのまま三runの共有窓の別モデルへ。修理1回まで。

## 06:17受入

E-417 PROVED-LEAN。第一runの最初二Aを実EndNから排除し、M<=2実freeを語長非依存で供給。二runの全A<=2free+1もnext targetなしで消費可能にした。全体check417jobs/2862公理宣言・G5成功。
数学的修理0、cNの1+1と2をそろえるtactic補修のみ。第一run入力は新しい供給位置制約、二run部分の既存count合成やInt adapterを別解決に数えない。第三charge<=2は未証明。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-03/exploit/first-two-free-charge: 3分01.206秒、H-20261027-03/audit/charge-statements: 2分51.642秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
