# Hypothesis card: 任意前置語のA-run供給を負の平方signatureで制限する

- ID: H-20261026-02
- Status: PROVED-LEAN
- Parent: R-20261026-01、E407。H01の直接free上界方法からkey-returnへ切替。
- Mode: 局所探索25分（06:14前後〜）。新しい全長供給位置制約がなければmulti-run十分条件へ。

## 一問・全量化子

任意Bool語u、r,j : Nat（0も含む）、P(v)=2areaW(v)−mass(v)(mass(v)+1)について、
localSupply(u A^r S^j) iff
∃ t<length(u), mass(u.drop t)+r=j+1 ∧ P(u.drop t)=−2(j+1)^2 か。
さらに供給されるなら j+1≤cntF(u) かつ r≤2cntF(u) を語長/r/jに依らず導き、
元0からの実EndN/実endpoint Aと全prefixへ接続する。
BlockWord/不足/free個数を仮定せず、実prefixを丸ごとuに含める。old/localを途中でrebasingしない。

## 紙上chain・未知edge

PはA appendで不変、Q=2area+mass(mass−1)=P+2mass²はS appendで不変。
E407の全local S-gap root式でu A^rのsuffixを切り、A-run内から始まるsuffixはQ=2A²>0で除く。
供給rootにはP=-2R²、mass+r=R=j+1が必要十分。
固定S個数の面積下界からP(v)>=−2cntF(v)^2、従ってR≤cntF(v)≤cntF(u)。
mass(v)>=−cntF(v)よりr≤2cntF(u)。u=S^h,r=2h,j=h−1で等号（h≥1）。
最弱の新edgeは全r/jと全始点のroot同値。単なる定義/同値wrapperを成果とせず、
r,j上界と同じsuffixの平方signature制約まで供給する。C1のfree上界やrankは別の未知edge。

## 反証passと受入・停止

空u、r0/r1、j0、全Aのu、u=S^h、純run三段の既知E393、非BlockWord前置語で攻撃。
r/jのoff-by-oneと窓始点がu内かA-run内かを独立に確認。
受入は双方向root式とsharp上界の一般Lean/実EndN/元基点接続/Audit/G5/check。
同値だけ/算術だけ/仮定の結論化ならSTOPPED。数学的修理1回まで。
CPU探索は新規protocolでfreeze後だけsingle-worker契約下で行い、発見/未使用holdoutを分離。
親cycle時間と同時検証CPUは二重計上しない。7:45新数学停止、8:00終了。

## 判定（06:21 JST）

E-408。発見12495組/独立holdout1920組、空語/r0/j0/非BlockWord/等号族h1,2,5,11,23で違反0。
一般root同値・先行S数上界・実元0/Int元p adapterが個別Lean/lintを通り、全体check413jobs/2819公理依存が成功。
G5にadapter/既知等号族の派生性を明示し、独立の定理数へ増幅しない。人間レビュー未。
数学的修理なし。初期tactic失敗（rwの対象/依存Bool case/append結合/不足namespace）は全log/source保存。
全Sは元historyのrun開始以前のSであり、tail free数ではない。一般C1/free-gap/r4初期証明は未供給。
予定25分のうち約7分+監査で新edgeを得たため、残りをmulti-run平方因子分解の評価へ移す。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
