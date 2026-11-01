# Hypothesis card: context消去の予算条件は外せるか

- ID: H-20261025-05
- Status: REFUTED
- Parent: R-20261025-01、H03/E-402。DAG検証中の独立な局所探索。

## 一問・量化子

ある固定Nat Cを選べば、任意Bool語u/vでmass(v)+suffixCeiling(u)≤−Cなら、
任意未来語xに対してlocalSupply((u++v)++x)=localSupply(v++x)が成立するか。
E-402の明示残りA予算を、現在の任意に深い負mass bufferで置き換えられるという強い補助案。
親C1/Qや実軌道についての命題ではない。

## 提案と反証pass

u=S、v=S^m、x=A^(2m+2) S^mを攻撃族にする。
全語はS^(m+1) A^(2m+2) S^mで、E-393から供給あり。
消去後はS^m A^(2m+2) S^mで、必要な先頭Sが1不足して供給なし。
m0ではSAA対AA、m1ではSSAAAAS対SAAAASを紙上境界対照。
任意のCにm=Cを代入すればbufferは−Cでも未来で破れる。
新CPU探索なし。追加の強化チェックとしてE402の境界0を1へ緩めると破れる小最小suffixを、実行前に別protocolを固定して探す。

## 受入・停止・配分

一様な反例族と全Cのno-goをLeanで示せれば強い補助案をREFUTEDとする。
単にE402を繰り返すwrapperは数えない。親C1への反例と混同しない。
最大15分、修理は一回まで。全DAGの計算時間とこのunitを親cycleへ二重計上しない。
次は実S数とsuffix最大massを使う、より短いseparatorの供給条件へ。

## 判定

E-405。全Cの一様反例族と閾値1の具体反例を個別Leanで確認。有限発見/holdoutと証明を区別し、親C1を反証しない。CPU探索0.118秒（cap5内）。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
