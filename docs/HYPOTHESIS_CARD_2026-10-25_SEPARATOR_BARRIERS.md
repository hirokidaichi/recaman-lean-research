# Hypothesis card: 実S数とsuffix最大massを分けるseparator条件

- ID: H-20261025-06
- Status: PROVED-LEAN
- Parent: R-20261025-01、H02/E-401、H03/E-402。全DAG検証と独立な記号的multi-run入力。
- Mode: 局所探索/活用。最大25分で実EndN/任意futureへの接続を判定、進まなければ停止して監査へ再配分。

## 一問・全量化子

任意padded BlockWord実prefix、任意語u、r≥1、Nat m/jについてK=suffixCeiling(u)、M=ones(u)、S=|u|−Mと置く。
m≥K+rかつS+m≥2(M+r)−1なら、実tail u S^m A^r S^jと実endpoint AでEndN iff r=2(j+1)か。
さらにr=2k,k≥1の場合、
m≥K+2k、m≥K+k+2、S+m≥2(M+2k)−1、S+m+(k−1)≥2(M+2k+1)−1
の4条件だけから、u S^m A^(2k)後で追加非Endable A0なら任意future長K'の追加全A≤1か。
M/S/KはInt、run/clockはNatとしてcastを明示。uの形/長さ/深さ、k/m/K'の上限なし。

## 依存chainと反証pass

local切断はE402の具体suffix ceiling。old切断は実総Sと全AのE385個数障壁。
最初の供給gapはk−1。次はevenFollowWordでlocalなし、4番目の条件がoldも排除する。
最初のAへの強帰納で任意futureを覆う。元0のEndN/free countを保持。
u空ならE397より緩い十分閾値（k2でm8、k≥3でm≥4k−1）を得る。
u=S^h A^M,h≥M+2,m≥M+3,k1なら4条件を供給でき、E401のm≥2M+5より短い。
既知E395のS5 A3 S4 A2はm4が質量条件とold条件を満たさず5供給対照を切らない。
境界k1/2/3、u空、uにSを増やす場合、自由なold tagに弱めたときの供給を紙上攻撃してから形式化。
新規CPU探索は当初0。必要な有限例はsource/protocolを先に固定し、単なるr上限増加にしない。

## 受入と停止

全rの実EndN同値、4条件からの全future追加A≤1、具体な無制限二run族の条件供給をLean/Audit/G5/全体checkで検証。
run形を任意tailが持つと仮定せず、一般r4/C1/rankを解決扱いにしない。修理は数学1回まで。
全DAGの監視とこのunitを親実績へ二重加算しない。監査/引継ぎ・7:45/8:00制限を守る。

## 判定

E-406。全r実供給同値/4条件の任意future追加A<=1/無制限二run族を個別Leanで確認。new lint21/22 substantive。全体checkと別pass意味監査はDAG完了後にまとめて実行。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
