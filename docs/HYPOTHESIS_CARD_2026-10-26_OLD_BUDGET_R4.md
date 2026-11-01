# Hypothesis card: 全mass old-only一回/A-run予算によるr4候補削減

- ID: H-20261026-06
- Status: COMPUTED（候補削減0）。証明書化方法STOPPED
- Parent: R-20261026-01、E411/E390/E404。新証明済み同時old制約を追加する局所探索。

## 一問と全量化子

元r4 A-event緩和（S-gap min(j,19)、全A0/A1、free<=4、正不足、A11も保持）に
oldSpent boolを追加する。実tailの全S>=3の同じA-run内で、localSupply=falseの供給Aは
元prefixからのold-only供給を必要とし、E411より高々1つ。local=trueのAはcreditを消費させず上から緩和し、
Sを一つ以上挟めばboolをfalseへ戻す。free Aでも同じA-runならcreditを保持する。
S<3は従来緩和を保ち、S19飽和時のfalse Aや第11Aを切らない。
これで旧12837状態/40024辺からどの候補/path/edgeが減るか。

## 受入と停止

独立なreverse-moment全graph照合、旧graphへの射影包含、実history/既知E395 five-supply/長gap対照を要求。
actual-to-credit-modelの全simulationは別の未知edgeで、数値closureだけをr4/C1証明としない。
全長/全childの新kernel実行は **新状態数<=3000かつsimulation/closed benchmark改善** の時だけ別protocolで検討する。
状態数が大きければこの証明書化方法をSTOPPED、候補削減はCOMPUTEDに留める。同じcapの時間追加はしない。
探索はsingle-worker exactCPU、各15CPU/20wall、全体30CPU+controller予備2CPU、state100000guard。
修理一回まで。7:45以降新数学なし、8:00終了。新edge/削減があるときだけ次へ進む。

## 判定（07:12 JST）

新graph12837状態/40024辺、射影も12837/40024、除去0状態/0辺、16終端語不変。
独立reverse DFSで全state/edge一致、784未使用長gap対照、既知4prefixの実free4/最後5供給を保持。
第11AとS19後free Aを遷移定義で切っていない。worker CPU1.511537秒、controller別、上限30内。
事前kernel gate状態<=3000を満たさず、同方式をkernelへ投入する方法をSTOPPED。古い表の再実行なし。
有限データはCOMPUTED、actual-to-credit simulation/全初期kernelは未供給、r4/C1は未証明。
新一般E411の数学は保持するが、r4有限候補が減ったと書かない。再開は別の独立数学的除去または実測の小さい商。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
