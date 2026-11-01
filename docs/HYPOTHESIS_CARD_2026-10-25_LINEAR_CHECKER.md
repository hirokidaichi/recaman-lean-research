# Hypothesis card: 単一suffix scanによる同一macroの検査

- ID: H-20261025-07
- Status: PROVED-LEAN（一般checker同値）。全r4分類E-404はCONJECTURED、single-file方法はSTOPPED
- Parent: R-20261025-01、H04の同じr4分類証明。別の量化子や状態上限へ変更しない。
- Mode: C1活用/検証工学。最初15分でkernel同値と256node実測を判定。

## 一問と受入

任意Bool語wについて、長さ/mass/area/local供給を右からの一回scanで計算し、
既存localSupply/wordArea/mass/lengthと全語で等しいことをLeanで証明する。
同じgap/stepA/全macroの両tag、全childを保存したfastSuccessorsと既存successorsの等式を証明する。
巨大な値へ既存checkerを展開せず、まずこの一般等式で書き換えてから具体checkをkernelで行う。
判定の意味、A11、飽和S、old必要signature、実語adapter、16終端語は一切弱めない。
benchが改善した場合だけ、旧slow DAGを途中終了してsource/logを隔離し、同じ全graphのfast DAGへ置き換える。
同じ表への時間追加ではなく、計算規則を保存する新しい線形scanが再開根拠。

## 反証pass

空語、SAA（mass1/area0）、非供給AA、長いSの先頭/末尾、window始点t0/t=length−1、実endpoint Aは別という境界を紙上照合。
重みをlengthではなくlength−1にする誤実装ではSAAを落とすため拒否されなければ失格。
S19/20のfree AとA11を既存macroのまま対照にし、全j0..19/両tag/全childの等式をkernelで確認。
数値graphは旧の独立検算済み入力でfresh holdoutとは呼ばない。

## 費用・停止

新CPU探索0。Lean検証はsource/argv/dirty hashとbench90CPU/90wall/4GiBを実行前に固定する。
初期Checked未供給のreductionだけを分類の進展としない。
全DAG fast版のcapはbench実測後に固定し、遅い旧jobと二重実績加算しない。
同値が破れるかbench改善なしならSTOPPED。数学的修理は一回まで。07:45/08:00を守る。

## 07:38の意味監査

全scan/macro等式は個別Lean/lint成功。256node同条件で72.52→31.24wall秒。
slow全jobは966.515wall秒で自分のgroupのみ停止し、linear版全jobも新しい証明済みpruningへの置換で1208.844wall秒で停止。
いずれも初期Checkedは未供給。線形scanの一般等式とr4分類の最終結果を別記し、同じ全jobへの時間追加を再開条件にしない。
数学source/log/argv/hashをpacketへ保存。最終分類はH10とE-404の結果を参照。

## 最終全体check

final-check-2.logでactive409 library/412build jobs/2811公理宣言が成功。一般等式は監査済みのhelperで、初期Checkedのない分類reductionや証明数を独立したC1進展に数えない。数学sourceは検証時の凍結hashを保持。

## 当日journal確定実績
親cycle R-20261025-01: 06:01:21.862027〜07:59:10.380882、確認済み117分48.519秒、不足2分11.481秒。
このcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。
