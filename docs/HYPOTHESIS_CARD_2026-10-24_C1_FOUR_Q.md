# Hypothesis card: r4の全長Qをkernelへ

ID H-20261024-02。親R-20261024-01 / H-20261024-01。Status CONJECTURED（既存入力E-388はCOMPUTED）。
C1活用の残り枠を使う。子の時間/CPUを親に二重計上しない。

## 一問と全量化子

任意符号語f、padded BlockWord prefix終端n、その後の正不足、qで不足1、
z=[n,q)の元0基点非Endable A≤4、y=[q,b)の元0基点非Endable A≤1、Fb≤Fnの下で、
任意長z/yについてZ=Ar(n,b-n)+(b-n)*(Fn-Fb+1)≥0と全t<nのP2(t,b)不在を証明できるか。
完成設定からのprefix供給には短い区間の帰納仮定だけを使い、H/Q自体を仮定しない。

## chain・反証・受入・停止

r4の16終端分類と深さ4を当日のkernel証明から供給し、
全yが深さ4内なら既存COMPUTED719状態をkernelへ移す。外ならE-379のfresh-lowを使う。
深さを仮定したまま最終Qを解決扱いにしない。分類やQ graphが未検証なら親もCONJECTUREDのまま。
既知Az<0、q=n空域、b=q、最終A予算の[b,b+1)差、元p基点と途中nの違いを監査する。
受入は実際の全P2・任意futureを量化した最終Lean statementと逐語audit、または全仮定を満たす反例。
同じ旧計算の再実行や既存Qを仮定したwrapperなら停止。r4 kernelが間に合わなければ未完と記録する。
探索CPUは新規追加なし。前日のq4-certificate/独立版を保存hashとともに検証入力へ使う。

## 入力不足による切替

H01の全r4分類kernelが未完了のため、このカードのa_z≤4による無条件適用は保留。
H-20261024-04で明示16rootを仮定した将来Qを独立に検証する。
有限root入力を供給済みと見せず、親のa_z≤4はCONJECTURED/既存E-388 COMPUTEDのまま。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **0.000秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
