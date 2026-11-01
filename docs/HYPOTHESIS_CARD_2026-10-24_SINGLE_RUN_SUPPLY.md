# Hypothesis card: 三run局所窓の完全式と長いS後の次の供給A

ID H-20261024-08。Parent R-20261024-01 / E-393。Status PROVED-LEAN。
Mode 局所探索、最初15分。最後のfree後を2段に制限する案は反証されたので、
single A-run状態の次の供給gapを記号的に一意化できるかを問う。新探索CPU0。

## 一問・全量化子

任意m,r,j≥0について、localSupply(S^m A^r S^j)が真であることは
r=2(j+1)かつm≥j+1と同値か。
任意のpadded BlockWord prefix後、r≥1,m≥2r−1で同じ実tailがあり、次clockが実Aなら、
元0基点Endableであることはr=2(j+1)と同値か。全パラメータ・未来gapの上限なし。

## chain・反証pass・受入

既存の当日three_runs_window_middleでP2の全A数r=2(j+1)、mass1から先行S数j+1。
全suffixをleading S内とA-run以後で分け、後者は単峰の面積>0で排除する。
逆方向は実suffix S^(j+1) A^(2j+2) S^jを構成する。
長いSならold windowはE-385で排除し、上のlocal式がactual EndNを決める。

m0/r2/j0、m1/r2/j0、odd r、境界m=j+1を反証passで固定。
長いS仮定を外すr3/m4/prefix SAAAはold窓を持つためactual iffの反例。
次clockのA条件を省くと窓があってもEndableでないので、その仮定を必ず残す。
受入は双方向のLean証明と実word suffixの供給。数値範囲検査だけなら不受理。
15分で新しい双方向edgeがなければ停止し、本日の意味監査へ移る。

## 形式化後の別pass判断（実時計07:12 JST以降）

E-393拡張。three_runs_window_iff/localSupply_three_runs_iff/endable_after_manyS_A_iffの両方向を確認。408jobs/2768decl全体検査成功。長いS/endpoint A条件を保ち、一般rankを主張しない。

実績正本は `docs/data/daily_research/2026-10-24.json`。親R-20261024-01へ包含し二重計上しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **352.924秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
