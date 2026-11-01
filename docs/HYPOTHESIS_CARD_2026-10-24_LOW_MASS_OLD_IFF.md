# Hypothesis card: 固定低mass代表と実old窓の双方向

ID H-20261024-13。Parent R-20261024-01/E-399。Status PROVED-LEAN。
Mode C1活用、最終接続監査からの一問。遅い開始のため07:45で数学作業を止める（約2分半上限）。CPU探索0。

任意f/padded BlockWord prefix終端nについて、同じr∈jointOldRootsを全b>nで共用する。
必要mass Rb=1+Fw(n)−Fw(b)∈{3,4}なら、実old窓∃t<n Win(t,b−t)があることは、
∃v suffix r, mass(v)=Rb, area(v)=−Ar(n,b−n)−(b−n)Rbと同値か。
実endpoint AはWinの存在と分離し、EndNを結論にする時には別途要求する。

前方向は実old suffixとarea split、逆方向はrが実prefix suffixであることからvを実時刻n−|v|へ戻す。
mass3/4は非空性を供給する。元の基点0を保持し、全clockの外に同じrを量化する。
空prefix/空代表、tripの9/13併存、b=n境界（対象外）、面積の符号を攻撃する。
受入は上の同値の全長Lean証明。07:45までに閉じなければSTOPPED、未証明sourceをactiveから除く。

## 07:45以降の監査判定

E-399を拡張。low_mass_old_window_iffと実endpoint A付きlow_mass_endable_iffは07:44:09までに個別Lean成功。
全体408jobs/2782宣言の公理監査も成功。同じrが全bに先行する。逆方向も実prefixのsuffixから実時刻を構成する。
これによりmass3/4に限りfalse tagの除外も正当化できる。他mass/S飽和後の扱いは次modelで別途監査する。
7:45以降は新規数学sourceを変更せず、検証/記録へ。親と時間二重計上しない。

## 最終実績（closed journal）

<!-- DAILY_CARD_ACTUAL_START -->
このカードに属するresearch区間は **108.405秒**。共通setup/監査/handoffは親cycleでのみ計上。
closed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds=7178.944。
<!-- DAILY_CARD_ACTUAL_END -->
