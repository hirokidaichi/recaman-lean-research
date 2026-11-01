# Hypothesis card: 共通suffix集合のexact更新と有限certificate

- ID: H-20261027-11
- Status: PROVED-LEAN（E-425の全長exact更新/実future保存）、STOPPED（有限kernel候補方式）
- Parent: R-20261027-01/H10。Mode: 局所探索、07:02開始、15分gate、追加CPU探索0。

任意BlockWord w、任意R、全suffixの正mass<=Rとareaを同じリスト集合に保持する。BlockWord atom vの追加では、旧pair(r,a)を(r+mass v,a+len(v)r+area v)へ移し、新v内suffixを加えるexact membership同値が任意長で成り立つか。
旧mass>Rはvのmass>0から戻らず、旧負massはBlockWord suffix positivityで存在しない。listの順番/重複を数学的stateにしない。
H10のR7=68/R11=647閉集合をcandidateに、全BlockWordのliteral suffix queryを同じ代表へ移せるか。R19は3001gate STOPPEDを維持して拡張しない。
受入は全長actual suffix membership同値と、もし可能なら定数表の全child照合を通常Lean decideで検査し、実wへの帰納simulationまで供給。table checkerだけや新Prop仮定は不受理。G5/Audit/lint/check。
反証: empty word/empty atom/R0/重複pair/同mass異area、trip途中負massをatom境界で切る必要、長いhistory123〜369符号の独立holdout1600照合一致を使用。
有限kernel候補はR7が1CPU秒相当以下で成功したときのみR11へ進む。各新checkはper-process15CPU/30wall/1GiB AS（tree累積capではない）、1回の修理は命題変更を伴う場合だけ。資源gate失敗は同job時間追加で再開しない。

07:04:33 generic append/table simulationの直接Lean成功。候補checkは1GiB ASをmacOSがpreexecで拒否し開始できず、事前gateに従い有限kernel方式STOPPED。R7/R11とも未検査、capを外してrootに入れない。R11sourceはpacketへ退避。失敗childのCPU未計測は0扱いしない。generic exact更新と実EndN query接続は別の有用unitとして継続する。

07:10 check423jobs/2899宣言成功、G5/lint/Audit確認。数学命題の修理0、純計算式の恒等式を明示してgrind/neg_mul表記を修正。定数表のverified仮定を持つgeneric helperは本成果のunconditional主張から除外し、有限表はCOMPUTEDのまま。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-11/explore/exact-spectrum-transfer: 5分12.084秒、H-20261027-11/audit/spectrum-transfer: 2分06.434秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
