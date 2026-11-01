# Hypothesis card: BlockWord prefixのold供給clockの一意性

- ID: H-20261026-05
- Status: PROVED-LEAN
- Parent: R-20261026-01、E408/E410とE381。C1活用へ戻るための新しい独立入力。
- Mode: 最初15分で反例またはprefix不等式を供給。clockの一意性と始点の一意性を混同しない。

## 一問・全量化子

任意BlockWord β、a,h,K : Nat、u=β A^a、n=length(u)、実seg f 0 n=u、
[n,n+h)全S、[n+h,n+h+K)全Aとする。元0基点の実old P2始点t<nを持つ
供給Aのclock数は高々1か。同じclockで複数始点を持つ場合は一つと数える。
目標を得られた場合は、local S^h A-run供給は第3AだけであるE393と合わせ、
全供給A<=2、従ってK<=実追加非供給A数+2を供給する。全prefix長/a/h/K上限なし。
一般C1/混合future/任意rankやr4全分類とは別の入力。

## 紙上chain・未知edge

old suffix v of uはBlockWordでmassρ>=1、P(v)>=-2。
S^h後のA-only供給clock iには P(v)+4hρ−2h²=-2、i=h+1−ρ。
同じuの二つのnested suffixから得るこの式が同じhで成立したとき、ρが等しいことを示す。
異なる始点が同じmass/areaを持つ例ASSAは既にあり得るので、始点単射を要求しない。
補助候補: BlockWordの任意prefix wにはP(w)>=-8、mass(w)<0ならP(w)<=0。
h>=3なら二nested suffixのmass差が正/負のどちらでも同じclock条件を満たせず、mass差0だけ残る。
h0/1/2はP>=-2とmass1 suffixの分類からold供給なしを先に確認する。
補助候補の反例ならこの方法を止め、親C1と区別して保存する。数学的修理は一回まで。

## 反証・受入・停止

βのfree/aas/tripleの接着、zero separator、同massの重複始点、SSAAA prefixのP=-8境界、
既知SAAA|S4 A4（local第3/old第4）を攻撃する。
CPUは新count機構の有限grammar族にのみ使い、r4全表/長さ上限を延長しない。
実行前protocol/argv/dirty source hash/発見と独立holdout、single-worker正確wait4を固定。
受入は一般old clock一意性と元0/p実count/free budget（または正確な反例）。
15分で独立edgeなしなら残り研究枠を既存の新定理の意味監査/別ray評価へ再配分。
7:45新数学停止、8:00終了、親cycle費用の二重計上なし。

## 06:59時点の継続根拠

有限発見6171/独立holdout384組に異なるold clockの反例なし（同clockの重複始点12件は保持）。
新しい一般prefix不等式P>=-8/負mass=>P<=0と、純S separator後のold clock一意性が個別Lean成功。
一般tail vを挟む場合もold keyの差に同じ式が現れるため、まず「tail中のS>=3」に限定して
全massの同時old clock一意性へ接続する（smallS<=2は別の有限mass領域）。
これは窓単位の独立old tagを同じprefixで同時に選ばない新edgeであり、同じ古い表の時間追加ではない。

## 一般化した受入（反例による修理ではない）

wは任意BlockWord、vは任意の後続tailでcntF(v)>=3、i/jはA-only未来clock。
old source t<|w|のrootはmass(w.drop t)+mass(v)+i=1 と
P(w.drop t)+P(v)+4mass(w.drop t)*cntF(v)=-2 を同じtで満たす。
同じw/vでこのrootを持つi,jは等しいこと、全ray供給count<=local(v ray count)+1を示す。
実全prefixがw、実後続tailがvのまま原基点EndNへ接続し、任意のfree予算をinputにせず
A-only長K<=実追加free+1+vの定符号run列長を供給する。
元のS-only separator h<3の枝は既に別に排除しており、この一般化でsmallS<=2を切った一般C1解決とは主張しない。
最弱edgeはP/質量のnested-suffix比較による全massの同時clock制約。新たな独立discovery/holdoutはOLD_TAIL_PROTOCOL.json。

## 判定（07:10 JST）

E-411。全prefix不等式/全mass profileの質量一意性/old clock一意性と、実f/Win（localも同時にあるold窓も含む）への接続をLean証明。
一般tail S>=3、word count予算と元0/Int元pのfree+1+tail run数予算まで全体check416jobs/2840公理監査/G5成功。
純S-only版h0/1/2も排除済み。一般tailのS<=2領域は別条件として未使用、黙って全Sへ外さない。
新たな全mass同時制約を使う候補削減をH06で測る。一般C1/rank/r4分類は未証明。人間レビュー未。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
