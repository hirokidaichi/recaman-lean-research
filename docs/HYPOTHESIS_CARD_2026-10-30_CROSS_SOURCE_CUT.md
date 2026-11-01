# 混合sourceの交差量を保持するcut

- ID H-20261030-04 / R-20261030-01/H07、Status PROVED-LEAN（E460; 最終467jobs/3059decl PASS）。
- Question: 任意非空BlockWord old u/任意混合b,v/全i,T,j、j>=2,i<T,T<=i+j、同じold/local二P2窓で、bにA-before-S対が一つ以上あれば、K=i+j-Tとしてones(b)>=j+1+K+1を導けるか。
- 原始counterpartはcross(b)=runKey(b)+2*cntF(b)^2>=4。これは符号語から計算する量でありfree結論ではない。全source/prefixと他old massは保持。受入は同じraw窓からの無限語長proofとactual同基点adapter、または反例。free/rank/C1とは呼ばない。
- Dependency chain: mass二窓からmass(u b)=K、S_b=C+A_b-K。key二窓の差から 2(A_b-K)^2=2(j+1)^2+runKey(u)+2C^2+cross(b)+4K*S_v-2。BlockWord key>=-2とC>=1でstrict squareを得る。負A_b-Kの場合はS_b>=0による(C境界)と矛盾。
- Falsifier: cross0を許すと既知E453のb=S6 A5/R5/K0で+1は偽。K0/任意大Kを別扱いし、source以前のfreeに置換しない。弱化historyの負keyは既知E455で排除条件の必要性を確認。四run最終S源ではE457の+2総Aと一部同じ情報なので、同枝の二重進展に数えない。全mixed sourceへのstrict cutとしてのみ評価。
- 停止: 最初15分で正しい平方差/strict candidate条件が出なければSTOP。CPU探索追加0。紙上chainの後Leanを既定10CPU/512MB/20wallで検証。単なる既存A-cutの代入だけなら独立成果にしない。

06:40:43: raw/core and actual same-base AS adapter passed512MB/10CPU cap. One ordinary argument-name fix List.length_drop n→i; hypotheses unchanged. Lint5/5 substantive. Actual AS givescross>=4 internally, no new defined-goal hypothesis.
