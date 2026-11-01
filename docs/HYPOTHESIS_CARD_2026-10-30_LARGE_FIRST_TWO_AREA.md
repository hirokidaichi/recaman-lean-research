# 最初二runが大きい枝のold area

- ID H-20261030-06 / R-20261030-01/H10、Status PROVED-LEAN（E462; 最終467jobs/3059decl PASS）。
- Same H01 quantified raw/actual domain plus M+L>=R=j+1. Question: short last ray T<=j+2と同じold mass/areaから全A>=2R+3を導けるか。最終S源は短lastを内部供給し、他old mass/prefixに上限を置かない。
- Chain: I=M(m+s+v)+L(s+v)+Uv >=H+2M+L、T<=R+1、ML>=R⇒I>=A。E457でA>=2R+2。等号ならC>=2はC²+2I<=2A+1と矛盾、C1はBlockWord mass1⇒u=Aと同じarea identityの奇偶に矛盾。free-prefix結論への定数修理ではなく符号交差と同一old sourceからの必要条件。
- Falsifier: raw sharp family u=AAA,h6,M1,m=r,L=r+1,s1,U2,v1,T=r+3,j=r+1（r>=1）でA=2R+3/ML=Rを確認し、無条件+4は要求しない。raw sharp controlは標準orbit/全positive/free-gap反例ではない。ML<RのE457 +2 sharpは残す。
- Acceptance: same source all-length proof/actual adapter plus sharp raw control、あるいは反例。15分でstrict candidate削減がなければSTOP。数学CPU探索0追加、Lean既定cap。成功後もfree/全射性を証明したとは呼ばない。

06:55:55: raw/actual/source boundary個別Lean成功。大きいgrindの探索は止め、同じ数式をC²<=1の小比較に分けて既定cap内検証、仮定を弱めていない。境界族は全rでP2/全A+3のみ、実zero/positive/free-gapを付加していない。
