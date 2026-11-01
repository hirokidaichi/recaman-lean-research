# Hypothesis card: A-only未来の供給を過去の定符号runで払う

- ID: H-20261026-04
- Status: PROVED-LEAN
- Parent: R-20261026-01、E408/E409。新しい独立count入力へ活用25分。

## 全量化子と一問

任意有限run列rs : List (Bool × Nat)、w=concat(rep n b for (b,n) in rs)、任意K : Nat。
長さ0のrunも許し、連続同符号のrunをまとめる必要もない（上界は選んだrun列の長さ）。
A-only未来のK個の位置でlocalSupply(w A^i)がtrueとなる個数はrs.length以下か。
全元0/p実history prefix=wで以後K個が全Aなら、
K ≤ 実際の追加非供給A個数 + rs.length を導けるか。長さ/K/free個数の上限なし。
自由tagや任意root存在Propを仮定しない。元pを維持して全old/local開始を含む。

## 紙上chainと最弱edge

E408のj0:供給clock iには同じsuffix vのP(v)=-2,mass(v)+i=1が必要十分。
P(A^k v)=P(v)+4k*S(v)、P(S^k v)=P(v)-4k*S(v)-2k²。
各定符号run内のsuffix始点はP=-2を高々1つしか持たない。
Aの場合S(v)=0ならP(v)>=0でrootなし、S(v)>0ならstrict。Sの場合k>=1でstrict。
同じprefix runに属する二つの供給clockは同じsuffixしか使えず、mass式から同じclockになる。
古い最初のrunで供給される候補と残りprefixからの候補へ分け、countの和集合上界をrun列で帰納する。
最弱新edgeはcountがrun数で抑えられる点で、key式の同値だけを成果にしない。
同じ過去runを別の未来A-runでも再利用できるので、全履歴の一回限り課金/一般rankとは主張しない。

## 反証・受入・停止

空prefix/全A/全S、zero長run、重複run、K0、元基点以外のlocal-only誤rebasingを攻撃。
全S prefixとB>=2のA^(B+1)では供給は第3Aだけ、free BでK=B+1となるsharp対照。
一般word countと実元0/p接続、free partitionをLeanで確認しG5/Audit/checkで受入。
25分でunique-root/countの独立edgeが供給できなければ、未供給箇所を保存し別候補監査へ切替。
数学的修理1回、CPU探索は実行前にfreeze/独立holdout/正確wait4。親子CPU二重計上なし。
7:45以降新数学なし、8:00終了。C1/free-gap/r4初期kernel全体は別の未解決義務。

## 判定

E-410。6663ではなくdiscovery6643組/holdout640組、sharp9対照で違反0。一般word countと実元0/Int元pのfree予算がLean/lint/全体check415jobs/2831宣言で検証。数学修理なし。A-only条件を外した混合futureでは新しいSが新たな供給を作るため、このrun課金を全体rankへ昇格しない。人間レビュー未。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
