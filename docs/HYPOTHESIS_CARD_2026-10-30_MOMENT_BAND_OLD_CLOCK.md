# 任意zero-mass headのmoment帯とold早期clock

- ID H-20261030-11 / R-20261030-01/H22、Status PROVED-LEAN（E465）。
- One question: 任意List Bool z、mass(z)=0、S=cntF(z)、area(z)=-B、4S+6<=B<=6S+4、任意BlockWord old prefix w/全v>=1/全iで、実old-source profile tailOldRay w (z Sv) iならi>=4か。固定seedだけへの単純代入を越えて、すべてのzero-mass mixed headへ供給できる必要条件を求める。
- Chain: source suffix uのC=v+1-i、key(u)=2B-2+2v²-4C(S+v)。C1/2の既知BlockWord key<=0と下限B>=4S+6によりC>=3。i<=3とx=v-i>=2ならkey>=-2は0<=B+i²-2i-x²-2x(S+1)-2Sを要求し、i²<=3i/x²>=4/x>=2/B<=6S+4に矛盾。全source/全長、free/結論/新Prop仮定なし。
- Falsifier/boundaries: 上端+1のS7/B47ではz=S6 A S A6、old=S A4（mass3/key-2）、v5/i3のrawP2が可能。下端-1のS5/B25ではz=S5 A5、old=AA、v2/i1のrawP2が可能。どちらもmoment帯の厳密さを攻撃するraw対照で、C1/実orbit反例にしない。
- Acceptance: 同じsourceの全量化子のproofと境界対照、または反例。07:45を絶対停止、追加CPU探索なし。成功してもlocal供給halfや全四runchargeは別義務、moment帯から自由tag/全history erasureを導かない。

07:39:55 full check467jobs/3059decl PASS。任意z/全v/i actualWin coreと両端raw sharpnessを登録。localのfree/rankは結論していない。
