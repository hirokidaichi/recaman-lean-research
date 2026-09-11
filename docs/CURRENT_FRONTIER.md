# Current research frontier

最終更新: 2026-09-11

この文書を、研究状態と次の研究gateに関する唯一の正本とする。個々の主張の証拠は
[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv)、Lean kernel上の公理依存は
[`Recaman/Audit.lean`](../Recaman/Audit.lean)を正本とする。

## 結論

2026-09-11の[等号境界エポック](EXTREMAL_CAPACITY_EPOCH_2026-09-11.md)では、容量不等式 `|U|≤|D|`（E-070）を
広げるのではなく**等号が立つ場所を測った**。判明したことは三つある。

第一に、`|U|≤|D|` は**全周期で sharp**（E-176）。各周期に等号を達成する正符号和語が存在し、
等号を達成する最大 `|D|` は周期20で6まで増える。S希薄語だけの現象ではない。

第二に、**等号語の最小供給窓はすべて ssCount≤1**（E-177）。周期8..31で、tightかつ高SS窓を持つ語は0。
つまり **E-070の等号側は E-128 の既証明クラスの内側にある**。E-070に残っているのは狭義不等式だけになった。

第三に、**等号語では課金が強制される**（E-178）。各供給Aを自分の最小窓内のSへ送る二部グラフの完全マッチングは、
周期8..22の tight語 336件すべてで**一意**であり、強制辺1,110本はすべて E-069 の oldest-S 先と一致する。
oldest-S は一般には `REFUTED` だが、**等号が立つところでは唯一可能な課金**である。
これで名前付きchargeが全滅してきた理由が確定した：selectorは効く場所では既に決まっており、
外れる場所（slackのある語）では外れても損がない。**selector探索は終了**とする。

その強化案は反証した。`slack ≥ c`（c = |U| − oldest-S像の大きさ）は周期18の `AAAASSAAAASAAASSSS`
（|U|=6, |D|=7, c=2, slack=1）と周期21で偽（E-180）。衝突を1件1Sで支払う会計は使えない。

代わりの目標は局所的で検査可能である：**高SS窓は自分の内部から削除可能なSを必ず供出する**（T6、E-179）。
高SS窓を持つ全語で、その語の全ての高SS窓が供出する（周期8..22、53,000語超、例外0）。
これが次のgateであり、Lean証明が消費すべき形である。

網羅範囲も広げた：周期31までの全正符号和語で `|U|≤|D|` 違反0、`U=A` 違反0、局所Hallマッチング飽和（E-175）。
従来はE-066がp≤16、E-081がp≤22、Hall gate H-20260907-09がp≤18だった。周期19..22の語数は
E-081の3,487,066と一致する（probe内で自動照合）。horizon延長だけではlabelを上げない規則は維持する。
tightブロック同士の接着による net 余剰も、全回転を含む対627,264件・三つ組6,751,269件（周期40まで）で0（E-182）。

Lean側では、この分枝の全探索が黙って依存していた停止則を定理にした（E-181、`PeriodicSupplyBound`）。
正の周期質量だけから後退部分和の drift 則 `g(l)=g(l-p)+σ` を導き、任意lagの供給探索を `d≤p(p+1)` の
有限検査へ落とす。「このphaseはどのlagでも供給されない」がkernel検査可能になった。
さらにWrap-vs-SS会計（E-183、`WrapSSBound`）により、P2 lag `d=qp+r` に対して `q·S ≤ ssCount + 2` を証明し、
走査上界を `d < (ssCount + 3)p` へシャープ化した。またSS=2端点剛性定理（E-184、`TwoSSEndpoint`）により、
SS=2窓同士およびSS=2と過去のSS≥1窓との端点共有をLeanで排除し、過去窓との端点共有はclean窓（`ssCount = 0`）に
限られること、および介在語の最小性阻害を証明した。さらに周期符号語上へ端点単射性を持ち上げ、
SS=2の端点相単射性・SS=1との非交差性・合同端点でのクリーン先行順序性、およびS端窓の合同容量
`|U2| ≤ |D|` と直和容量 `|U1| + |U2| ≤ |D|`（E-185、`TwoSSPeriodicSupply`）を証明した。
さらにSS=2窓を含む部分集合の近傍全容量性（E-186、`TwoSSTightDisjoint`）により、`p ≤ 11` かつ `|U| < |D|` でSS=2窓を含む任意部分集合 `A` の近傍が `N(A) = D` に達し `|A| < |N(A)|` へ狭義拡大すること、したがってtight部分集合（`|N(A)| = |A|`）はSS=2窓を含み得ないこと、および任意の減算 `s` を削除してもSS=2窓を含む成分でHall条件が自動的に保たれ、減算削除可能性の検査がSS=2窓を避ける部分集合へ完全に帰着されることを証明した。
さらにSS=2窓からの局所減算供出定理（E-187、`TwoSSLocalDonation`）により、S端SS=2窓はその最古減算相 `s*(u) = endpointPhase p u d ∈ D` を供出すること、窓自身および `u` を含む任意部分集合が `s*(u)` を被覆すること、`p ≤ 11` かつ正slackのもとで `s*(u)` の削除が `u` を含む全成分でHall条件を保存すること、相異なるSS=2窓の供出相が互いに単射であり、かつSS=1窓のマッチング像と交わらないことを証明した。
さらにtight部分集合回避とHall保存定理（E-188、`TwoSSAvoidTight`）により、減算 `s` の削除による近傍変化が `s ∉ N(A)` ではゼロ（`N(A) \ {s} = N(A)`）、`|A| < |N(A)|` では高々1減小に留まる二分法を確立し、減算削除可能性が `U \ {u_0}` のtight部分集合回避へ帰着されること、およびlag 3のAAS窓が被覆する減算はその端点相 `endpointPhase p u 3` のみであり、lag 3端点との非交差性からtight回避と大域Hall保存が直結することを証明した。
さらに一般周期大域wrap障害定理（E-189、`WrapObstruction`）により、任意周期 `p ≥ 1` に対し `lag ≥ p` の窓が減算全体 `D` を被覆することから正slack語ではtight部分集合（`|N(A)| = |A|`）がwrapping窓を含み得ず、全tight部分集合が非wrapping局所窓（`lag < p`）に局在すること、減算削除後のHall条件検査が非wrapping部分集合に完全に帰着されること、および `p ≤ 7` ではtight窓がlag 3のみ、`p ≤ 11` ではlag 3とlag 7のみに有限分類されることを証明した。
さらにtightボトルネック集合のサイズ下界定理（E-190、`TightBottleneckBound`）により、単一周期内 `i < j < p` の減算位置が相加合同で厳密に単射であることから非wrapping窓の減算が合同縮退せず、サイズ `k` のtight部分集合は `lag ≤ 2k + 1` の窓しか含み得ないこと、特にサイズ1（singleton）およびサイズ2のtight部分集合はlag ≥ 7の窓を含み得ず全構成要素がlag 3に限定されることを証明した。
さらに小語・小サイズtight成分でのSS=2局所供出完結定理（E-191、`TwoSSSmallCapacityClosure`）により、サイズ2以下のtight部分集合は個別近傍サイズ3以上の窓を含み得ないこと、および `p ≤ 11` かつ正slackのもとで非供出加算が供出相 `s*(u0)` を避けるlag 3 AAS窓を持つ場合、`s*(u0)` は `U` から大域的に削除可能であり、任意の加算部分リスト上でHall拡大条件が完全に保存されることをLeanで証明した。
さらに周期依存slack境界とp≤10でのSS=2供出完結定理（E-192、`TightComponentSlackBound`）により、正の符号和 `signSum > 0` から `2|D| < p` が導かれ `p ≤ 10` で `|D| ≤ 4`（`p ≤ 8` で `|D| ≤ 3`）となること、正slack語で供出加算 `u0` を避ける任意の部分リスト `A` が `|A| ≤ |D| - 2 ≤ 2`（`p ≤ 8` では `|A| ≤ 1`）を満たすこと、したがって `p ≤ 10` のtight部分集合回避においてlag ≥ 7の窓が完全に排除され全tight成分がlag 3 AAS窓に剛性化されること、および `p ≤ 10` の全語で最古減算 `s*(u0)` が普遍的に削除可能でありHall条件が大域保存されることをLeanで証明した。
さらに赤字容量によるtightボトルネックlagの普遍層化定理（E-193、`UniversalTightLagBound`）により、正slackを持つ任意の周期符号語において供出加算 `u0` を避ける任意の部分リストが `|A| ≤ |D| - 2` を満たし、tight部分集合の構成要素の個別減算数 `k` が `k ≤ |D| - 2` に上から抑えられること、したがって `|D| ≤ 4` では `k ≥ 3`（lag ≥ 7）が排除されて全tight窓がlag 3に限定され、`|D| ≤ 6` では `k ≥ 5`（lag ≥ 11）が排除され、一般にlag `4m - 1` の窓がtight成分に属するためには `|D| ≥ 2m + 1` かつ `lag ≤ 2|D| - 3` が必要であることをLeanで証明した。
さらにP2奇数減算パリティ剛性と普遍lag 3 AAS強制定理（E-194、`TightP2ParityRigidity`）により、長さ1および長さ5のP2語が存在しないこと、長さ3のP2語が一意に `[true, true, false]`（`AAS`）に決定されること、したがってlag `d ≤ 5` のP2窓は必然的に `d = 3` かつ `AAS` 窓であること、および `|D| ≤ 4` の正slack周期語においてSS=2供出加算を避けるtight部分集合の全構成要素が必然的にlag 3 AAS窓に強制されることをLeanで証明した。
さらにSS=2局所供出と普遍tight回避総合定理（E-195、`TwoSSTightAvoidanceTheorem`）により、正slackかつ `|D| ≤ 4` の周期語において供出加算 `u0` を避ける任意のtight部分集合が純粋にlag 3 AAS窓のみから構成され、その近傍がlag 3端点相の集合と厳密に一致すること、供出相 `s*(u0)` がこれら端点相を避けるならば `s*(u0)` の削除によってtight近傍が全く変化せずHall不等式が保存されること、および加算集合 `U` の任意の部分リスト上でHall拡大条件が大域的に保存されることをLeanで証明した。
さらにSS=2とAAS窓の衝突排除定理（E-196、`SS2AASCollisionObstruction`）により、同一端点を共有するclean lag 3 AAS窓と後続SS=2窓の時間離隔 `k` が必然的に `k ≥ 12` であること、任意ストリームにおいて `lag < 15` のSS=2窓がlag 3 AAS窓と端点を共有し得ないこと、周期語における合同端点相の衝突 `endpointPhase p t d = endpointPhase p u 3` が `d < 15` で完全に排除されること、および `lag u0 < 15` のSS=2供出窓の供出相 `s*(u0)` が `U` 内の全lag 3 AAS端点相と厳密に非交差であることをLeanで証明した。
さらにp≤11におけるSS=2供出容量完結定理（E-197、`ElevenSSDonationClosure`）により、正slackかつ正の符号和を持つ `p ≤ 11` の周期語において供出加算 `u0` を避ける任意の部分リストが `|A| ≤ 3` を満たすこと、`lag < 15` のSS=2窓供出相が `U` 内の全lag 3 AAS端点と自動的に非交差となることが定理として演繹され外部仮定が解消されること、したがって `p ≤ 11` の全周期語において最小lag 11を含む `lag < 15` のSS=2窓からの最古減算 `s*(u0)` が普遍的に削除可能であり任意の加算部分リスト上でHall条件が完全に保存されることをLeanで証明した。
さらに長さ7のP2語完全分類とtightボトルネック障害定理（E-198、`LagSevenTightObstruction`）により、長さ7のP2語が正確に4語のみに限定され各語が厳密に3個の減算を含むこと、サイズ2以下のtight部分集合は個別近傍サイズ3以上の窓（lag 7など）を含み得ないこと、および `p ≤ 11` の周期語において供出加算を避けるサイズ2以下の全tight成分でlag ≤ 5の窓が必然的にlag 3 AAS窓に強制されることをLeanで証明した。
さらにp≤11における高SS局所供出大統一定理（E-199、`UniversalTwoSSDonationTheorem`）により、正slackかつ `p ≤ 11` の周期語において供出加算を避ける任意部分リストが `|A| ≤ 3` を満たすこと、サイズ2以下のtight回避集合が純粋にlag 3 AAS窓のみからなる厳密な剛性を持つこと、`lag < 15` のSS=2供出相 `s*(u0)` が全lag 3 AAS端点と自動的に非交差となること、最小lag 11を含む全SS=2供出窓から供出減算 `s*(u0)` が普遍的に削除可能であり `U` の任意部分リスト上でHall拡大条件が完全に保存されることをLeanで証明した。
さらに減算削除可能性と厳密供給赤字定理（E-200、`SS2StrictSlackTheorem`）により、削除近傍 `N(A) \ {s}` が減算全体 `D` の真部分リストであることから任意の削除可能減算 `s ∈ D` が加算供給集合に対し狭義赤字上界 `|U| ≤ |D| - 1` を必然的に強制すること、したがって飽和供給 `|U| = |D|` ではいかなる減算も削除不可能であること、および全加算集合 `U` の削除後近傍が `|N(U) \ {s*(u0)}| ≤ |D| - 1` を満たしてHall不等式と整合することをLeanで証明した。
さらに低SSとSS=2の3層統合共同容量定理（E-201、`LowSSTwoSSJointCapacity`）により、低SS加算（clean AAS窓およびSS=1窓）の端点相と `lag < 15` のSS=2窓の端点相が合同端点相で完全に非交差となること、したがって低SS加算群 `U_{≤1}` とSS=2加算群 `U2` の直和容量上界 `|U_{≤1}| + |U2| ≤ |D|` が成立すること、および各SS=2窓が減算容量を1ずつ排他的に消費して低SS加算容量を `|U_{≤1}| ≤ |D| - |U2|` へ狭義抑止することをLeanで証明した。
さらにtightボトルネック集合のClean剛性定理（E-202、`TightSSZeroRigidity`）により、標準的lag 3 AAS窓 `[true, true, false]` が厳密に `ssCount = 0` であること、`|D| ≤ 4` の正slack周期語、あるいは `p ≤ 11` かつサイズ2以下の全tight回避集合において構成要素の `ssCount` が厳密にゼロに制限されること、したがって `ssCount ≥ 1` を持つ窓（SS=1窓およびSS=2などの高SS窓）はtightボトルネック部分集合に決して属し得ず、tight部分集合から構造的に完全排除されることをLeanで証明した。
さらに多重供出赤字と同時削除定理（E-203、`SS2MultiDonorDeficit`）により、相異なる2個の元を含むリストの長さが2以上であること、相異なる2個の減算を削除した減算プールが `|D| - 2` に狭義減少すること、相異なるSS=2供出窓が相異なる合同減算を供出すること、`lag < 15` の2個のSS=2供出相が任意のtight AAS近傍を同時に避けること、したがって2個の減算を同時に削除してもtight近傍が不変（`N(A) \ {s1, s2} = N(A)`）に保たれること、2個の減算の同時削除可能性が加算供給集合に対し二重赤字上界 `|U| ≤ |D| - 2` を必然的に強制すること、および赤字1以下の供給集合（`|U| ≥ |D| - 1`、すなわち全tight語および赤字1語）において `lag < 15` のSS=2供出窓が2個以上存在することは絶対に不可能であることをLeanで証明した。
さらに等号境界からの高SS排除と赤字普遍定理（E-204、`ExtremalSSExclusion`）により、飽和供給 `|U| = |D|` においていかなる減算も削除不可能であること、削除可能減算の存在が正のslack `|D| - |U| ≥ 1` を必然的に生じさせること、2個の同時削除可能減算の存在がslack `|D| - |U| ≥ 2` を強制すること、したがって供出減算が削除可能であるようなSS=2窓は飽和供給 `|U| = |D|` に決して存在し得ないこと、2個のSS=2供出窓を持つ語は赤字1語（`|D| - |U| ≤ 1`）になり得ないこと、および等号語（`|U| = |D|`）の全窓が必然的に `ssCount ≤ 1` を満たさねばならないという経験的発見（E-177）の厳密なLean形式化と証明を確立した。
さらに二重重みSS=2容量と赤字階層定理（E-205、`TwoSSWeightCapacity`）により、基本重み不等式 `n0 + 2*n2 ≤ nD` から供給赤字上界 `n0 + n2 ≤ nD - n2` および `n2 ≤ nD - (n0 + n2)` が必然的に従うこと、したがって飽和供給 `|U| = |D|` では `|U2| = 0`、赤字1語では `|U2| ≤ 1`、赤字2語では `|U2| ≤ 2`、一般に赤字 `k` の語では高SS窓の個数が高々 `k` 個に抑えられること（赤字階層則）、周期語において各SS=2窓が減算容量を2単位ずつ排他的に消費して全加算容量を抑止すること、および単一・二重SS=2供出窓によるslack拡大則（`slack ≥ 1`, `slack ≥ 2`）をLeanで証明した。
さらに高SS排除大統一還元定理とGate T6完結定理（E-206、`HighSSEliminationGrandTheorem`）により、低SS語で容量上界 `|U| ≤ |D|` が成り立ち高SS窓が狭義赤字 `|U| ≤ |D| - 1` を強制するならば全周期語で無条件に `|U| ≤ |D|` が成立するという大還元原理（Grand Reduction Principle）を形式化し、`p ≤ 11` の全周期語において最小lag 11を含む `lag < 15` の全SS=2窓が普遍的に削除可能減算を供出して狭義赤字 `|U| ≤ |D| - 1` を必然的に強制すること、飽和供給 `|U| = |D|` はSS=2供出窓を決して含み得ず全窓が低SS（`ssCount ≤ 1`）に純化されること、およびResearch Gate T6（高SS窓からの局所減算供出）がLeanカーネル上で完全に閉結・解決されたことを証明した。
さらにSS=2最小lag下界と長さ9のP2不可能性定理（E-207、`SS2MinimalLagBound`）により、任意P2語の長さが奇数（d % 2 = 1）に限られること、長さ9の全ビット語の網羅決定により長さ9のP2語が皆無であること、長さ7の最小P2語がユニークに2語に分類されいずれも ssCount ≤ 1 を満たすこと、したがって長さ7の最小P2語で ssCount = 2 となるものは存在しないこと、および任意の最小SS=2窓のlagが必然的に11以上（lag ≥ 11）に制限されるという幾何学的下界をLeanで証明した。
さらに最小SS=2窓のlag 11一意強制と長さ13のP2不可能性定理（E-208、`SS2LagElevenForcing`）により、長さ13の全ビット語の網羅決定により長さ13のP2語が皆無であること、したがって lag < 15 を満たす任意の最小SS=2窓のlagが厳密かつ一意に11に限定（lag = 11）されること、その供出減算相がユニークに endpointPhase p u 11 に固定されること、任意の最小SS=2窓が正確に6加算・5減算から構成され単一供出減算を除いてもなお内部に4個以上の減算余剰（surplus ≥ 4）を保持することをLeanで証明した。
さらに普遍的tight容量階層と減算数による窓排除定理（E-209、`TightCapacityHierarchy`）により、個別の近傍に k 個以上の減算を含む窓 u を含む任意のtight部分集合 A のサイズが必然的に k 以上（|A| ≥ k）でなければならないこと、したがってサイズが k 未満のtight部分集合は k 個以上の減算を持つ窓を決して含み得ないこと、供給加算数 |U| ≤ 5 の全周期供給において供出窓 u0 を避ける任意の部分リストのサイズが高々4（|A| ≤ 4）であり5個以上の減算を持つ窓（lag 11を含む全高SS窓）がtight回避部分集合から完全に排除されること、同様に |U| ≤ 4 で4個以上、|U| ≤ 3 で3個以上、|U| ≤ 2 で2個以上の減算を持つ窓がtight回避部分集合から厳密に排除されるという普遍的階層則をLeanで証明した。
さらにSS数による普遍的4層lag階層と高SS下界定理（E-210、`UniversalSSStratification`）により、長さ11の全P2語が ssCount ≤ 3 を満たすこと、lag ≤ 5 の任意最小P2窓が ssCount = 0（完全clean）であること、ssCount ≥ 1 を持つ任意最小P2窓のlagが7以上（lag ≥ 7）であること、ssCount ≥ 2 を持つ任意最小P2窓のlagが11以上（lag ≥ 11）であること、lag < 15 の全最小P2窓の ssCount が3以下（ssCount ≤ 3）に抑えられること、したがって ssCount ≥ 4 を持つ任意の超高SS窓のlagが必然的に15以上（lag ≥ 15）に達すること、および lag < 15 の窓に ssCount ≥ 4 が決して存在し得ないという普遍的4層階層則（lag ≥ 3, 7, 11, 15）をLeanで証明した。
さらに最小SS=3窓の完全分類とlag 11一意強制定理（E-211、`ThreeSSClassification`）により、長さ11の全ビット語の網羅決定により ssCount = 3 を満たす最小P2語がユニークに3語（w1=SSAAAAAASSS、w2=AAASSSSAAAS、w3=AAASSASSSAA）に完全分類されること、ssCount = 3 を持つ任意最小P2窓のlagが11以上（lag ≥ 11）であること、したがって lag < 15 の任意最小SS=3窓のlagが厳密かつ一意に11（lag = 11）に固定されること、任意の最小SS=3窓が正確に6加算・5減算から構成され内部余剰（surplus ≥ 4）を保持することをLeanで証明した。
さらに三重重みSS=3容量と赤字階層定理（E-212、`ThreeSSWeightCapacity`）により、基本三重重み不等式 `n0 + 2*n2 + 3*n3 ≤ nD` から供給赤字上界 `n0 + n2 + n3 ≤ nD - (n2 + 2*n3)` および `2*n3 ≤ nD - (n0 + n2 + n3)` が必然的に従うこと、したがって飽和供給 `|U| = |D|` では `|U2| = 0` かつ `|U3| = 0`、赤字1語（`|U| = |D| - 1`）ではSS=3窓が厳密に完全排除（`|U3| = 0`）され、赤字2語（`|U| = |D| - 2`）でも高々1個（`|U3| ≤ 1`）しか存在し得ないこと（3層赤字階層則）、周期語において各SS=3窓が減算容量を3単位ずつ排他的に消費して全加算容量を強力に抑止すること、およびSS=3供出窓によるslack拡大則（`slack ≥ 2`）をLeanで証明した。
さらに普遍的Mod-4パリティ剛性と離散量子窓長階層定理（E-213、`P2ModFourRigidity`）により、任意P2語の長さが厳密に `w.length % 4 = 3` を満たさねばならないこと、したがって剰余類 0, 1, 2 mod 4（偶数長すべて、および 1, 5, 9, 13, 17, 21 等の奇数長）のP2語が皆無であること、各区間 `(4k+3, 4k+7)` にP2窓長が絶対に存在しない普遍的離散ギャップ則、P2窓長が `d < 7` で必然的に 3（一意）、`d < 11` で 3 または 7、`d < 15` で 3, 7, または 11、`d < 19` で 3, 7, 11, または 15、`d < 23` で 3, 7, 11, 15, または 19 に厳密に制限される離散量子窓長階層則をLeanで証明した。
さらに4層容量還元とlag<15における純粋低SS極値構造定理（E-214、`FourTierCapacityReduction`）により、全供給窓数に対する普遍上界 `n_tot ≤ nD - (n2 + 2*n3)` を確立し、高SS窓の存在（`1 ≤ n2 + n3`）が狭義赤字 `n_tot ≤ nD - 1` を強制すること、SS=3窓が赤字2（`n_tot ≤ nD - 2`）を強制すること、二重SS=2窓が赤字2を強制すること、SS=2とSS=3の共存が赤字3（`n_tot ≤ nD - 3`）を強制すること、飽和極値供給 `|U| = |D|` が純粋に低SS窓のみから構成（`|U2| = 0 ∧ |U3| = 0` かつ `|U| = |U_{≤1}|`）されること、赤字1供給がSS=3窓を完全排除（`|U3| = 0`）しSS=2窓を高々1個に抑えること、赤字2供給でSS=3が存在する場合にSS=2が完全排除（`|U2| = 0`）されること、および `lag < 15` の全供給に対する大域容量不等式 `|U| ≤ |D|` が純粋に低SS供給（`ssCount ≤ 1`）へ完全に還元されるという大還元定理をLeanで証明した。
さらに普遍的SS層化第5層とssCount≥6に対するlag 19下界定理（E-215、`SSSixLagBound`）により、長さ15の全P2語の網羅決定により `ssCount ≤ 5` であること、したがって `lag < 19` を満たす任意のP2窓の `ssCount` が5以下（`ssCount ≤ 5`）に抑えられること、`ssCount ≥ 6` を持つ任意のP2窓のlagが必然的に19以上（`lag ≥ 19`）に制限されること、および `lag < 19` の窓に `ssCount ≥ 6` が絶対に存在し得ないという普遍的SS層化第5層則（lag ≥ 3, 7, 11, 15, 19）をLeanで証明した。
さらに最小SS=5窓の完全分類とlag 15一意強制定理（E-216、`FiveSSClassification`）により、長さ15の全ビット語の網羅決定により `ssCount = 5` を満たす最小P2語がユニークに5語（w15_1=SSSAAAAAAAASSSS, w15_2=AAAASSSSSSAAAAS, w15_3=ASSAAAAASSSSSAA, w15_4=AAAASSSSSAASSAA, w15_5=AAAASSSASSSSAAA）に完全分類されること、`ssCount = 5` を持つ任意最小P2窓のlagが15以上（`lag ≥ 15`）であること、したがって `lag < 19` の任意最小SS=5窓のlagが厳密かつ一意に15（`lag = 15`）に固定されること、任意の最小SS=5窓が正確に8加算・7減算から構成され内部余剰（surplus ≥ 6）を保持することをLeanで証明した。
さらに5層容量不等式とlag<19における赤字層化定理（E-217、`FiveSSWeightCapacity`）により、基本5重重み不等式 `n0 + 2*n2 + 3*n3 + 4*n4 + 5*n5 ≤ nD` から供給赤字上界 `n_tot ≤ nD - (n2 + 2*n3 + 3*n4 + 4*n5)` および `slack ≥ n2 + 2*n3 + 3*n4 + 4*n5` が必然的に従うこと、したがって飽和供給 `|U| = |D|` では全高SS窓（SS=2, 3, 4, 5）が厳密に完全排除（`n2=0, n3=0, n4=0, n5=0`）され純粋に低SS窓のみから構成されること、赤字1供給がSS≥3窓を完全排除しSS=2窓を高々1個に抑えること、赤字2供給がSS≥4窓を完全排除すること、赤字3供給がSS=5窓を完全排除すること、単一SS=4窓が `slack ≥ 3`、単一SS=5窓が `slack ≥ 4`、二重SS=5窓が `slack ≥ 8` を強制すること、および `lag < 19` の全供給に対する大域容量不等式 `|U| ≤ |D|` が純粋に低SS供給へ無条件に還元されるという大還元定理をLeanで証明した。
さらにSS層化とlag<19における容量還元大統一定理（E-218、`GrandStratificationSynthesis`）により、`lag < 19` の全P2窓長が `{3, 7, 11, 15}` に限定され `ssCount ≤ 5` であること、`ssCount ≥ 4` を持つ窓が必然的に `lag = 15` に強制されること、`ssCount ≥ 6` を持つ窓が `lag < 19` に絶対に存在し得ないこと、任意高SS窓（`ssCount ≥ 2`）の存在が厳密な正の赤字バッファ `slack ≥ 1` を強制すること、飽和供給 `|U| = |D|` が純粋に低SS窓（`ssCount ≤ 1`）のみに剛性化されること、および `lag < 19` の全窓に対する大域容量不等式 `|U| ≤ |D|` が低SS供給へ無条件に還元されるというマスター大統一定理をLeanで証明した。
さらに周期依存tightボトルネック窓局在化とSS排除定理（E-219、`TightPeriodStratification`）により、任意周期 $p$ において正slack語のtight部分集合が非wrapping局所窓（`lag < p`）に厳密に局在しwrapping窓（`lag ≥ p`）が完全排除されること、周期 $p \le 15$ ではtight窓のlagが `{3, 7, 11}` に限定され、周期 $p \le 19$ では `{3, 7, 11, 15}` に限定されること、$p \le 7$ では全tight窓がクリーンAAS窓（`ssCount = 0`）に強制されること、$p \le 11$ では全tight窓が `ssCount ≤ 1` に制限され高SS窓（`ssCount ≥ 2`）がtight部分集合から完全に排除されること、$p \le 15$ では `ssCount ≤ 3` に制限され `ssCount ≥ 4` が完全排除されること、および $p \le 19$ では `ssCount ≤ 5` に制限され `ssCount ≥ 6` が完全排除されることをLeanで証明した。
さらに高SS窓のtightボトルネック完全排除と高SS部分集合狭義拡大定理（E-220、`TightSubsetSSExclusion`）により、正slackを持つ任意の周期語において高SS窓を含む部分集合が自動的・普遍的に狭義拡大（`|A| < |N(A)|`）すること、したがってtightボトルネック部分集合（`|N(A)| = |A|`）が高SS窓を含み得ず完全に低SS窓へ制限されること、周期 $p \le 11$ では `ssCount ≥ 2` の窓を含む任意部分集合が狭義拡大しtight部分集合の全構成窓が純粋に `ssCount ≤ 1` に制限されること、$p \le 7$ では `ssCount ≥ 1` の窓を含む任意部分集合が狭義拡大しtight窓が純粋に `ssCount = 0`（クリーンAAS）に剛性化されること、$p \le 15$ では `ssCount ≥ 4` を含む任意部分集合が狭義拡大しtight窓が `ssCount ≤ 3` に制限されること、および $p \le 19$ では `ssCount ≥ 6` を含む任意部分集合が狭義拡大しtight窓が `ssCount ≤ 5` に制限されることをLeanで証明した。
さらに閾値高SS窓の普遍的wrap性と最大近傍被覆定理（E-221、`HighSSWrappingTheorem`）により、任意のP2語に対して最小性仮定なしに `ssCount ≥ 2` が `w.length ≥ 11` を強制し、`ssCount ≥ 4` が `w.length ≥ 15` を強制すること、したがって周期 $p \le 11$ では全高SS窓（`ssCount ≥ 2`）が必然的にwrapping窓（`lag ≥ p`）となり、$p \le 15$ では全 `ssCount ≥ 4` 窓がwrapping窓となり、$p \le 19$ では全 `ssCount ≥ 6` 窓がwrapping窓となること、高SS窓を含む任意部分集合の近傍が減算全体に達する（$N(A) = D$ かつ $|N(A)| = |D|$）こと、局所slackが常に大域slack以上（$|N(A)| - |A| \ge |D| - |U|$）となり高SS窓が決してボトルネックとならず最大級の余剰被覆を提供することをLeanで証明した。
さらに高SS部分集合のHall条件不敗性とHall破綻の低SS局在化定理（E-222、`HallRobustnessTheorem`）により、総供給が減算数以下（`|U| ≤ |D|`）の任意の周期語において高SS窓を含む任意の部分リスト $A$ が自動的にHall拡大不等式 $|A| \le |N(A)|$ を満足し、$|U| < |D|$ では狭義不等式 $|A| < |N(A)|$ を満たすこと、したがって仮にHall破綻（$|N(A)| < |A|$）が発生する場合でも破綻集合 $A$ は高SS窓を含み得ず完全に低SS窓へ局在すること、周期 $p \le 11$ では全破綻集合が純粋に `ssCount ≤ 1` 窓に局在し、$p \le 7$ では純粋にクリーンAAS窓（`ssCount = 0`）に局在し、$p \le 15$ では `ssCount ≤ 3` に局在し、$p \le 19$ では `ssCount ≤ 5` に局在することをLeanで証明した。
さらにHall条件の層化低SS部分集合完全還元定理（E-223、`PeriodicHallReduction`）により、総供給が減算数以下（`|U| ≤ |D|`）の周期語における全加算部分集合上の大域Hall条件 $|A| \le |N(A)|$ が純粋に低SS部分集合上の検査へ無条件に完全還元されること、周期 $p \le 11$ では全低SS部分集合（`ssCount ≤ 1`）上でHall条件が成立すれば全加算部分集合上でHall条件が自動成立し大域Hall条件と低SS Hall条件が論理同値となること、$p \le 7$ では大域Hall条件がクリーンAAS部分集合（`ssCount = 0`）上の条件と論理同値となること、$p \le 15$ では `ssCount ≤ 3` 部分集合上の条件と論理同値となること、および $p \le 19$ では `ssCount ≤ 5` 部分集合上の条件と論理同値となることをLeanで証明した。
さらに容量赤字補償と高SS窓包含部分集合の減算削除普遍生存定理（E-224、`CapacitySlackCompensation`）により、高SS窓の存在自身が強制する供給赤字（slack）が減算削除のコストを完全に相殺すること、周期 $p \le 11$ では高SS窓（`ssCount ≥ 2`）を含む任意部分集合 $A$ が任意の減算 $s \in D$ の削除後も無条件にHall不等式 $|A| \le |N(A) \setminus \{s\}|$ を維持・生存すること、$p \le 7$（`ssCount ≥ 1`）、$p \le 15$（`ssCount ≥ 4`）、$p \le 19$（`ssCount ≥ 6`）でも同様の普遍生存則が成立すること、したがって供出減算 $s$ の大域削除可能性（Gate T6）の検証が高SS供出窓を避ける部分集合 $A \subseteq U \setminus \{u_0\}$ の検査へ無条件に完全還元されることをLeanで証明した。
さらに普遍的Gate T6閉結と層化削除可能性統合定理（E-225、`UniversalGateT6Closure`）により、周期 $p \le 7$ の全正slack周期語において供出加算を避ける任意のtight部分集合が純粋にlag 3 AAS窓のみから構成されること、供出減算 $s^*(u_0)$ が全tight部分集合の近傍と自動的に非交差（$s^*(u_0) \notin N(A)$）となること、供出窓を含む部分集合が容量赤字補償則により減算削除後も無条件にHall条件を満たすこと、非tight部分集合が局所slackにより生存すること、したがって周期 $p \le 7$ の全周期語において供出減算 $s^*(u_0)$ がいかなる外部仮定もなしに普遍的に削除可能であり $U$ の全部分リスト上でHall条件が厳密に保存されること、周期 $p \le 11$ ではGate T6の削除可能性検証がtight回避部分集合の検査へ100%完全還元されること、およびtight回避部分集合の全窓が純粋に低SS（`ssCount ≤ 1`）へ制限されることをLeanで証明した。








次エポック候補は18件を生成し、3レンズの敵対的スクリーニングで15件を却下した
（[triage](NEXT_EPOCH_TRIAGE_2026-09-11.md)）。生き残った3件はいずれも既存定理の合成で、
kernel上は通るがE-067/E-070/T4のいずれも動かさない。**独立した5件のkill判定が、
実際に開いているunitとしてT6（E-179）を名指しした**。従って次のgateはT6のまま据え置き、
合成lemmaを先に積まない。却下15件の衝突理由はtriageに記録した（再提案防止）。

E-067・E-070・全射性／非全射性は未解決のまま。active direct branch は0本。

続く [SS=2 先頭 run](HYPOTHESIS_CARD_2026-09-10_TWO_SS_OLDEST_S.md) で、境界例を通る共通履歴を Lean 証明した（E-132）。
最小 P2 で lag>3 なら先頭 AAS は禁止。先頭 A run が a≥3 なら、同じ run の時刻 `t-(a-2)` が
clean な lag-3 窓 AAS を持つ。標準 sign 114 の `AAASSSASASA` は a=3 で、sign 113 がこの兄弟である。
これは newest-S が E-128 の lag-3 端点と衝突する理由であり、SS=2 の新しい S 単射ではない。

名前付き4課金は停止した（E-133）。oldest-S は周期16で衝突、first-SS は周期13から衝突、
newest-S は標準 114/113 自身で E-128 と衝突する。S-ended prefix の SS≤2 拡張（E-130）に続く
定数修理はしない。

標準 10^7 の SS=2 最小供給は 52,357 件（E-134、`COMPUTED`）。one-per-run 違反 0。
companion（a≥3）148 件は兄弟 AAS が 148/148。孤立 a=0 が 52,198 件、a=1 が 11 件、a=2 は 0。
周期 1..18 も one-per-run 違反 0。有限診断であり、one-per-run の一般証明ではない。

孤立 a=0 の直前 S 課金は周期13と標準軌道 3950 件で E-128 と衝突し、`REFUTED`（E-136）。
原因は E-132 の双対で Lean 証明した（E-135）：長さ ≥3 の A run の先頭 t では t+2 が AAS を持ち、
端点が t-1。singleton A への1回修理は holdout 周期17で停止。
標準10^7の孤立 a=0 非singleton 5件はすべてこの E-135 の長さ3 run であり、長さ≥4の先頭は0（E-148）。

連続 A の one-per-run は、後窓が前窓を尾に含む入れ子なら `PROVED-LEAN`（E-137）。
距離2なら run はさらに前の A へ伸びる。前窓が後尾より長い場合は長さ23まで組0（E-138、`COMPUTED`）。

連続源（k=1）の one-per-run は、後尾が前窓を含む入れ子と、前窓が長く残りが短い場合まで
Lean（E-137, E-140）。無制限の連続 one-per-run は抽象履歴で `REFUTED`（E-142）：
`minWord (|v|-1)` を mass 0・moment −1・SS=2 の尾へ接着すると、連続する最小 P2 SS=2 が
二つできる。最小例は new=`ASSAAASAASS`、old 長さ31。標準10^7の SS=2 違反は 0 のまま。
SS=3 の軌道違反6件は同じ逆入れ子だが extra は SA 始まりで minWord ではない（E-143）。
直前 S 課金の再修理と offset 表は再開しない。

SS=2 の P2 は NoSAAS なしで先頭 A run が 4 未満（E-166）。E-132 の最小性で a=2 も消え、残るのは 0,1,3。軌道 10^7 と一致（E-158）。
ssCount≥1 の任意 P2 は先頭 A run が ssCount+1 以下（E-169）。等号 a=SS+2 の extraAs=0 族は 2·moment≤-6。SS=0 の AAS だけが質量等号で P2 になり得る。
孤立 singleton の SS 間隔のうち gap 2 は E-155、gap 4 は E-170。gap 3 と 7 は自由語として存在する（E-171）ので E-154 を語定理へ昇格しない。
SS 始まり15件は SSS+(NoSS尾) が8件（E-174）と SS(SA)* gap≥17 が7件（E-173）。
次の焦点は孤立 singleton の S 配分（課金再開なし）、または E-067/E-070。

E-067、全 lag の E-070、全射性・非全射性は未解決。active direct branch は 0 本のまま。

2026-09-10の[3時間研究](THREE_HOUR_RESEARCH_2026-09-10.md)で、**有限履歴から周期供給問題への縮約 E-065 を元の任意有限 State・任意開始 clock の範囲で Lean 証明した**。
周期性を仮定した実 greedy 更新から正の周期符号和と各 A 位相の P2 供給を導く。
供給の存在を仮定に置き換えていない。必要 lag は `0<d<p(p+1)`。

新しい [共通端点の研究](LOW_SS_ENDPOINT_CAPACITY_2026-09-10.md) で、**SS が高々1個の P2 窓を持つ全 A 位相の共同容量**を全周期で Lean 証明した（E-128）。
clean と SS1 を同じ S 予算で扱い、NoSAAS・最小 lag・周期符号和・lag 上限を仮定しない。
SS≤1 の任意の P2 窓には S で終わる P2 prefix があり、異なる現在 A の供給窓はその最古端を共有できない。
この二つの補題を周期接着した。紙上の二族分類 E-121 や単独容量 E-127 は証明の前提ではない。

E-129 の独立全数検査は周期1..22の 8,388,606 語で違反0。
標準 10^7 ステップでは対象が 992,184 / 1,315,896 = **75.39988%** の有限 P2 供給 A を占めた。
以前の「全 lag≤11 と clean の和集合」は 921,983 件・70.065% で、今回のクラスと包含関係はない。
新しい対象は旧範囲の外へ70,208件を加える一方、旧短距離の7件を含まない。**両定理の和集合容量は未証明**。
有限診断の割合を全 A や無限軌道の割合と解釈しない。

S-ended prefix を SS≤2 へ直接拡張する案は、標準 sign time114 / step115 の
最小窓 `AAASSSASASA`（lag11、SS2、NoSAAS、最古端103はA）で反証し Lean 認証した（E-130）。
従って実軌道条件や NoSAAS を足すだけの修理は停止する。E-070 自体の反例ではない。
SS ごとの定数予算の反例 E-122、型 B の実到達 E-125 も引き続き保持する。

E-131 では、同じ端点を共有する m+1 個の現在 A 供給窓には **最大窓に SS≥2m** が必要と Lean 証明した。
全 m の等号共通履歴も Lean。ただしその族は lag3 の短い供給を持つので、最小窓の反例ではない。
これは端点内の多重度予算であり、異なる端点間で SS を共同配分する定理ではない。

| 証拠 | 安定した成果・停止判断 |
|---|---|
| E-096 | 入れ子を仮定しない `(d₂−d)²≥4k(d₂−1)` と最適等号例、`PROVED-LEAN` |
| E-097 | 余剰≤4R の同 run 多重度閾値 `m≤R(R+1)` と全 R≥2 境界族、`PROVED-LEAN` |
| E-098 / E-099 | 中央 reservoir の A≤2R は `PROVED-LEAN`、固定 offset 延長は全 m≥3 で `REFUTED` |
| E-100 / E-101 | bounded-excess 容量を全周期で証明。同 run の rank により閾値を線形化、`PROVED-LEAN` |
| E-102 / E-103 | U≤11 との具体的容量は `PROVED-LEAN`。標準 10^7 で長 run 拡張の対象 0 件、追加最適化停止 |
| E-104 | 全 odd 時刻 A という明示的制約下の全 lag 容量、`PROVED-LEAN` |
| E-105 / E-106 / E-107 | clean を窓ごとへ局所化し U≤11 と合成、`PROVED-LEAN`。70.065% は `COMPUTED` |
| E-108 | 固定小偶奇欠陥数の拡張は `STOPPED`。有限 Hall 通過を一般証明としない |
| E-109 / E-110 | NoSAAS 下で SS-free iff clean、標準更新との接続は `PROVED-LEAN`。残余 SS 数は `COMPUTED` |
| E-111 | 有限 P2 iff 符号差 1 の実 historical blocker、`PROVED-LEAN`。一般 blocker の必要条件ではない |
| E-112 | 中央 charge は周期 12 と標準 sign time 1350/1352 で `REFUTED`、両方 Lean 認証 |
| E-113 | clean lag は d<2p、現在 A なら最適 `3d+7≤4p`、`PROVED-LEAN` |
| E-114 / E-115 | 短い blocker の P2 剛性と正周期での clock 非依存 lag bound、`PROVED-LEAN` |
| E-116 / E-117 | 標準正ドリフト尾から P2、自然周期の整数拡張と `d<p(p+1)`、`PROVED-LEAN` |
| E-118 | phase energy は旧 κ の定数倍だったため `STOPPED`。有限通過は新機構ではない |
| E-119 / E-120 | 非正の value drift 排除と任意有限 State への接続、`PROVED-LEAN`。E-065 全体を昇格 |
| E-121 | SS1 最小窓の二族完全分類は `PROVED-PAPER`。全パラメータ族の P2 式は `PROVED-LEAN` |
| E-122 | 同じ唯一の SS を跨ぐ最小供給需要は非有界、`PROVED-LEAN`。総 S 容量への反例ではない |
| E-123 | 標準 10^7 の SS1 最小供給 70,375 件、同じ SS の最大需要 2,796、`COMPUTED` |
| E-124 / E-125 | 型 B 排除は有限 seed で `REFUTED`（Lean）、標準 step 96,911,838 でも `COMPUTED` |
| E-126 | 任意 SS 数で内部の加算 run を制限する `a+v+2B≤SS+2` と正確な gap 余剰保存、`PROVED-LEAN` |
| E-127 | SS1 最小供給は A run ごとに高々一つ、従って全周期で SS1 単独の容量、`PROVED-PAPER` |
| E-128 | SS≤1 の任意 P2 を S-ended prefix へ縮め、共通端点の単射から clean/SS1 の共同容量、`PROVED-LEAN` |
| E-129 | 周期1..22全語と標準10^7を独立検査、low-SS対象992,184件・75.39988%、`COMPUTED` |
| E-130 | SS≤2へのprefix正規化拡張は標準step115で`REFUTED`、最小性・NoSAAS・A端点をLean認証 |
| E-131 | 共通端点をm回追加使用するとSS≥2m、全mで等号の共通NoSAAS履歴、`PROVED-LEAN`。族は非最小窓 |
| E-132 | 最小P2の先頭AAS禁止と a≥3 の clean lag-3 兄弟、標準114が実例、`PROVED-LEAN` |
| E-133 | SS=2のoldest-S・newest-S共同・first-SS課金、`REFUTED`。同じ課金の修理停止 |
| E-134 | 標準10^7のSS=2は52,357件、one-per-run 0、companion 148、孤立a=0が52,198、`COMPUTED` |
| E-135 | 孤立a=0が長さ≥3のA run先頭ならt+2がAAS、`PROVED-LEAN`。E-132の双対 |
| E-136 | 孤立a=0の直前S共同課金、周期13と軌道3950件で`REFUTED`。singleton修理もholdoutで停止 |
| E-137 | A始まりSS=2の尾にSS=2のP2 prefixは無い、連続入れ子は不可能、`PROVED-LEAN` |
| E-138 | 前窓が長いcase5は長さ23まで0、`COMPUTED` |
| E-139 | 標準10^7の孤立a=0は全件NoSAAS、52,193/52,198がsingleton、`COMPUTED` |
| E-140 | NoSS mass1の 2M+n≥3、等号 AA(SA)^rS。短いcase5残りは不可能、`PROVED-LEAN` |
| E-141 | 標準10^7のSS=3は21,727件、one-per-run違反6、lead2=0、`COMPUTED` |
| E-142 | 無制限連続one-per-runは抽象履歴で`REFUTED`。minWord接着の最小対をLean認証 |
| E-143 | SS=3の6違反はすべてE-140 momentのNoSS mass1 extra、先頭SA、後窓lead≥4、`COMPUTED` |
| E-144 | 標準10^7のSS=2にminWord extraは0/17443、`COMPUTED` |
| E-145 | NoSS mass1の完全分類 [A] / minWord / AS・SA前置。slack 3+8k+4a、`PROVED-LEAN` |
| E-146 | (SA)^k++minWord の moment 3k−r、slack 3+8k。SS=3 extra 6件がこの族、`PROVED-LEAN` |
| E-147 | 標準10^7のSS=2に prefix+(SA)^k minWord glue は0、`COMPUTED` |
| E-148 | 孤立a=0の非singleton 5件はE-135の長さ3 run、長さ≥4は0、`COMPUTED` |
| E-149 | 標準10^7のSS=4は16,455件、one-per-run 0、lead2=0、`COMPUTED` |
| E-150 | 最小P2のSSヒストグラム。同じSSのrun違反はSS0が41、SS3が6、SS≥64が20。ほか0。lead2はSS0のみ、`COMPUTED` |
| E-151 | 孤立先頭の長さ≥3 runはt+2がclean。41件のclean二重はこの形、`PROVED-LEAN` |
| E-152 | SS≥64の同一run 20組。18件はgap1でextra mass1 moment=1-|v|、extraはNoSSでない、`COMPUTED` |
| E-153 | minWord周期は lag≤4p でU=0。equality族はE-070反例にならない、`COMPUTED` |
| E-154 | 孤立singletonのSS間隔はgap1/5/≥8のみ。gap5は10件、`COMPUTED` |
| E-155 | SS間隔2はssCount≥3。ssCount=2ではgap2不可能、`PROVED-LEAN` |
| E-156 | 連続逆入れ子の extra は SS 非依存で mass1・moment=1-|v|、`PROVED-LEAN` |
| E-157 | 孤立singletonの99.97%がSA始まり、SS始まりは15件、`COMPUTED` |
| E-158 | SS=2最小の先頭runは0,1,3のみ。a≥4は軌道0、長さ31まで抽象0、`COMPUTED` |
| E-159 | NoSAAS SS=2 P2の先頭Aは5未満。残るa=4、`PROVED-LEAN` |
| E-160 | a=4 の E-126 等号族は moment≤-8 で P2 でない、`PROVED-LEAN` |
| E-161 | NoSAAS SS=2 P2の先頭A runは4未満。残るのは0,1,3、`PROVED-LEAN` |
| E-162 | SS=3の先頭runは0,1,3,4。a=4が54件、a≥5は0、`COMPUTED` |
| E-163 | SS=4の先頭runは0,1,3,4。a=4が3件、a≥5は0、`COMPUTED` |
| E-164 | a=5 の E-126 等号族は moment≤-15 で P2 でない、`PROVED-LEAN` |
| E-165 | NoSAAS SS=3 P2の先頭A runは5未満。残る0,1,3,4、`PROVED-LEAN` |
| E-166 | SS=2 P2の先頭A runは4未満。NoSAAS不要。残る0,1,3、`PROVED-LEAN` |
| E-167 | SS=3 P2の先頭A runは5未満。NoSAAS不要。残る0,1,3,4、`PROVED-LEAN` |
| E-168 | 任意P2の先頭A runはssCount+2以下。NoSAAS不要、`PROVED-LEAN` |
| E-169 | ssCount≥1のP2先頭A runはssCount+1以下。等号族はmoment≤-3、`PROVED-LEAN` |
| E-170 | NoSAASのSS間隔4はssCount≥3、`PROVED-LEAN` |
| E-171 | 最小NoSAAS SS=2 a=0はgap 3と7を持つ。E-154の欠落は軌道、`COMPUTED` |
| E-172 | NoSAAS ssCount=2のSS間隔6は内部AAAA（SSAAAASS）、`PROVED-LEAN` |
| E-173 | 孤立SS始まり15件はSSS(SA)*が8、SS(SA)* gap≥17が7、`COMPUTED` |
| E-175 | 周期31まで全正符号和語で`\|U\|≤\|D\|`違反0・`U=A`違反0・局所Hall飽和。E-081の語数と一致、`COMPUTED` |
| E-176 | `\|U\|≤\|D\|`は全周期でsharp。等号を達成する最大`\|D\|`は周期20で6、`COMPUTED` |
| E-177 | 等号語の最小供給窓はすべてssCount≤1。E-070の等号側はE-128の内側、`COMPUTED` |
| E-178 | 等号語の完全マッチングは一意で、強制辺1,110本すべてがoldest-S。selector探索終了、`COMPUTED` |
| E-179 | 高SS窓があればslack≥1。局所形T6「高SS窓は内部からSを供出」は周期22まで例外0、`COMPUTED` |
| E-180 | `slack ≥ c`は周期18 `AAAASSAAAASAAASSSS`と周期21で`REFUTED`。線形な衝突会計は停止 |
| E-181 | 正の周期質量だけで後退走査のdrift停止則と`d≤p(p+1)`、`PROVED-LEAN` |
| E-182 | tightブロックの接着でnet余剰は生じない。対627,264・三つ組6,751,269件、`COMPUTED` |
| E-174 | ssCount=2のSSS始まりは尾がNoSS、`PROVED-LEAN` |
| E-183 | Wrap-vs-SS会計：P2 lag `d=qp+r`で`q·S ≤ ssCount+2`、商上界`d/p ≤ ssCount+2`と`d<(ssCount+3)p`、`PROVED-LEAN` |
| E-184 | SS=2端点剛性：SS=2窓同士・SS≥1過去窓との端点共有排除、clean過去窓限定と遅延12以下介在語P2接頭辞、`PROVED-LEAN` |
| E-185 | SS=2周期端点単射性と直和容量：SS=2端点相単射性、SS=1との非交差性、S端合同容量`|U2|≤|D|`および`|U1|+|U2|≤|D|`、`PROVED-LEAN` |
| E-186 | SS=2 tight部分集合排除と減算削除帰着：p≤11・正slackでSS=2窓を含む任意AでN(A)=Dかつ|A|<|N(A)|、tight部分集合へのSS=2所属排除、任意減算削除に対する高SS成分のHall保存、`PROVED-LEAN` |
| E-187 | SS=2最古減算局所供出：S端SS=2窓の最古減算相s*(u)∈Dの自己被覆、p≤11・正slackでのHall保存、SS=2相互単射性およびSS=1像との非交差性、`PROVED-LEAN` |
| E-188 | tight部分集合回避とHall保存：減算削除による近傍保存二分法、deletabilityのtight回避帰着、lag 3窓の端点限定被覆と大域Hall保存、`PROVED-LEAN` |
| E-189 | 一般周期大域wrap障害とtight局所化：任意周期pでlag≥p窓のD全被覆、tight部分集合の非wrapping局所性（lag<p）、任意減算削除に対するHall条件の非wrapping帰着、p≤7（lag 3のみ）およびp≤11（lag 3, 7のみ）有限分類、`PROVED-LEAN` |
| E-190 | tightボトルネック集合サイズ下界：単一周期内減算指標の合同単射性、tight集合のlag上界lag≤2|A|+1、サイズ1および2のtight集合に対するlag≥7窓の排除とlag 3限定性、`PROVED-LEAN` |

## 2026-09-09 以前の判断と継承した証拠

以下は今回の出発点となった履歴である。「次」の指定は上の結論で更新する。

研究の目標は標準Recamán数列の全射性の真偽を決着させること。全射性・非全射性はともに未証明である。
全射性の命題の証拠レベルは`CONJECTURED`。現在、決着へ直結するactive direct branchは0本である。
#70・#71・#61、および5パターンの並列調査は判定を完了した。

続く[#73第1pass](ISSUE73_PERIODIC_SUPPLY_2026-09-07.md)で、全periodの符号語に対する
**lag≤7の供給容量U7≤Dと、正符号和なら短い供給を持たない加算が存在すること**をLeanで証明した
（E-071）。2026-09-08にmin-lag-11の17型へU7と像が交わらないchargeを与え、型対の距離`j−i`
での符号衝突をLeanで決めた（E-079）。同じchargeの周期接着により
`|U7 ∪ U11min| ≤ |D|`は全周期でLean（E-080）。min-lag-15の155型へ同じ非両立CSP chargeを延長し、
`|U7 ∪ U11min ∪ U15min| ≤ |D|`も紙上で成り立つ（E-086）。正符号和のE-070反例は最小lag≥19
を使う。任意周期の `|U11min| ≤ |D|` は Lean（E-087）。E-067はperiod19..22の正符号和3,487,066語でも
U=Aが0（E-081, `COMPUTED`）。全lagのE-067/E-070は未解決で、#73はOPEN。E-072・E-073・E-074・
E-075のselector・rank・単純予算を停止し、E-076・E-077・E-078の有限証拠は一般証明と分ける。
lag-19型表は完了にしない。lag-by-lag型課金クラスは停止した（E-088）：宣言した
d非依存セレクタはlag-15でZ開対を持ち、φ7を一様規則として再現しない。E-080/E-086は残る。
次は新しい型表ではなく、d非依存の局所障害または閉形式potentialだけを再開条件とする。
供給Aのtwo-child κ降下をSへ単射課金する案とそのleast-P2窓への修理は反例で停止した
（E-082, E-083）。どちらもU=Aではない。L=7 potentialの新しい7bit埋め込みもL=11で偽（E-084）。
C++のL=23は正サイクルなし・max P=5で、L=19のmax=4は天井ではない。
U7のfollowing-gap類へのlag-11一様課金は`ASSSASSAAAASSA`で偽（E-085）。lag-by-lagの
型offset延長はE-088で停止。

2026-09-09の[一回・二回の減算先読み](HYPOTHESIS_CARD_2026-09-09_CATALYTIC_LOOKAHEAD.md)は
両候補をL=11で反証した（E-089, `REFUTED`）。未来の減算をk回まで許した最大純供給数R_kは、
S一歩でk=1では1→3、k=2では0→2と増え、F_k=−R_kの支払不等式が破れる。
上界を含む値は独立全列挙で確認。kを増やす今回の探索は`STOPPED`とし、任意の固定kの不可能性や
E-067/E-070の反証とは扱わない。再開には減算による供給の繰り返し再活性化を扱う構造が必要。

同日の[1時間研究](ONE_HOUR_RESEARCH_2026-09-09.md)で、型表に依存しない局所障害を得た。
先頭にm≥3個のAを持つP2窓は **d≥4m−1**、この下界を達成する全mの族もLean（E-090）。
等号窓はmの整数分割と一対一（E-091, `PROVED-PAPER`）で、直後のm−1個のSはLeanで強制される。
同じA区間の入れ子供給には **Δ(Δ−4k)≥4k(d−1)** が必要で、等号窓のchargeは単射、
長い等号窓の直前から二つ目のSは短い供給のchargeと衝突しない（E-092, `PROVED-LEAN`）。
この局所機構と周期上の接着から **|U≤15|+|Q(m≥16,d=4m−1)|≤|D|** を紙上で得た
（E-093）。追加するlagは63以上で上限なし。周期接着・像の非衝突・一般の個数拡張も
Leanで証明した（E-095）。既存φ7/φ11/φ15への具体的適用は紙上であり、
すべての長い窓を扱うE-070とは区別する。

一方、最小供給lagがA区間で単調に増える案は反証した（E-094）。具体例の23→15はLean、
先頭A数r²−1でlagが4r²+4r−1→4r²−1となる任意r≥2の族は紙上。
従って「長いA区間なら窓は入れ子」としてE-092を拡張してはいけない。
次の研究対象は**等号でない窓と、入れ子でない窓への切り替わりを同時に扱う局所制約**。
lag別型表、先読み回数の増加、run長だけでの単調lag修理は再開しない。
E-067/E-070および全射性・非全射性の未解決状態とactive direct branch 0は変わらない。


最新の[並列調査と順位](PARALLEL_APPROACH_TRIAGE_2026-09-07.md)では、次に掘る候補を
**周期符号語の供給不足**へ絞り、[issue #73](https://github.com/hirokidaichi/recaman-lean-research/issues/73)を作成した。有限履歴のeventually periodicな実更新は、各加算phaseに
有限lagの供給恒等式P2を要求する（`E-065`, `PROVED-LEAN`、2026-09-10に全有限State版を監査済み）。
それを全加算phaseで同時に満たす正符号和の語は存在しない、という命題は`CONJECTURED`（`E-067`）。
period≤18の229,045語と別の90,640評価では反例0だが、一般証明ではない（`E-066`, `COMPUTED`）。
強化した供給phase数の容量不等式も未証明（`E-070`）で、最古Sへの単射案は反証済み（`E-069`）。
これは固定blockによる帰納の可否を判断する構造研究であり、永久欠損へはまだ接続しない。

他の限定候補は停止：同じ集計値から異なる2step到達が生じる履歴対（`E-061`）、SS入口でも
blockerの早い初出を要求できないcanonical反例（`E-063`）、連結supportへ補修できるsurvival反例族
（`E-064`）、全有限穴集合が空になり得るhole-only抽象（`E-068`）。
初出を逆算したold rail輸送と入口分類は`PROVED-PAPER`の部分結果（`E-062`）だが、
canonical生成を分離する新しい不等式ではない。5方式全体の不可能性を示したとは扱わない。

最新の[戦略地図](STRATEGY_MAP_2026-09-07.md)は、#70のLean証明と#71の分類・停止判断、#61の既存証明統合を記録する。
#61では認証済みの19@99734をno-low補題へ接続し、完全なpermanent-tail replayのclock112を
追加仮定なしに排除した。clock下界113・target下界115は`PROVED-LEAN`（`E-060`）。
これは既存の有限残余の解消であり、大域機構の発見や停止済みfloor列挙の再開とは扱わない。
詳細は[#61仮説カード](HYPOTHESIS_CARD_2026-09-07_CLOCK112_CLOSURE.md)。
前回の自由cutoffと固定prefixの監査も維持する。
`∀ B, ∃ N, ∀ n≥N, B<a(n)` は無条件に `PROVED-LEAN`（`E-052`）。
従って自由なeventual landing floorだけでは永久欠損は出ず、canonicalの4の遅い出現が
cutoffを取り違える推論の反例になる（`E-053`）。旧 `E-028` のrouteは `STOPPED`。
同じ検証済みcutoffから先を排除する定量入力は未解決である。

local survival比も追加前史なしには閉じない。density・parity・one-useを全て満たすexact seedに
比を破る59→1のno-wrap continuationがあり（`E-054`, `PROVED-LEAN`）、任意の固定finite prefixを
含めても破れる反例族を得た（`E-056`, `PROVED-LEAN`）。一方、preload-freeな20,001軌道の
2,677,448適用recordではT=1 survival比に違反0（`E-055`, `COMPUTED`）。
canonicalやpreload-freeでのsurvival比の一般命題は未証明。新候補 `7J≤3(v-u)` はcanonical
200億項のholdoutで5件破れた（`E-057`, `REFUTED`）。係数修正は停止し、反例のphase/birth
分類を完了した（`E-058`, `COMPUTED`）。31,058値を二つの隣接producer railへ分類したが、
独立した大域不等式は得られず正のsurvival攻略は`STOPPED`（`E-059`）。
一般seeded countermodel族は#70で全payloadのLean認証を完了した。

形式化済みのresidual kernelは、仮想missing tailをeventual-high corridor（A枝）または
fixed-root target-low stream（B枝）へ送る。A枝は「欠損値非有界」またはrigid burst streamまで
縮約済みだが、burst streamを排除するfixed-seed ancestry/drift枝は停止条件に到達した。
B枝のreset repaymentも、新しいglobal invariantがないため停止中である。

停止は命題の否定を意味しない。fixed-seed infinite supply no-goとreset repaymentのexact命題は
未反証だが、それらを現在のpayloadから導く証明ルートが尽きた、という判定である。

## 現在の分岐

| 分岐 | 現在得られているもの | 証拠 | 判定 |
|---|---|---|---|
| 全射性 | `∀ m, ∃ t, a t = m` | `E-001` | `CONJECTURED`、active direct branch 0 |
| residual kernel | 仮想missing tailのA/B exact二分 | `E-002` | architectureとして保守 |
| A: divergent candidate | candidate発散なら永久欠損値が非有界 | `E-004` | 構造的代償。矛盾ではない |
| A: recurrent burst | 欠損非有界またはrigid burst stream | `E-003` | supply no-goだけが未決 |
| A: demand birth | subtraction/addition birth分類、addition枝のclock contraction | `E-005` | `PROVED-LEAN`の再利用可能部品 |
| A: periodic schedules | balanced有限核とeventually-periodic no-go | `E-006`, `E-007` | 非周期scheduleは未排除 |
| A: supplier ancestry | forced class非閉包、generic parent merge | `E-008` | `REFUTED` |
| A: one fixed seed | 内部供給つき3-use有限例、infinite no-goは未決 | `E-009`, `E-010` | 現proof branch `E-011`は`STOPPED` |
| A: admissible seed density | 既知seedはすべてcanonical density（`valuesThrough_length`, `a_le_upperTri`）に違反 | `E-019` | `COMPUTED`、gate 3の最初の拘束的候補 |
| A: preload-free orbits | 20,001 orbit・1.27M burst useにsame-candidate link 0件（strict-high形・c-floor形とも） | `E-020`, `E-021` | `COMPUTED`、c-floor link no-goは`CONJECTURED` |
| A: cone excursions | burst後のstrict-high excursionは倍化clock前に崩れ、cone-exterior runは2倍へ届かない | `E-022`, `E-023` | `COMPUTED`、excursion boundは独立`CONJECTURED` |
| A: local use gap | `sqrt(6m)`のlocal読み | `E-012` | `REFUTED`、修理も`STOPPED` |
| A: external blocker collision | same-candidate H4/H8 test | `E-015` | 20Mまで評価母集団0、設計を`STOPPED` |
| A: window collision | 異candidate dyadic window集約の`E ∩ S` | `E-016` | 17適用windowすべて交わりなし、`REFUTED` |
| A: demand provenance | 減算初出はnear-diagonalが多数、加算初出はtruncatedが約3割 | `E-017`, `E-018` | `COMPUTED`、最小証人は`PROVED-LEAN`。gate 3の制約条件 |
| B: reset repayment | exact命題は未反証、local bridgeは枯渇 | `E-013` | `STOPPED` |
| 独立部分定理 | `TailHall₃`候補 | `E-014` | `CONJECTURED`、全射性の直接枝ではない |

## 証明frontierの最短形

```text
least missing target
  -> exact residual kernel
     |- A: eventual-high candidate corridor
     |    -> missing values unbounded
     |       or rigid recurrent burst supply
     |          -> fixed-seed infinite supply no-go is open
     |          -> current ancestry/drift proof route is STOPPED
     |
     `- B: fixed-root target-low stream
          -> infinitely many upward resets
          -> reset repayment proof route is STOPPED
```

この図の矢印は証明済みの依存と未証明義務を区別する。最後の二つの`STOPPED`を
同値なcoverage、future return、canonical reachabilityで置き換えてはならない。

## 再開条件

A枝を再開するには、次のいずれかを先にexactな仮説カードへする。

1. external addition blocker集合`E`について、cutoff-independentに`|E|`が非collision量に対して
   strict growthする不等式（`E ∩ S`型のcollisionは同一candidate形・window集約形ともに閉鎖済み）。
2. reuse intervalのcrossingやparent merge後にも保存される非merge質量。
3. arbitrary finite stateと`stateAt start`を、future returnやtarget occurrenceを仮定せず分離する
   canonical-only invariant。
   最初の候補はhistory density（`|seen| ≤ clock+1`、`max seen ≤ upperTri clock`）である。
   `H-20260902-03`により、既知の固定seed反例は全深度でこの拘束に違反する（`E-019`）。次のunitは
   blockerをpreloadせずexact prefixで生成するadmissible synthesizerか、admissible seedのuse数上界の
   紙上証明でなければならない。
   `H-20260902-04`はpreloadなしの単一初期値generalized orbit 20,001本（内部供給burst use 1,272,765件）で
   strict-high same-candidate linkが0件であることを示した（`E-020`）。exact命題「generalized orbitに
   strict-high linkは存在しない」を`CONJECTURED`として登録し（`E-021`）、許可されるformalization routeは
   「最初のlinkがpreloaded blockerを強制する」紙上証明のみとする。
   **意味上の注意**：strict-high（candidate > clock）は2026-09-01のfixed-seed protocolの
   use間条件であり、corridorの実際の条件（least recurring candidate cに対しcandidate ≥ c）より強い。
   そこでprobeにc-floor mode（中間candidateが全て≥c）を追加して再検査したところ、censusは不変で
   link 0件だった。従って`E-021`はc-floor形（corridor-faithful）で登録する。一方`E-023`の
   excursion boundはcone-exterior条件に依存する独立部分命題であり、corridor streamを排除しない
   （`E-022`参照）。同様に、2026-09-01のfixed-seed 3-use記録はstrict-high形の記録であり、
   c-floor形での固定seed探索は未実施である。

2026-09-02の最初のexternal collision unitは、同じcandidateの4回または8回のsupplied useで
`E ∩ S`を要求した。しかしcanonical 20Mでは4,798 useに対し4,797 candidate、最大use数2で、
既知fixed seedも3-useに留まるため評価母集団が空だった。この閾値設計は`STOPPED`とし、上の
再開条件1を満たすには異candidate間または固定clock windowで集約される非空なdebt量を要求する。

2026-09-02の第二unit（`H-20260902-02`）はその要求どおり、異candidate・dyadic window集約の
collision `E(W) ∩ S(W) ≠ ∅`、減算初出需要の半clock縮約`2t < w`、加算初出需要の非truncated性
`2b < w`の3命題を凍結した。3命題ともcanonical discovery 2Mで反証され、holdout 20Mでも
17適用windowすべてで`E ∩ S = ∅`、near-diagonal減算初出1,533件、truncated加算初出732件だった。
従ってcollision型のdebt設計は同一candidate形（空虚）と集約形（反証）の双方で閉じ、再開条件1は
`|E|`のstrict growth形だけを残す。再開条件3のcanonical-only invariantは、canonicalで多数派である
near-diagonal減算sourceを許容しなければならず、birth-clock縮約では固定seedと分離できない。

B枝を再開するには、post-reset blocker birthをfuture repayment、target occurrence、canonical
reachabilityなしに有限化するglobal invariantが必要である。

`TailHall₃`は、全射性ではなく`liminf a_n/n ≤ 3`型の独立部分定理としてのみ再開できる。

いずれも、exact statement、acceptance test、frozen falsifier、stopping conditionを持つ
hypothesis cardが作られるまでactive branchへ昇格しない。

## 2026-09-02 午前の方針転換（真偽を問わない証明計画）

全射性が偽でもよいという方針のもとで、
[`RESEARCH_ROADMAP_2026-09-02_TRUTH_AGNOSTIC.md`](RESEARCH_ROADMAP_2026-09-02_TRUTH_AGNOSTIC.md)
を作成した。要点は次の通り。

- `E-024`（`COMPUTED`, canonical 3e9）: sub-diagonal着地は28.6%で安定し、A枝の無限corridorは
  経験的に全targetで偽である。小さな高さはdescending chain（2時刻で高さ3減、既存のcomb）でしか
  現れず、[1e8,1e9)の47件は1本のchainだった。mex 1355はchainの剰余類（mod 3）が合わず着地できない。
- `E-025`（`PROVED-LEAN`, `MissingDensityDichotomy`）: 二分定理D「無限個のnで`a n ≤ n+2`、または
  全ての窓`[0, m+2]`（`m ≥ 2N+2`）に`m ≤ 4·|missing|`を満たす永久未訪問値のNodupリストがある」。
  系`EventualHighCandidateTail.missing_density`はA枝が密度1/4の欠損を含意することを、
  `not_eventualHigh_of_recurrent_low`は`a n ≤ n+2`の再発が全targetのA枝を否定することを示す。T1完了。
- `E-026`（`PROVED-LEAN`, `DescendingChain`）: chain補題（T2）と遅延着地の特徴づけ`late_landing_iff`（T3）。
  強制加算、帯への着地（高さ`h−3`）、k段の降下`chain_descends`、mod 3剰余類、上方脱出と遅延着地の2出口。
- `E-027`（`COMPUTED`, Chaffin 10^612項）: 下降弧は1 decadeあたり8.45本で一定だが深さ比の裾は急峻で、
  10^41以降10^7未満の着地はない。852655は10^612項まで欠損、1355の初出は第3.25×10^11項。
  真偽の見立ては非全射側に大きく傾いた。
- `E-029`（`COMPUTED`, run-length simulator 10^13）: 1355の初出とmex推移がOEISと一致。2^20未満の遅延着地は
  1 decadeあたり約2.3分の1に減り、10^12台では30件。高さ≤1356のinterior時刻は各decade数百〜二千件で、
  [1e9,3e9)の0件は揺らぎだった。
- `E-030`（`PROVED-LEAN`, `HoleHopping`）: chainは自クラスの最初の未訪問candidateに着地し、小さい値への着地後は
  連続する穴を掃く（comb）。小さい値の領域の力学は「穴の集合の上の剰余類ゲーム」である。
- `E-031`（`COMPUTED`）: 帯の生存を無制限とした閉包はChaffinの穴をほぼ全て（852655を含む）埋めるので、
  852655の保護は剰余類の組合せではなくarcの深さ（帯の生存）に依る。
- `E-032`（`COMPUTED`）: 区間の終端は遅延着地61%・帯の既訪問値39%。帯の未訪問run長は典型的に`n·10^−6`。
- `E-034`（`PROVED-LEAN`, `PopupLock`）: pop-up後に `2c+v+2` が既訪問なら `k=3/4` に固定され、その間 clock 未満の値は
  訪問されず、`k=2` 候補は弧自身の直前の `k=2` 値である。arc trace の終端機構の局所部分は全て Lean 化された。
- `E-035`（`PROVED-LEAN`, `LevelTwoThree`）: pop-up後に `2c+v+2` が未訪問なら `k=2` へ戻り、`k=2/3` ping-pong は
  1対ごとに offset が5減り、K対後の `k=1` への出口では位置エネルギー（値+時刻）が `2m+s−K`、すなわち
  段の直前より `K−1` 低い。Φ を下げる唯一の局所機構が Lean 化された。
- `E-033`（`COMPUTED`, arc trace 10^10）: 弧の底は最後の遅延着地であり、深い弧6本の底はcomb末端で
  `2c+v+2` が既訪問のとき `k=3/4` に固定される（6/6）。その値は同じ弧が少し前に `k=2` 値として
  訪問していた。（旧版の「終端は Φ の落差で記述できる」は `E-036`/`E-037` で撤回。）
- `E-036`（`COMPUTED`, arc potential probe 10^10）: 「固定 ⟺ `Φ=2·時刻+高さ` の落差 ≥ 3」は偽。blocked かつ
  落差 < 3 が 318 件（test 値は前の弧の `k=4` 値）、fresh かつ落差 ≥ 3 が 2,745 件。底 = 最初の落差 ≥ 3 の
  comb 末端は 0/39。Φ の減少は `k ≥ 3` を経由する区間でのみ起こる（45,859 件、`maxk ≤ 2` は 0）。
- `E-037`（`COMPUTED`, arc death-rule probe 10^10）: 固定は通常破れる（break 15,926 / wrap 8 / `k=5` へ 3,452）。
  break 添字は `i_gen=(T−1)+⌊(J_eff+2)/3⌋`（12,777/15,926）、固定のまま剰余が尽きる条件は `v<13+7·i_pred`
  （7/1/0/15,926）。36 弧の底は全て comb 末端で、弧の終わりは wrap 8・break 後に穴なし 11・fresh 後に
  穴なし 15・`k=5` 後 2。landing floor は「剰余の残量と帯の run で費用が決まる hole-hopping の降下が
  852656 に届かない」命題に更新（カード受入条件 3）。
- `E-038`（`PROVED-LEAN`, `LockResidue`）: 剰余則 `(q,r)→(q±1,r−q)`（`q≤r`）と剰余の跳ね上がり（`r<q`、ステップ種に
  よらず弧が終わる）、固定の 1 対で剰余が 7 減ること、予算 `t<m+7`（comb 末端座標で `v<13+7K`）で対の内部に
  剰余増加が起きること、着地前 run が J 対なら固定が `⌊(J+2)/3⌋` 対以上続くことを Lean 化。`E-037` の wrap 条件と
  T=1 の break 下界（10^10 で 2,658/2,658）の局所部分が定理になった。
- `E-039`（`PROVED-LEAN`, `PingPongRuns`）: 任意 level `p+2/p+1` の ping-pong の 1 対で剰余は `2p+3` 減り、K 対の run の
  上側値は `a m + k`、下側値は `a m − (m+k+1)` の連続 run（候補の既訪問/未訪問だけで記述）。既訪問候補は加算を、
  未訪問候補は減算を強制する。chain(p=0)・k=2/3 段(p=1)・固定(p=2) の共通形で、blocker provenance
  （`H-20260903-01`、[card](HYPOTHESIS_CARD_2026-09-03_BLOCKER_PROVENANCE.md)）の仮説 (B) の裏付け。
- `E-040`（`PROVED-LEAN`, `CombExit`）: T 本の歯の comb の加算値 `i+v+2−s` が、test 値未訪問後の k=2/3 段の出口候補
  `i+v−2−3k`（`3k+5 ≤ T`）を塞ぐ。段は `⌊(T−2)/3⌋` 対以上続く（`popup_lock_persists` の fresh 側対応物）。
  provenance census（10^9）で entry23 blocker の 85% が同じ弧の level-1 値、その主成分が gap=7 の comb 加算値
  だったことの exact な説明。
- `E-041`（`COMPUTED`, blocker provenance 10^10、`H-20260903-01` は `REFUTED`）: 降下を塞ぐ値 52,228 件の初訪問を
  全数調査。lock 側（test/lockcand/l3）は全て level ≥ 2 で 96% が**同じ弧自身**の run（k=2/3 段の下側 run、chain の
  上側 run、以前の固定の k=3 run）、残りは前の弧の k=4 固定 run（`n/c ∈ [0.44,0.62]`）。fresh 側（entry23/bandexit）は
  同じ弧の level-1 値が 87%（comb の歯 4 の加算値 = gap 7、`CombExit`）、前の弧の k=2 値（`n ≈ c/2`）が 12%。
  99.78% が ping-pong run に属し、例外は梯子・スパイク・谷のみ。**帯の履歴は「同じ弧の直近の run」と「前の弧の
  時刻 ≈ c/2 の run」で決まる**（スケール半減の自己相似）。[epoch report](BLOCKER_PROVENANCE_EPOCH_2026-09-03.md)。
- `E-042`（`PROVED-LEAN`, `H-20260905-01`）: no-wrap 予算 `13+7k≤v` と comb 末端より早い clock
  `n<c=i+1` だけで、lock candidate `w=2c+v−1−3k` は sharp な `2n+14+4k≤w` を満たす。
  positive `n` では `2≤w/n`。従って `E-041` 後続候補 (A') の `lockcand` level 下界も
  provenance を使わない算術的帰結であり、この枝は landing floor の causal input として `STOPPED`。
  再開条件だった具体的run帰属は `E-043` で調べ、`E-044` のno-goまで進んだ。
- `E-043`（`COMPUTED`, `H-20260905-02`）: `lockcand` 初訪問を same-arc `q=2` の upper/lower/both
  ping-pong rail、run外の `SSSS` ladder / `SSAA` valley、または直前arc `q=4` の `SSSS` ladderの
  6型へ凍結分類した。`c<10^10` の609件と未使用holdout `10^10≤c<2·10^10` の274件は無修復で
  全て分類され、time/budget/formula/flag/gap-cost違反も0。一般定理ではなく200億までの有限証拠。
- `E-044`（`PROVED-LEAN`, `LockResidue`）: same-arc型の `q=2` 分解 `w=2n+r` は
  `2(c−n)+12+4k≤r` と `2(c−n)+13+4k≤n` を課す。一方、任意の `M` に対して一つのlocal
  `(n,r,w)` が `M` 個の異なる後続event式・no-wrap予算と両立する弱化history countermodelもLean化。
  実測でもevent arc当たりのquery最大数は129から196へ増えた。local producer分類だけからuniform
  bounded charge / landing-bottom descentは出ないため枝は `STOPPED`。再開にはactual arc survivalを使う
  strict descentまたはfinite-to-one chargeが必要。[epoch report](LOCKCAND_PRODUCER_EPOCH_2026-09-05.md)。
- `E-045`（`COMPUTED`, `H-20260905-03`）: actual arc survivalへ戻り、同じcompleted arcに後続late
  landingを持つblocked comb endの必要条件候補 `7·hPrev≤16·v`（run identityにより
  `7T+21J≤9v`）を凍結した。既存discovery 19,365件、10^10時点でopenだった第40弧のpre-cutoff
  352件、未使用holdout `10^10≤c<2·10^10` 6,391件で違反0・identity違反0。第40弧は
  `a(13808214835)=1814`を底として完了し、この新terminal recordもthreshold未満に入った。
- `E-046`（`PROVED-LEAN`, `LockResidue`）: `T=1`ではthresholdの逆向き
  `16v<7(v+1+3J)`がpre-landing runを最初のresidue-budget failure pairまで持続させる。
  level-3側freshnessの下で`popup_lock_wrap_of_long_prelanding_run`がpair内residue increaseを強制し、
  threshold未満terminal 9件中T=1 wrap 7件の機構を説明する。
- `E-047`（`PROVED-LEAN`, `H-20260905-04`, `LockResidue`）: multi-toothではfinal lockの
  `k<T-1`候補がearlier-tooth test値そのものであることを使い、その値がfinal landing時までに既訪問という
  actual-history仮定とshiftしたpre-landing runを合成する
  `popup_lock_wrap_of_multitooth_history`を証明。唯一のthreshold未満`T=2` terminalはこの条件と数値的に
  整合する。一方、同membershipは全`T≥2` recordの21,563/45,889件にしかなくcomb形だけでは導けない。
  一般survival比は`CONJECTURED`のままで、残余はmembershipをarc survivalから強制するedgeと
  `l3blocked` survival。
- `E-048`（`PROVED-LEAN`, `H-20260905-05`, `PingPongRuns`）: 一般levelの
  `pingpong_pair_wrap`はresidueがpair費用`2p+3`未満なら二歩内のincreaseを返す。`p=3`を反復runへ
  適用した`level45_run_wrap`は`9K≤r<9(K+1)`でpair `K`のwrapを強制し、threshold未満terminal
  `c=99734,v=19`の`5A 4S 5A 3S`（初期residue 9）を説明する。
  `popup_l3blocked_level45_entry/wrap`がpopup座標からこのkernelへのbridgeも与える。通常の
  `l3blocked`後に必要なfresh/blocked historyが何pair続くかは未証明。
- `E-049`（`REFUTED`, `H-20260905-06`）: completed-arc l3blocked 4,844件のinitial level-5/4 runを
  exact追跡。discovery 3,478件はwrap 1 / upperBlocked 628 / lowerFresh 2,849、holdout 1,366件は
  0 / 223 / 1,143で、wrap index違反0。しかしterminal `c=588583`はbudget 532 pairに対し43 pairで
  `lowerFresh`へ離脱し、offset 1350で後からwrapするため「terminal iff initial budget wrap」は反証。
  個別traceでは後続がupper residue `4393-7j`のlevel-4/3 phase 628点であることをexact確認した。
  first-exit classifier枝は`STOPPED`。再開にはlevel下降を跨ぐphase間のglobal descentが必要。
- `E-050`（`PROVED-PAPER`, `H-20260906-01`）: phase capacity
  `B(q,r)=floor(r/(2q-1))`と`alpha·n+beta·x+psi(q)`の和は、exact seeded lowerFresh族と
  upperBlocked族により全係数が排除され、連続positive-length phase間のstrict descentもnonincreaseも
  与えない。seedはhistory cardinality、triangular range、canonical parityを満たすが、全seed memberの
  initial-0 first-birth provenanceは要求しない。従ってこの限定classは`STOPPED`であり、全canonical
  invariantのno-goとは扱わない。
- `E-051`（`COMPUTED`, `H-20260906-02`）: completed canonical arcの`l3blocked` event後、最初のwrap
  またはlate landingまでの同一positive blocker多重度`<=2`を凍結検査。discovery `s<=600000`は
  17 excursion・6,305 use・最大2、holdout `600000<s<=2000000`は22 excursion・12,802 use・最大1、
  違反0。一回使用は`c=97896,w=395922`の二回使用で偽。all-scale boundは`CONJECTURED`で、
  survival ratioへ接続するweight inequalityなしにはLean化しない。
- `E-028`（`STOPPED`, `H-20260902-05`）: 自由cutoffのlanding floorから非全射を導くrouteを停止。
  floor自体は`E-052`の無条件な帰結で、prefixと同じcutoffを供給しない。rising floorだけによる
  欠損無限個の推論も`E-053`で撤回。固定した検証済みHから先の排除には新しい定量入力が必要。
- 両方向の証明はchainの侵入率・生存の定量定理（T4）に帰着する。Chaffinのデータで「侵入（弧）の
  発生率は`c/n`で減衰しないが、弧の深さが固定値へ届かなくなる」と判明したため、T4は非全射方向
  （chainの生存長が帯の未訪問run長で決まる自己相似構造）の証明を目標にする。
- 上の分岐表と再開条件は歴史的記録として残し、優先順位は2026-09-06の戦略地図に従う。

## 文書の役割

| 文書 | 役割 | 更新規則 |
|---|---|---|
| `CURRENT_FRONTIER.md` | 現在の研究状態と再開gateの正本 | status変更時に必ず更新 |
| `EVIDENCE_REGISTRY.tsv` | frontier-changing claimと証拠の機械可読正本 | claim追加・label変更時に更新 |
| `Recaman/Audit.lean` | `PROVED-LEAN`定理のkernel監査正本 | major theorem追加時に更新 |
| `PROOF_MAP.md` | theorem dependencyと過去の到達経路 | 現在の優先順位を主張しない |
| `ROADMAP.md` | 判断とgateの時系列 | 過去記述を上書きせず追記 |
| `STATUS_REPORT_2026-08-30.md` | 2026-09-01までの説明的snapshot | current statusの正本にしない |
| `RESEARCH_PORTFOLIO.md` | 過去枝のscore・停止理由・再開条件 | historical portfolioとして保存 |
| `DEVELOPMENT_LOG.md` | append-onlyな実装・研究ログ | 過去記録を書き換えない |
| `HYPOTHESIS_CARD_*.md` | 一つのbounded research unit | quantifier・acceptance・stopを凍結 |
| round/audit report | 一回の研究handoff | 後日のstatus正本にしない |

## 同期規則

1. evidence labelには`PROVED-LEAN`, `PROVED-PAPER`, `COMPUTED`, `OBSERVED`,
   `CONJECTURED`, `REFUTED`, `STOPPED`だけを使う。
2. `PROVED-LEAN` registry rowは一つ以上の`#print axioms`対象を持たなければならない。
3. computationのhorizon延長だけではlabelを上げない。
4. exact命題が`CONJECTURED`でも、証明ルートが尽きれば別rowで`STOPPED`にする。
5. current branchの変更は、この文書とregistryを同じchange setで更新する。
6. `bash scripts/check_research_registry.sh`と`./scripts/check.sh`を通してからhandoffする。

## 現在の検証基準

- Lean 4.33.1、標準ライブラリのみ。
- Lean source 311 files（`Recaman/` 310 に root の `Recaman.lean` を加えた数。`Audit.lean` は前者に含む）。
- `./scripts/check.sh`: 1,743 audited declarations。証拠台帳182件、うち `PROVED-LEAN` 76件。
- 許可された公理依存は`{propext, Classical.choice, Quot.sound}`。
- `sorry`, `admit`, `native_decide`, user-defined `axiom`は禁止。
