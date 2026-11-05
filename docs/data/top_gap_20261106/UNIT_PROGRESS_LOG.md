# 2026-11-06 research units

Baseline main and origin/main: ae4d701ecbc6844ea8109f653b3791b5935c2450. The 2026-11-06
journal was the only untracked path at setup. Previous hosted CI 41929965090 succeeded in all
three jobs. Mathematical exploration worker budget is 0. Individual Lean runs use -j1 -M512,
10 CPU seconds per process and 20 wall seconds, with process-group wall termination. This is
neither an OS address-space cap nor cumulative tree CPU enforcement.

## H01 counted last-seven and shared source key

Question: Does the actual last-seven branch of the original four-run old-target counter imply
new clock bounds or contradiction? Acceptance: same original windows, actual count, old
source mass untruncated, exact source order and source key. Stop at the 15-minute gate if no
new edge; no resource-only restart. The last-seven to old/initial-S supports proof covers
the bounded clocks i,k<T, including clock 0 and T-1; a witness outside T is irrelevant.
One positive final separator is essential for its two-piece A/S bound. The local cap after
excluding the first S family uses four earlier constant runs and the final A/S clock.
Old order requires j>=2. Keep both source keys and suffixes, with no prefix reset.

## H02 initial-S source and the selected target

The first scratch bound for the old supplier's key had the wrong sign. The exact shared
identity is key(z)=4(i-k)S-2d². Combining that with the selected target cancels the
old supplier entirely. The shorter derivation uses the counted initial-S source x
directly, with y=S^d++x and d=h-q. Let R=j+1, C=mass(u), tau=T-j-k,
A=ones(y)+T, S=cntF(y). The two mass balances give d=C+tau and S=C+A-R.
The exact selected-target key is
key(u)-2-4dS+2d²+4CS=-2R².
Using key(u)>=-2 and cancelling the C*S terms after substitution gives
R²+C²+tau²<=2+2*tau*(A-R).
This uses the counted initial-S source and the selected old target, with no condition
on other supplier masses, no second old witness, and no area/headmass assumptions.
Positive R forces tau>0 when A>=R. For gap13, A<=30 and T<=16 give tau<=3;
even dropping C² and tau² yields 196<=98. Thus E580's v/C/four-tuple arithmetic
is unnecessary for gap13 closure. A29 is independently excluded by the head-A cross
cut once actual count gives T<=16. At A30 saturation gives last7 and the initial source.
Boundary audit: k=0 maximizes the bound; k>=T-j forces a nonpositive right-hand
cross term and cannot satisfy the square budget. The formula retains d=0 and
negative tau until the inequality is applied, and it uses the same suffix x in both
mass/key equations.

## H03 gap13 closed at the Nat actual-count core

TopGapThirteen.gap_thirteen_excluded was individually verified with -j1 -M512.
The original counter and target give A in 29..30 and head supply at least9, hence
head free at least4 via the existing checked r3 projection. Then T<=16.
A29 contradicts cross>=4*(A-T)+12. A30 forces last7, and the initial-source
square contradicts gap13. This covers every chosen positive old target mass under
the same hypotheses. Original Intp adapter, exact statement audit and full check
are pending. The first gate was passed. E580's conditional scalar band is not needed.

## H04 joint early clock budget

Question: Can every original final-ray witness whose start has at most j prior A
signs be charged to the same band i<T-j, and can that shared band eliminate gaps
12 through 10? Acceptance: original EndN, same Win, actual prefix A cutoff,
no assumed disjointness and no old history truncation. Stop if the count comparison
requires another independent unknown invariant. Work in symbolic cases, no worker.

E441 already places any old supplier in i+j<T. E452 places a local supplier
with at most j prior A signs in the same band by contraposition. Thus, for any
cut n+Q with Q<=B and cN A n Q<=j, the union of clocks from all starts before
n+Q costs at most T-j. The remaining term is actual EndN from n+Q, justified
pointwise by a surviving original window. It is not a reset to a BlockWord.
The edge retains T<=j and boundary i=T-j, where no such earlier source pays.

For j>=9, original counter A>=2j+3/F<=j and last<=7 give head E>=j-4>=5,
head free>=4, T<=j+3 and A<=j+17. Saturating last7 would force the initial-source
square, but R²>=100>2+2*3*16. Hence last<=6, T<=j+2 and A<=j+16.
For j>=10, if M>j then headfree>=M-2, so T<=7, no early clock.
Cut after the initial S removes all old and initial suppliers, leaving at most5.
Then T<=6, A<=j+15, X<=14, N>=2j-3 and Qcross>=N+2M+L>=40.
The same target bound gives 121+2*40<=197, impossible. Hence M<=j.
If M+L>j, first-two free>=M+L-5 forces T<=10<=j. Cut after the middle S
(second separator) leaves three local families. If M+L<=j, cut after the
third S leaves the final A/S pair, and the early band costs at most2.
Both give last<=3, A<=j+13, X<=12 and T<=j-1. Then N>=j+4, Qcross>=N+3,
contradicting R²+2Qcross<=145. No source A bound is substituted for free.

## H07 gap9 refinement

With M<=j, the joint early budget gives last<=T-j+3. The actual head free
r>=4 and T+r<=j+last force T<j. If M+L<=j the last count is at most1,
incompatible with required E>=j+3. Otherwise A<=j+13, N>=j+4 and
Qcross>=N+2M+L>=2j+6, incompatible with the same target square already at j9.
With M>j, the previous long-first route gives T<=6, last<=5, A<=j+15.
At j9, A<=23 would give X<=13 and Qcross>=36, impossible (172>170).
So A24, head10/last5, N>=18 and Qcross<=46 (C>=2).
If m+s>=3 then Qcross>=18+30+1, impossible; hence m=s=1.
For m1 and M>=5 the second ray's initial S source would require
q>=M-2 and (q+1)^2=2M+1. But (M-1)^2>2M+1.
The second local ray therefore has only clock2. With at most one old
clock, the first two actual rays cost at most4 and the head at most9,
contradicting saturation. The proof leaves arbitrary initial S length and
the old prefix before the chosen target intact. No head enumeration.

H08 monolithic actual high-gap composition exceeded Lean -M512 before kernel
acceptance. Source isolated as STOPPED_FourHighGapExcluded.lean.txt. No root/Audit
registration or resource retry. The new H09 mechanism excludes the first-A
source on the *last* ray by its own key, independently of the earlier H07
second-ray/head cap. In the long-first high-gap branch the same target square
forces j9, A24, N>=18, and m=s=v=1. With all three separators unit length,
a first-A source of positive depth e must satisfy 3e+2L+U=4. Genuine L,U>=1
give at least6. Its absence leaves at most four local clocks after the initial
S cutoff, whereas the actual full budget requires last5. Retain all old sources
via the early-band theorem and derive T<=j before removing them.

H11 actual unit-source composition exceeded -M512 after one repair of the
word-rewrite type error, isolated STOPPED. Independent H12 pruning: no last-six
or initial-S square is needed for the high-gap closure. At j>=9 the seven bound
already yields r>=4. When M<=j, the joint cutoff forces T<j and last<=3.
When M>j, r>=M-2 and last<=7 already force T<=8<=j. The early cutoff then
forces last<=5 and T<=6. This removes the entire last-seven/initial-square
subchain from the high-gap exclusion dependency, while retaining it as an
independent result. The mathematical cases and old histories are unchanged.

H13/H14 high-gap closure accepted with -j1 -M512. The original Nat core and
arbitrary Intp/padded/P2 adapter exclude every j>=9. The independent H12
T<=8 early-band step removes the last-six subchain from this proof. H08 and
H11 remain STOPPED. Existing exact count17/r3 projection are reused.

## H15 delay-sensitive source prefix

Question: Can gap8 be excluded using a delay-sensitive prefix charge and
the actual short-separator head count? Stop at a missing joint source
inequality or if the verified small proof cannot be connected under the cap.
Do not enumerate heads or cut unselected old sources.

Let K=i+j-T>=0 for an actual local source at i<T. Then K<=j-1.
The two-source cross identity, target mass C>=2, primitive old key>=-2,
nonnegative prefix cross and the source's own remaining S count give
(A_prefix-K)^2 >= (j+1)^2+C^2-2 > (j+1)^2.
The negative square branch is impossible since A_prefix>=0 and K<=j-1.
Hence A_prefix>=j+2+K, without an AS-pair assumption. Old sources remain
in i+j<T. Before any actual cutoff with prefix A count <=a, the union of
old and local clocks therefore costs at most max(T-j, a+T-(2*j+1)).
The stronger clock band keeps T<=j and boundary equality. It does not
charge A as free and it preserves arbitrary mixed words.

At j8, E>=11 from A>=19/F<=8. If headfree r<=3, then EH<=r+1,
EL<=7, forcing r3/EH4/EL7/A19/N7. The target square with X10 and
Qcross>=N+3 gives 81+4+20>101. Thus r>=4.
If M>8, M<=r+2 and r<=8 give M<=10. The initial cutoff and
T+r<=8+EL yield T<=8 then EL<=5 then T<=6. The delayed cutoff after the
second S has prior A<=10 and band length zero. Thus EL<=3, T<=4,
A<=21, N>=15 and Qcross>=34, violating the target square.
If M<=8, the ordinary joint cutoff gives T<8 and EL<=3. The delayed
cutoff after the third S rules out M+L<=9 unless EL<=1, which is
incompatible with its forced A19/T<=5 target square. Thus M+L>=10.
Headfree>=M+L-5>=5 gives T<=6. A19/20 violate the square and A21
forces EH10/EL3, N>=15 and Qcross<=30. A first A run M<=2 would give
head<=8, so M>=3. Now I=M*m+(M+L)*s<=15 implies m=s=1.
With these separators the third ray's first-A and middle-S sources
fail the exact key by parity, giving head<10. No fixed head or history
length is assumed.

## H19 head supply floor and final-pair charge

Question: can the delay bound through the whole pre-final-A prefix
force j+1 actual head suppliers, and the third separator cut reduce
all j>=6 to a single final-pair clock? Keep selected target C>=2,
actual final A, original relative positivity and actual free counter.
Stop at a failed exact partition or a missing source inequality.

For arbitrary mixed prefix with N>=2 earlier A signs, checked r3 at
headfree r=0 yields N<=1, hence r>=1. Let E be final-ray supply and
F=r+T-E. Same target gives A=N+T>=2j+3. At the cutoff immediately
before the final A, the residual local ray has empty prefix and no
source, so E<=max(T-j,A-2j-1). The counter implies T+r<=j+E.
If the first term pays, T>=j would force r=0, while T<j is
dominated by A-2j-1>0. Therefore E<=A-2j-1 and head actual
supplied N-r>=j+1. For j>=4 this implies r>=4 via checked r3.

For genuine four-run, W=M+L<=r+5. The cutoff after the third S
gives E<=max(T-j,W+T-(2j+1))+1. If T+r>j+1, the first term
cannot pay and the second forces W>=j+r, contradicting j>=6.
Thus T+r<=j+1 and both bands vanish (W+T<=j+6<=2j+1).
Consequently E<=1, A<=j+11, T<=j-3, and 2j+3<=A.

Gap8 then forces A19/N>=14, and the selected target square fails.
Gap7 has A17 or A18 and both squares fail. Gap6 requires A17,
head10/last1/free6, N>=14 and exact AS I<=10. Head10 forces
first-two supplied5, M>=3, W>=5. If m=s=1, third-ray parity
gives head<=8. Otherwise I=M*m+W*s>=11. Thus j>=6 is paper-closed.
H18 gap8-only scalar validated separately but this stronger route
does not use it. No enumeration and no extra old supplier bounds.

H19–H23 individually accepted. Genuine four-run same-old-target actual counter
at original Intp/padded/zero-fullpositive must have j<=5. H14 j<=8 and the
gap8-only scalar are included, not additional coverage. H08/H11 remain stopped.
The new arbitrary-mixed head-supply floor uses existing checked r3 only to derive
nonzero head free. No unverified r4 certificate is involved.

## H24 gaps 4 and 5 exact saturation

Question: do the exact delayed band and the terminal pair's clock2 force a
third-S source incompatible with the same target? Acceptance: original counted
clock at i<T and literal local source/target formulas, no independent tags.
Stop if a required source cannot be extracted or the exact equations fail.
Budget 0 mathematical worker. Boundary T=1/2 and equality at delay cutoff kept.

For j5, let W=M+L, r=head free, E=last supply, and
D=max(T-5,W+T-11). If E<=1, T+r<=6 and W<=r+5 make D=0 and T<=2.
Only pair clock2 remains, so E=0 and T<=1. A<=15; A<=14 violates the
square, and A15 forces head10 and N>=14, I>=11, also violating it.
If E>=2, T+r>=7, W<=r+5 forces W=r+5 and E=D+1=T+r-5.
Saturation requires 2<T, D<=2 and all i<D supplied. At i=D-1, prior
A must reach W, so the third S (or the pair) is the source. The pair is
outside the band, so it is the third S. Its own positive suffix length q
obeys 2*v*i=(v+1)^2-q^2, forbidding i1. Thus D1/E2/T3/r4/W9, and
the source clock0 yields q=v+1<=s, U=2v+2. Head N-r=5+U<=10
implies v1/U4. A16/N13, I>=2W+M>=19, so C^2+36+2Q>=104>101.

For j4, r=4/F4/E=T. At W<=7 the delayed band plus one cannot pay
T>=2, while T1 lacks pair2. W8 forces D=T-1, T3, and at i1 an
impossible third-S source. Thus W9, head=5+U and U<=5. Every last
clock is supplied. For T!=3 the highest clock T-1 is a third-S source
by the strict cutoff after the second A. T2 impossible; T1 gives U4/v1/s>=2
and the target square contradiction. For T>=4, v>=2T-4. Exact
square and 1<=U<=5/T<=7 exclude all, using I>=W+6 if U=5
(head10); T4/U5 needs that sharper saturation cost. For T3 clocks0/1
can only come from second A and third S after the middle-S cutoff.
Third S cannot supply1, and second A has one clock. Hence third S
supplies0 (U4/v1). At clock1 the delay cut leaves only the final A of
the second run (depth1); its key with U4/v1 requires s^2=10.
These are paper arguments until original actual integration and audit.

H27–H33 excluded all remaining gaps and verified the full original Intp
old-target theorem. H34 full repository check passed 821 jobs and 3621
axiom declarations. E581–585 have exact statement audits. H08/H11 stopped
bytes and the verified superseded prototypes are preserved in the packet.
The initial automated review declined a combined relocation and registration
command; a read-only git ownership check confirmed the listed prototypes
were all untracked and created in this session. The separately scoped,
guarded archive and registration were then approved.

At H35 the local-exploration allocation starts from the final-S target
position, with question and counter bounds in the new hypothesis card.
It is a different target than E457–E482's old-target plus final-S supplier.

H39 final-S all-length and H41 third-A onward all-length original Intp passed
individual verification. H42 supplies the exact third-S profile and the
same-separator factored clock order for every residual q.

H43 short-third-S scalar's broad q/U disjunction reached its 10-CPU-second
per-process cap (exit152; wait4 10.101925 CPU seconds), isolated. No resource
increase. H44 uses a stricter factor classification without q/U cross-product:
the positive difference factor is d=1..3. If R>=3, then c=5,7,8,9 only.
Thus q=3 follows before any U split. The residual (U-3)^2=9-c rules out c7
and fixes U for c5/8/9. This is independent symbolic pruning.

H44 q<=3 symbolic factor module hit kernel -M512. H45 actual candidate
could not import it, so those exact sources are isolated; q<=3 remains
paper only. H46 narrows the question to q<=2 plus arbitrary q satisfying
q+R<=v. q1 is a single adjacent-square gap; q2 uses U1/2/3 and U>=4,
no general small-factor union. The only short q2 branch U3/v2/R2/T3
conflicts with the existing r3 head bound. This is a different smaller
mathematical domain, with the stronger q3 result explicitly pending.

## H48–H56, separate proof and adoption audit

H48 fixed q3 before factoring. H49 verified current Nat and Intp actual gap
for q≤3 or q+R≤v. H50 actual counter band and H51 seven-to-third-S
source extraction stopped after one repair; files isolated. H52/H53 verified
independent source-square exclusions at 512MB. E-590 records the actual
count composition as paper evidence; the last-seven extraction into both
source families remains unformalized.

The H01 clock-order prototype exceeded the one-repair limit. Its last
individual Lean run did pass, but those bytes are isolated and are not
used in root, Audit, or the E-584 claim. E-584 retains only the bounded
source existence theorem, independently accepted after one repair.
E-585 and the all-length E-583 proof do not depend on that prototype.
