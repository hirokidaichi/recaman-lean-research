# M5 / low free4: the first return is already impossible

結論：**M=5・low free<=4を満たす元履歴は存在しない**。前史の深さ・上昇幅・長さを制限せず、元の履歴と全供給元を保持する。E-735は紙上証明の記録（**PROVED-PAPER**）。23時後の利用者指示で全結論をE-743 **PROVED-LEAN**まで形式化した（人間レビュー未）。R以後に高いfreeを用意する前に、必要な深い最低点からRへ戻る段階で矛盾する。

新しい有限部分はE-734のLean証明を使う。ただし、そのLean定理は**明示的なold-source面積条件付き**であり、後続E736/E737は元floor/count/三連A形から条件を生成し、E738はその三連A形を元A3/free2から生成した。E729/E730と元free予算の接続は以下の紙上証明である。旧49型の直接Lean検証はCPU上限でSTOPPEDのまま。有限探索で反例が無かったことを証明へ読み替えていない。一般Mの費用不等式・C1・全射性は未証明。

## Exact original domain

Use f:Nat->Bool, H=Fw f, B(k)=sum(1<=i<=k)H(i), and K_c(k)=B(k)-c*k. Original Win(u,q) means u<q, H(q)=H(u)+1 and K_H(u)(q)=K_H(u)(u). Actual EndN0 includes f(q)=A; original free is A with no source from Nat0. No arbitrary interior origin replaces Nat0.

Let h>=1, T>=h, the first h signs be S, and the original history through T+41 have positive actual deficit at every nonempty prefix. Its tail is Z^5 A, Z=ASSSSAAA, every plateau A actual, and every complete boundary source set at T+8j, j0..5, is{h-1}. Let d=2-h, c=d-4=-h-2 and

    F_low(T)=#{q<T: original free(q), H(q)<=d-1} <=4.

All upper heights, depths, runs, lengths and high free remain unrestricted. No standard-orbit realization is claimed. The two necessary source families from E728 have levels c/c+1 and **normalized key differences** K_c(u)-K_c(T)=24j+15 and K_(c+1)(u)-K_(c+1)(T)=16j+11 for j0..4, with u<T in each family. These are differences in the same original history, not absolute K values or a reset at T. Their full original source sets, including alternatives, are retained.

## 1. The exact original prefix that must exist

Boundary source h-1 gives H(T)=d. E729's floor-visit payment, which is valid for any original floor and does not impose an upper height, gives M<=F_low whenever min(H[0,T])>=-h-4. Therefore a PC5 counter must have m=min(H[0,T])<=-h-5. Let v be its last occurrence and R the first return to d after v. Then H(R)-m>=7 and every height at v<k<=R is strictly greater than m.

E730, with this same original history and all original sources, gives

    p=A[0,v)<=3,     original total free[0,R)<=4.

The total-free statement is only at this PROVED first-return prefix. It is not asserted on all[0,T): arbitrarily many high free after R remain allowed in the parent. E730 proves its chronology through a guarded all-source transport, not a new BlockWord assumption.

The A at v and v+1 are original free. A subtraction at either clock would contradict v being the last minimum. A source for the first would have height m-1, absent globally. A window from height m to the second has nonnegative relative summands and a positive last summand, so has positive area. Thus at most two original free precede v. The first two original A are always free; if p3, the third must be actual, which by the first-three classification means that all three old A are consecutive. Old free counts for p0/1/2/3 are consequently0/1/2/2.

## 2. A new area condition retaining EVERY old supplier

Take any original source u<v of any future target q>=v. Set j=H(u)-m>=0, r=A[u,v), and C=Ar f u(v-u). Let x_1,...,x_r be the heights, relative to m, at the A starts between u and v. The original global floor gives x_i>=0. Before the ith A there are at most i-1 earlier A, so x_i<=j+i-1. The exact walk count gives v-u=2r+j.

Telescoping x(x+1)/2 across this original bridge gives the identity

    C = -j(j+1)/2 + r(1-2j) + 2 sum_i x_i.                 (1)

For completeness, the area of the bridge above m is
`2 sum_i x_i+r+j(j-1)/2`: each A contributes x_i+1 to the triangular increment, while each S contributes minus its starting height. Subtracting j*(2r+j) yields(1). It follows that

    -j(j+1)/2+r(1-2j) <= C <= r^2-j(j+1)/2,
    C == r-j(j+1)/2 (mod2).                              (2)

For p0/1/2, take the union of(2) over0<=r<=p. Every original old source lies in this set. It is harmless if the conditions also admit a source unavailable in the given history: the model will be weaker, never stronger.

For p3 the old A form one consecutive block. An old-source suffix either contains no A, starts within the last one/two A of that block, or contains all three preceded by s S. Its complete allowed area list is therefore

    -j(j+1)/2;
    1-j(j+1)/2                       if j>=2;
    4-j(j+1)/2                       if j>=1;
    9-j(j+1)/2-6s                    for0<=s<=j.           (3)

The j>=2/j>=1 constraints express the two/one A before a source inside the block, whose first height is nonnegative. For the final case, the bridge is S^s A3 S^(j+3-s), with s<=j supplied by the floor. Direct summation gives(3). No other old A is possible; no old alternative source is discarded.

Now write t=q-v, w=seg f v t, h_q=H(q)-m and B_v=Ar f v t. The source height gives j=h_q-1. Splitting the original zero-area window at v gives

    C = (h_q-1)*t-B_v.                                   (4)

Equations(2)/(3)/(4) are exactly the Boolean `oldAllowed` premise in E734. E736 now checks(1)/(2) in original f/Fw/Ar/cN vocabulary; E737 checks the entire suffix classification and crossing-window transport, with the literal-three condition produced by E738 from original A3/free<=2. They are valid for EVERY original crossing source and any future height; no first-hit height ceiling or future-length cutoff is an assumption here.

## 3. A weaker model still cannot rise seven levels

At every future A, admit supply when either a literal local window starts at/after v, or its C/j satisfy the old-area list. Unlike the original history, the model even permits mutually incompatible old sources. Every original actual A is admitted by(2)–(4), while local sources are the unchanged literal windows. Therefore

    relaxed paid free <= original total free,

starting with the correct old paid amount0/1/2/2. This inequality direction is essential. No admitted phantom source is called a realized original supplier, and original free tags are never replaced by the relaxed tags in the parent.

The new checker has only four initial p-cases. Its151-node finite certificate is accepted by ordinary Lean kernel reduction. More importantly, `recovery_bound_of_old_area_admission` proves by induction on an ARBITRARY original future length K that these checked states contain every original continuation satisfying the explicit source-admission premise, old paid budget, total original free<=4 and strict post-v floor. It concludes

    H(v+K) < H(v)+7.

The14 in the checker is certificate fuel, not an assumption K<=14. The proof propagates a checked state with relaxed paid<=original free at every original step. A source before v uses the explicit old-area premise; one at/after v uses the existing original `localSupply_seg_iff`. No resource-limited or unchecked computation is part of the Lean proof.

Apply this theorem with K=R-v. Section1 supplies the free budget, p and strict floor; section2 supplies every old-source admission. It gives H(R)<m+7, whereas H(R)-m>=7. This contradiction excludes the deep return and hence PC5.

## 4. Stronger local consequence and sharp boundary

The argument proves the following paper statement in the original initial-S/positive-prefix setting:

    H(T)=2-h and F_low(T)<=4  =>  min(H[0,T])>=-h-4.

Together with E729's floor-visit payment it gives M<=F_low for every supplied PC plateau whose F_low<=4, and in particular excludes M5/low4. A counter to the general cost inequality must now have M>=6 and F_low>=5. This is a fixed-free-budget result; it is not a uniform arbitrary-rank charge or a resolution of C1.

The boundary is nonvacuous. S8 AAAA S AAA has four original free, at clocks8,9,11,14; supplied A10/13/15 have sources7/6/12. It rises six levels from its last minimum. With parameter h4 it ends at2-h and attains the bound min=-h-4. Appending one A reaches seven levels but costs a fifth free; with parameter h3 this is exactly a deep return at min=-h-5. Thus the distinction between six and seven levels is real.

## Falsification, failed method and general results

- O4, the stronger total-A<=7 claim under original free4, is REFUTED by `SSAAASSSSAAAASA` (A8/free4, all original positive prefixes). Its full sources passed an independent verifier. It is not a PC5 counter.
- Exact49-profile search closed at540 nodes. The all-source profile coverage has a complete paper argument and380 independent source comparisons, but the direct Lean certificate hit its fixed60CPU cap. That packet is STOPPED and excluded from root/Audit. It was not split or given more resources.
- The new global-floor triangular identity(1) and the contiguous-three spectrum(3) changed the mathematical model. Its4-case relaxed query closed at151 nodes; independent bridge discovery/holdout and62 original-old-source admissions/all151 branches passed. The new Lean module had one interface repair (Boolean lemma name,0+n normalization, literal sign arithmetic), then passed at0.913CPU/1.093wall seconds under the SAME60CPU/90wall/-j1/-M512 cap. It is not the stopped certificate retried with different tactics.
- E732 independently proves the arbitrary-depth old-source radius2p+b, complete source-window transport and preservation of the original old free ledger. Its sharpness families are PAPER; its general free-to-p producer is not known.
- G0, the stronger claim that no new low free after R forbids useful late low keys regardless of old stock, is REFUTED. The closed preloading recurrence gives positive original histories with no free after R and positive keys at both low heights. The m8 example has offsets6/19 and39355 old low free, so it does not satisfy the budget4 or the exact parent inventory. All-m proof is PAPER, two exact certificates and independent tail-source audit are COMPUTED. This explains why the old stock cannot be ignored.

## Audit, provenance and next decision

Baseline08fc48f20e395adc56a1ab2c8a3dac223560723d. Frozen protocols, exact source/input hashes, original full-source certificates, guard/CPU/wall receipts, stopped bytes and separate semantic audit are in[data/post_return_high_free_20261117](data/post_return_high_free_20261117/SEMANTIC_AUDIT.md). E734 is conditional PROVED-LEAN; E736/E737/E738 now check the section2 source producer and original triple classification. At the23:00 handoff, E729/E730 and the remaining original budget/parent connection were PAPER. The later user-requested formalization E739–E743 now supplies those dependencies and the full M5 conclusion in Lean; human review remains pending. Full repository validation/publication receipts are recorded separately.

The useful next mathematical question is how the old-area/free interface changes with a fifth paid free; do not automatically enlarge the stopped exact table, rerun the old SMT/generators, or assume a uniform M bound from this case. The current user scope remains M5. Generalization progress comes from the source-preserving interface and the G0 mechanism counter, not from increasing M or counting modules. The25-minute distinct mechanism reservation was observed for25m02s, with exact clocks in DISTINCT_GENERAL_PHASE.json; nominal allocations are not elapsed-work claims.

## Targeted assumption audit after the formal producers

Dropping the contiguous-three restriction while keeping only the general r<=3 floor envelope admits the exact relaxed word `AAAASAAASSASASASAAA`, reaching height7 at relaxed paid4. At future clock6 it requests j3/C1, inside the generic area/parity interval but outside EVERY contiguous-three case (tri3=6; permitted C=-6,-5,-2 or3-6s). The later incompatible admissions are recorded too. Thus retaining the original old-A chronology is essential to this proof. This is a counter to the deliberately weakened source model, not an original PC5 history; no common original past is asserted. Both the weakened witness and the original rise6/free4, rise7/free5 boundary words passed separate forward/reverse source checks. Frozen protocol/output: CONTIGUITY_AUDIT_PROTOCOL.md and contiguity-audit-summary.json in the packet.


## Post-deadline formalization update

The explicit follow-up request to formalize and commit produced E739–E743. The first24-key family alone forces five prior low free from raw initial-S/boundary-window/literal-plateau assumptions, so the full simultaneous24/16 parent with low4 is excluded. The endpoint floor argument also drops the positive-prefix premise. No extra finite search or stopped-certificate restart was used. See [formalization card](HYPOTHESIS_CARD_2026-11-17_M5_FORMALIZATION.md) and [separate semantic audit](data/m5_formalization_20261117/SEMANTIC_AUDIT.md). This does not add another independent generalization advance to the evening unit.
