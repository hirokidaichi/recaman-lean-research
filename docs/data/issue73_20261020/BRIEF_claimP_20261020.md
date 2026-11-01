# Briefing: Claim P / Conjecture SC (2026-10-20 session)

Repo: /Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research  (DO NOT commit, DO NOT edit tracked files;
write your scripts/notes under your own folder in the scratchpad
/private/tmp/claude-501/-Users-hirokidaichi-ghq-github-com-hirokidaichi-recaman-lean-research/cbe2276f-5113-5a8c-b36d-e20197a7b6e4/scratchpad/<your-name>/ )

Background reading (only what you need): docs/HYPOTHESIS_CARD_2026-10-03_GENERAL_LAG_CLOSURE.md items 8, 11-16;
docs/RESEARCH_HANDOFF_2026-10-03.md. Existing probes: experiments/issue73_20261003/subagent_probes/ (os/auto.py = exact
left-to-right automaton, see E-368).

## The model (line model, no periodicity)

sigma : Z -> {A=+1, S=-1}. Walk F(t) = sum_{c<t} sigma(c), so F(t+1) = F(t) + sigma(t). "Clock c is S" means F(c+1)=F(c)-1.

A *P2 window* for an A-clock b (sigma(b)=A) is W_b = [t_b, b-1] (length L = b - t_b, necessarily L = 4m+3) with
  (mass)   sum_{c in W_b} sigma(c) = 1           i.e. F(b) = F(t_b) + 1
  (moment) sum_{c in W_b} sigma(c) * (b - c) = 0  i.e. sum_{u=t_b+1}^{b} (F(u) - F(t_b)) = 0,
equivalently: F(b) = h_b + 1 and the mean of F over (t_b, b] equals h_b := F(t_b). (Equivalently sum sigma(c) c = b:
"signed centre of mass sits at b".) Minimality of the window is NOT needed for anything below (do not assume it unless you say so).

A *closure* (finite) is a finite set M of members, each with a chosen P2 window W_b, and own : M -> S-clocks with
  (M1) own(b) in W_b, sigma(own b) = S;  (M1') own injective;  (M2) every S clock in the union of the windows is own(b) for some b.

Known closures: isolated AAS (newest-first word AAS: window [b-3,b-1] = S,A,A oldest->newest, own(b)=b-3), and the
"w1 triple": members v (AAS, owns v-3), v-2 (lag 7 word, window [v-9,v-3] = S S A A A A S oldest->newest, owns v-9),
v-5 (AAS, owns v-8). Disjoint unions of these are closures.

## What is known (Lean-proved unless stated)
* E-362: for a P2 window, sum over its S clocks c of (F(c) - h_b) = m  (L = 4m+3); sum over A clocks = -(m+1).
  Hence a window all of whose S lie at height F(c) <= h_b is AAS.
* E-363: nested P2 windows differ in length by >= 8; leading m S's force L >= 4m+3; windows shifted by <= 3 cannot coexist.
* E-364 suffix Hall: #S[z,y] <= #M[z+1,y+1] in a component [x,y] with newest member y+1, so F(z) <= F(y+1)+1.
* Prefix Hall: members b <= z own S's in [x, z-1] injectively.
* E-366/E-367: Theorem R / R': if a member w's owned S lies in no other window (w is *private*), then M \ {w} is a closure;
  if M \ {w} is a disjoint union of AAS and triples, then so is M.  =>  The classification
  "every finite closure is a disjoint union of isolated AAS and w1 triples" (which gives G1 for all lags) is reduced to
      **Claim P: every nonempty finite closure contains an S clock covered by exactly one window.**
  (Inductive hypothesis may be used: every proper sub-closure is a union of AAS/triples. Back-closure: for any x, the set of
  members reachable backwards along r -> m := "own(r) in W_m" is a closure; a subset is a closure iff its complement is
  forward-closed. So a minimal counterexample has no private member, contains a long (non AAS/w1) member, and a strongly
  connected core K with |K| >= 2.)
* Conjecture SC (stronger, from the automaton E-368, verified for all closures with window length <= 11 with no limit on the
  number of simultaneously open windows, and <= 15/27 with <= 8/4-6 open windows): in every finite closure every member owns
  the OLDEST clock of its own window (which is therefore S). Equivalently E(z) := #{b : t_b < z <= own(b)} is identically 0.
  Lemma OS: the oldest S of a component is covered once (<=> E(s0+1)=0).
* Relaxing the moment condition to a one-sided inequality makes Claim P FALSE ({0:AAS, 1:AAASSSA, 2:AAAASSS} newest-first,
  moments 0,-2,-8): any proof must use moment = 0 exactly (both signs).
* Counting identity: sum over covered S of (cov(s) - 1) = 2 sum_b m_b; so failure of Claim P needs sum m_b >= |M|/2.
* Purely local/bounded-region arguments cannot work (card item 9(a)).
* Under SC every owned S sits exactly at the owner's base level (F(own b) = h_b).

## Deliverable
A final message (you cannot write REPORT.md in the repo) with: precise statements you claim, which are PROVED (full proof
written out, checkable), which are computational (script path + command + output), and which are conjectural. Mark every
proof step you are unsure about. Negative results (approaches that provably cannot work, counterexamples to sub-claims) are
valuable — give the explicit counterexample. Keep CPU usage to at most 2 cores. Time budget: about 2 hours wall clock.

## UPDATE (20:10): round-1 results — the new target is Conjecture H (line capacity)

* Fix p. An A clock b is *endable from p* if some P2 window [t, b-1] has t >= p. e_p(k) = #endable clocks in [p,k-1],
  s_p(k) = #S clocks in [p,k-1].
  **Conjecture H: e_p(k) <= s_p(k) for all p < k.**  Verified exhaustively for all sign strings of length <= 34
  (scratchpad/levels/hall.c; parent re-verified independently to length 24+). H for intervals implies the project's central
  conjecture E-070 (periodic |U| <= |D|: lift to [0, Kp), K -> infinity). So H is a strengthening of the main open problem.
* Given H, Hall's condition holds for every family of P2 windows with distinct ends, so a closure is exactly a family with
  #windows = #S(union), and every closure component is an equality case of H (saturation: every endable clock is a member).
* **Conjecture EqClass**: if e_p(k) = s_p(k) and clock k-1 is endable, then sigma[p,k-1] parses as
  (SAAA | SSAAAASAAA | A)*, the endable clocks are exactly the members of these blocks, each with exactly one window from p
  (lengths 3/7). Verified for length <= 30 (any first clock) — parent re-verified to 24.
  H + EqClass => classification of closures => Claim P => G1 for all lags.
* Prior Lean proofs of periodic special cases: E-071 Recaman/ShortPeriodicSupply.lean (lag <= 7, via an explicit potential on
  the 7-bit shift graph with `decide` on local inequalities, telescoped: `potential_step`, `chargeSum_le_potential`);
  E-080 Recaman/LagElevenPeriodic.lean (lag <= 11 sum, injections phi7/phi11); E-128 Recaman/LowSSEndpoint.lean +
  Recaman/LowSSPeriodicSupply.lean (windows with ssCount <= 1, all lags: S-ended prefix -> endpoint injection).
* Refuted: level-refined H (SSSSSSSSSAAASSSSAAAASA at level -8); every simple canonical injection endable -> S inside the
  minimal window (oldest S, last S, last S at base level, greedy within level ...), see scratchpad/levels/inj*.c.
  Moment relaxations (<= or >=) break Claim P. Additive per-window monovariants for SC cannot exist (scratchpad/monovariant).
* Core/tail reduction for a minimal counterexample (scratchpad/oldest, scratchpad/monovariant): cores with <= 5 S's
  do not exist (lag-uniform finite check).

## UPDATE 2 (20:35): round-2 results
* PROVED (Lean E-371): Clean Window Theorem. Minimal window [t*,b-1], level h=F(t*), P_h(u)=sum_{w<=u}F(w)-h*u, v=P_h(b).
  b clean <=> every h-visit u in (t*,b) has P_h(u) < v. Clean => sigma(t*)=S; two P2 pairs sharing a start => newer unclean.
  => b -> t* injective on clean endables => H on intervals whose endables are all clean. Lean also: ssCount<=1 or depth-1
  minimal windows are clean (E-372). Paper (hpot): level-refined H holds for windows of depth<=1 (walk >= h-1) or height<=1
  (walk <= h+1) — Theorems A/B/U in scratchpad/hpot report; (d,c) state reformulation: per start t, d=F(k)-F(t),
  c = area - d(d+1)/2; A: (d,c)->(d+1,c); S: (d,c)->(d-1,c+2d-1); gain iff A and (1,-1) present.
* COMPUTED: H restricted to windows of length <= 27 holds for ALL strings (Bellman potential certificate; parent re-verified
  independently). Additive potentials over open starts provably cannot work (LP Farkas). Level-refined H false at depth 2.
* hunclean: Lemma 0 (parity: an h-visit u with P_h(u)=P_h(b) gives a P2 window [u,b-1]); Lemma 1: r_b := last h-visit u<b with
  P_h(u) >= v is an S clock (r_b=t* iff clean) but r is not injective (SAAASSSSAAAASA). Computational (all strings <= 32/34):
  U1 matching: clean b -> S c in window with F(c) >= h_b, unclean -> F(c) >= h_b+1. U3: clean exactly at own level F(c)=h_b,
  unclean F(c) >= h_b.  LEVEL-TRUNCATED H: for all p<k and integer g:
     #{clean endables with h_b >= g} + #{unclean with h_b >= g-1} <= #{S c in [p,k) with F(c) >= g},
  and also e_{>=g} + u_{>=g} <= s_{>=g}. (g -> -inf recovers H/H+.) Downward truncation fails. All obstruction cores to
  extending clean->t* (54 up to length 34) begin with SAAASSSSAAAA (unclean window SAAASSSSAAA).
  Files: scratchpad/hunclean (upd.c, hg.c, hg3.c, ext.c), scratchpad/hinduct, scratchpad/hpot.

## UPDATE 3 (20:55)
* H+ is FALSE (length 34: SAAASSSSAAAASASSSAAASAAASSAAAASAAA, e=11,u=3,s=13). H holds there.
* H restricted to windows of length <= 31 verified for all strings (parent, Bellman on finite state graph).
* htrunc (scratchpad/htrunc): Lemma A (excursion gadgets: an excursion below y can be replaced by any excursion with the same
  (n = half-length, Q = area) without changing anything relevant at thresholds >= y+2). Lemma B: for unclean b, r := last
  h-visit in (t*,b) with Area(t*,r] >= 0 (then > 0): clocks r, r+1 are both S (F(r+2)=h-2). Lemma Q: q := last S before r with
  F(q)=h+1 exists, t* < q < r, and every P2 window starting at q has depth >= 3.
  DF2 (verified <= 31): depth-<=2 unclean endables inject into "deep-forced" S clocks c in W_b with F(c) >= h_b+1 (after c the
  walk reaches F(c)-3 before F(c)+1, within [c,b]); deep-forced S's are never starts of depth-<=2 windows, so DF2 + Clean Window
  Theorem => H for depth-<=2 endables (this class contains SAAASSSSAAA and the w1 triple). D2-local verified <= 34.
  U1-R2 (verified <= 31): depth<=2 cleans -> t* rigidly, depth>=3 cleans -> S in W_b with F >= h, uncleans -> S in W_b with F >= h+1.
  Canonical non-greedy rules for uncleans are all non-injective; only greedy/full matching works.

## UPDATE 4 (21:25)
* DF2 is FALSE at length 32 (ASASASASASASSAAASSSSASASAAAASASA).
* NEW COMPUTATIONAL THEOREM (E-374, audited): for every L <= 31, H_L holds and EqClass_L holds for ALL spans
  (equality words = V-tight paths in the finite state graph of H_L; regular-language inclusion check, scratchpad/parent/eqclassL.c),
  and periodic tight cycles are block words for L <= 27 (tightcyc.c). Consequences: every finite closure whose windows have
  length <= 31 is a union of AAS and triples; G1 holds for tight B whose member lags are all <= 27 (all periods).
  So a counterexample to H, EqClass or Claim P must involve a P2 window of length >= 35.
* The minimal potential V_L has max <= 5 for L <= 27; the V-tight product grows ~x3.9 per +4 in L.

## UPDATE 5 (21:35) — H reduces to EqClassW (pump, parent-verified)
* B = {SAAA, SSAAAASAAA, A}. EqClassW(p,n): if [p,p+n) is tight (e = s) and its last clock is endable, the word is in B*.
* Density Lemma: any suffix v of a word in B*A* has 10·#S(v) <= 3|v|; hence no such suffix is a P2 window.
* Theorem 1: H(p,n) follows from H(p,<n) and EqClassW(p,<n). [violation at n => [p,p+n-1) tight and p+n-1 endable;
  last endable before => tight prefix = block word, then only A's; the window of p+n-1 is a suffix of B*A* — contradiction.]
  So H for all lengths <= EqClassW for all lengths; everything reduces to the INDUCTIVE STEP of EqClassW.
* Theorem 2 (minimal EqClassW counterexample x = σ[p,k), tight, k-1 endable, not a block word, H(<=n), EqClassW(<n)):
  [p,k') has slack 1 where k'-1 = previous endable, and the clocks between the last two endables are all A.
* Theorem 3: for every cut q in (p,k), X_q := #{endables b >= q all of whose windows (from p) start before q} >= max(d(q),1),
  where d(q) = s_p(q) - e_p(q) >= 0. x = w·A^i·y with w a block word, y starting with S at the last zero k1 of d, d > 0 on
  (k1,k); every block boundary in w is straddled by some window ending in y. If σ(p)=A some endable is unclean.
* DL4 conjecture (all strings, n <= 30): every string of length >= 4 has a deletion of 4 consecutive clocks not decreasing
  e - s. DL4 => H. Canonical deletion rules all fail.
* Deleting a factor u keeps a containing window P2 iff Δ(u)=0, |u| ≡ 0 mod 4 and its area relative to that window's base is 0;
  two windows with different bases containing u cannot both survive.

## UPDATE 6 (22:00) — eqstep results (scratchpad/eqstep)
* Phi(q) := #{endables b with tau_b < q} - #S[p,q) = slack(q,k) - slack(p,k) = X_q - d(q); Phi(q+1)-Phi(q) = #{tau_b = q} - [S at q].
  tau_b = start of b's minimal window (intrinsic). On a tight x, Phi >= 0 (H on suffixes).
* Lemma BW: in w in B*, endables = block members, tau bijective onto S clocks, all clean, Phi = 0.
* Lemma C: x = S·w' (w' in B*), b a non-member A of x with [0,b-1] P2 => b=3 (x=SAAA·B*) or b=7 (x=SSAAAASAAA·B*).
* Theorem R: for tight x with last clock endable: x in B* <=> Phi ≡ 0 <=> all suffixes tight <=> tau bijective endables -> S.
* Theorem CC: a minimal counterexample to EqClassW has an UNCLEAN endable (else Clean Window Theorem gives Phi <= 0).
* Straddlers (tau_b < k1 <= b in x = w A^i y) are unclean.
* Dichotomy for a minimal counterexample: (A) tau_{k-1} > p and Phi > 0 on (p, tau_{k-1}]; then some unclean endable b != k-1 has
  minimal window starting at p; or (B) tau_{k-1} = p: x is ONE minimal window plus its end clock (n >= 36).
* Conjecture PHI (all strings <= 28): slack(q,k) <= 2·slack(p,k) for every q (=> EqClassW => H).
* Suffix monotonicity fails (SAAASSSSAAAASAAAAASAAA); slack-1 words have no simple grammar.

## UPDATE 7 (22:10) — CASE (B) CLOSED, case (A) open
* Theorem B (caseB, parent-verified, scratchpad/caseB): x = σ[p,k) tight and [p,k-2] a P2 window of k-1 (minimal or not),
  H on proper subintervals + EqClassW on shorter tight intervals (starts p and p+2 only) => x = SAAA. Proof: exactly 2
  non-endable A's => x = S^j AAA..., all later A's endable; prefix H => F <= 2; F=2 => prefix SAAA (j=1); last minimum is at j;
  no A at levels -j+1, -j+2 after j+2 (dip lemma: every P2 window dips strictly below its base) => F >= -j+3; j=1,2,3 contradict
  area / F(L-1)=0; j>=4: H at start 2: the clock before the first time F=1 has all windows starting in {0,1}, so d_2 = 0 there;
  the tight interval from start 2 is a block word starting S^{j-2}A — impossible (SSS for j>=5; triple forces F(12)=2 for j=4).
* caseA (scratchpad/caseA): Lemma 1 (endable b != k-1 with tau_b = p: slack(p,b+1) >= 0, = 0 only for SAAA; for the newest b*,
  slack(p,b*+1) >= 1 and X_{b*+1} >= 1); Lemma 2 (b* unclean, window length >= 11). The case-(A) PATTERN (last endable,
  q0 = tau_{k-1} > p, slack(q,k) > slack(p,k) for all q in (p,q0]) forces slack(p,k) >= 4 for n <= 30 (>= 5 at 31,32) without
  assuming tightness — huge margin. Refuted: OW (length 31), G' (n=27), tail-pays.

## UPDATE 8 (22:25) — case (A) reduced to the Straddler Lemma (caseA2, scratchpad/caseA2)
* Notation: c = k-1, minimal window [q0,k-2], y = σ[q0,k), h2 = F(q0), d(q) = s_p(q) - e_p(q), a_y = #A in y not endable from p,
  X = #A b in y endable from p with tau_b < q0 (straddlers). Identities: slack(p,k) = d(q0) + a_y - 2; slack(q0,k) = a_y + X - 2;
  Phi(q0) = X - d(q0). Band identity: F(q) - h2 = d(q0) + a_y[q0,q) - d(q) on [q0,k].
* Theorem A*: if a_y + d(q0) <= 2 (+ induction hypotheses) then y = SAAA. (Theorem B = A* with q0 = p.) A* kills case (A).
* A* <= STRADDLER LEMMA SL: if a_y + d(q0) <= 2 then X <= d(q0). (Then slack(q0,k) <= 0, y tight, Theorem B applies to y.)
* Data (all strings <= 28): A* holds; X > d(q0) forces a_y >= 4. (a_y,X,d) with a_y+d <= 2 only (2,0,0), (1,1,1).
* b* lemma: in a minimal counterexample b* (newest endable with tau = p) satisfies b* >= q for all q with d(q) = 0; if d(q0) = 0
  then b* > q0 straddles q0 and F <= h2+1 on [q0,b*]; the prefix w = σ[p,q0) is a block word when d(q0) = 0.

## UPDATE 9 (22:45) — SL partial (scratchpad/straddle)
* Reductions: a_y + d <= 2 forces a_y + d = 2 (tight); cases (a_y,d) in {(2,0),(1,1),(0,2)}; SL <=> y tight (then Theorem B on y).
  Cap: F(q) <= h2 + 2 - a_y[q,k) on y. d=0 => w = σ[0,q0) is a block word.
* d=0 PROVED for j <= 3 (y = S^j AAA z): Lemma 1 (block-suffix positivity: D(t) = F(q0)-F(t) >= 1 and A1(t) = area(t,q0] >= 1;
  D=1 only for suffix "A"); Lemma 2 (A in y at level <= running-min+1 is not endable); Prop 3 (y = S^j AAA z, non-endables are M,
  M+1, F >= m+3 after M+3); straddlers have 1 <= D <= j-2; j=1 => y=SAAA; j=2,3 impossible; j>=3 => F <= h2+1 on y.
* OPEN: d=0 with j>=4 (Theorem B's start-(q0+2) port blocked by early straddlers below h2, e.g. y-prefix SAAA|SSSSAAAA where the
  4th A has window SAAASSSSAAA straddling q0 — such prefixes never complete); d=1 (Lemma 2 false: SSAAAA|SAAA, straddler SSAAAAS;
  data: only triple end); d=2 (a_y=0, data: never completes).
* DFS (dfsall.c): all prefixes w with prefix-H, d <= 2, |w| <= 15 & |y| <= 80 (|w| <= 17 & |y| <= 44): 0 violations of A*/SL.

## UPDATE 10 (22:50) — straddle2
* Lemma TS (verified all strings <= 30, sharp): b1 < b2 consecutive A clocks with only S's between, both endable from p; q* = start
  of the S-run before b1 (σ[q*,b1) = S^j, σ(q*-1) = A). Then slack(p,q*) >= 3. Generalization: r consecutive endable A's after q*
  (only S's between): min slack 1,3,4,6 for r = 1..4. TS => SL case d=2 impossible.
* Proved: Lemma 1 (block-suffix positivity with an A tail: σ[p,e) = β A^a, β in B*: D(t) >= 1, area(t,e] >= 1); Lemma 1' (then
  after e an S-run then A: that A has no P2 window from >= p); TS1 (b endable with only S's in [e,b): slack(p,e) >= 1);
  Lemma M (in a block word, between two members there is a non-member A); TS-partial: slack(p,q*) >= max(1, 2-j, 3-j-i)
  (so TS holds if i = j = 0). Case d=2 impossible when y starts with AA; in case d=2, F <= h2+1 on [q0,k-1].
