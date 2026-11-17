# Old source radius: paper proof and separate semantic audit

Candidate frozen H-OSR, first Lean module compiled21:05:18 JST, first attempt,0.557CPU/2.010wall seconds under10CPU20wall/-j1/-M512. Required full repository audit is still separate. Discovery1023 words/176725 eligible conditions; frozen holdout1024 words/250518 conditions. Every complete source set equals its literally shifted suffix set. Invalid variants all fail at SAA (take next A as target sign): omitting the height hypothesis, replacing2p by p, and reducing the radius by1. Both finite queries STOPPED after the declared one-shot ranges.

## Proof independent of computation

Let u be an original source, u<=v. Put a=A[u,v), z=S[u,v). Then H(v)-H(u)=a-z and v-u=a+z, so v-u=2a+H(u)-H(v). The source equation is H(u)=H(q)-1. Since H(q)<=H(v)+b+1 and a<=A[0,v)<=p, the distance is at most2p+b. If u>=v the cut inequality is immediate. This proves that EVERY original source lies at or after s=max(0,v-2p-b), without any hypothesis on old minimum, original positivity or future additions.

For every u>=s, the relative walk heights in [u,u+k] under g(i)=f(s+i) are exactly those under f: subtracting H(s) cancels in each H(u+j)-H(u). Thus both the mass equation and zero area, and therefore each Win, are equivalent. Forward source transport additionally uses the proved lower bound u>=s; backward transport simply restores the identical original window. No source is created or lost. The target sign is copied, yielding EndN equivalence. For future A clocks satisfying the ceiling, the free indicator is therefore identical. Summation yields `future_free_transport`; splitting the ORIGINAL free count at v yields `original_free_ledger`. This keeps all old free charged, even when their markers in a newly based comparison prefix would differ.

## Auditor pass: logical strength and boundaries

The stated theorem is valid even without v<=q or a minimum at v; neither assumption is introduced to manufacture substance. Only the mass component of Win is needed to exclude old starts; its area component remains essential in the exact source equivalence. Original positivity is neither assumed nor transported. Source radius may exceed v, in which case s0 is the identity; the intended E730 p3/first-rise7 consumer can instead erase arbitrarily long old prefixes. Future A count and length are unrestricted. The future height premise is derived from the FIRST-hit question, not an upper bound imposed on the full research history.

The suffix operation never erases an internal neutral word (E707) or shortens an S run while retaining an unchanged old prefix (E726/E727). It discards only clocks proved not to be sources for any queried future A. The old original history and old free ledger remain authoritative. Old free is NOT identified with the newly based comparison prefix free; no new BlockWord or positive margin is claimed. These differences are the exact reason the known source-loss countermodels do not refute this transport.

Relative to E722 (global initial-S) and the older BlockWord/depth radius, this admits arbitrary old sign histories with only their old A count bounded and preserves every future source under a target-height band. Parameter p is not replaced by old free. The useful producer is presently E730 p<=3; a general-free producer is still missing. This is a conditional history-preserving reduction, not M<=F_low or C1.

## Validation setup event

The first vacuity invocation returned `error: module Recaman.OldAdditionSourceRadius not imported` because the probe imports the repository aggregate. This is a harness-setup error, not a clean report or mathematical failure. The module had already compiled. Add the ordinary aggregate import and Audit declarations, rebuild the aggregate, then invoke the required lint again; no theorem, resource or tactic repair is made. Keep this event in the final receipt.
