# Sharpness mechanism, frozen before checking its concrete instances

This is an exact parameterized counterfamily to decreasing the new source radius, not a restart of the stopped G0 corpus or source generator. It is not a low-free4 or PC5 counterexample. Source0 below means the source clock before an optional initial S padding; all original alternative sources remain allowed.

## Unrestricted cut, every p,b with N=p+b>=1

Word W = S^N A^N (AS)^(N^2-1) A; target is the next A at q=length(W). Take u0 and v=N+p. Then A[0,v)=p, H(v)=-b, H(q)=1, v-u=2p+b. Area(S^N A^N)=-N^2; each AS at height0 contributes1, and the final A contributes1. Hence the whole source window has area0 and mass1. The radius is attained for every p,b except the trivial p=b=0. Appending the target A makes actual supply explicit. If original positive prefixes are wanted, prepend h S signs with h greater than the total A count in W A; the existing initial_S_positive bound supplies every original positive prefix. All original windows shift, old A remains p and the exact old-source distance is unchanged.

## Last global minimum and bounded future height, p>=0,b>=2

Let C=p^2-b^2+1, D=2b-3>0, k=max(0,ceil(C/D)), l=kD-C>=0. Use

    W = A^p S^(p+b) A (AS)^k A^(b-1) (AS)^l A.

Again u0, v=2p+b, H(v)=-b and p old A. v is the last global minimum; every later height is strictly greater than-b, up to target height1. The first loops are at height-b+1, contributing-D each; the later loops are at0, contributing1. The path without loops has areaC, so total area C-kD+l=0 and mass1. The source attains2p+b. Initial positive padding h S as above gives original positive prefixes and initial S while keeping v the last minimum. All future A start at height<=0 (relative to u), below the target ceiling1. Thus even those additional geometric assumptions cannot generally decrease the radius. This does NOT impose original free<=4.

Local relevance: p3,b5 gives k0,l15, old word A3 S8 and future A5(AS)^15 A. It attains the11-clock old-source radius for the low6-above-floor target. Its many low free prevent promotion to the parent counter; the point is that full old-source retention really is necessary before using the free budget.

Discovery parameter pairs for first family: (0,1),(1,0),(3,5),(4,2),(7,3). Frozen holdout: (2,7),(8,4),(11,6). For minimum family use the same pairs only when b>=2. Check every source at the target, claimed source/window/height/oldA and original positivity after padding by A(W A)+1. Independently enumerate original free to disclose that no low4 parent claim follows. Budget one query per split,3CPU/6wall, no larger retry; script/input hashes before run. Complete symbolic formulas above, not finite instances, support the all-parameter PAPER claim. Kernel formalization of the family is separate from the already checked radius theorem.
