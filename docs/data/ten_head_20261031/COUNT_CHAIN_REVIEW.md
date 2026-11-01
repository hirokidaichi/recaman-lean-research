# Separate count-chain review during final preservation

This checks the already adopted source/count proof, rather than proposing a new bound.

Mass-two restrictions: write R=j+1 and C=2. Target suffix AA has key0, SAAA has key-2. The shared target equation gives
`B=4S+4v-v²+R²+key/2`.
Upper band and v1/2/3 give R²<=2S+2; the internally supplied S<=16 and R>=5 force R=5. The actual head supply<=10 plus headfree<=fullfree<=j gives S<=j+10=14. The target equation and upper band give S>=12. Word moment parity is B≡S mod2, not an independent old-source parity choice. Thus v1/3 yield S/B=(12,76),(13,79),(14,84); v2 yields (12,76),(13,81),(14,84). This audits all nine output groups. None is assumed on the actual theorem's input.

Mass-two local charge: v1 has firstA/secondA merging into clocks0/2 and no initialS source; one middleS family remains, hence <=3. At v2 the initialS clock0 also merges; secondA and middleS cost at most one each, hence <=4. At v3 without the initialS family, baseline0/2 plus firstA/middleS/secondA is <=5. If an initialS family occurs it forces B=6S+1, hence S13/B79 in the target-derived groups; that same head forces the secondA source to clock0, leaving the same total5. These are source-family upper bounds; they do not assert every permitted clock is supplied. Since T=v+3, every case has at least one actual last-ray free after all old suppliers are excluded. A>=12 in the head gives headfree>=4 by the existing r3 count. Disjoint addition contradicts actual fullfree4.

Mass-one small head: the target/word moment constraints leave S7/B39/v2/R5/T6. The head's integer moment is I=M(m+s)+Ls=5, which supplies h>=M+2. The firstA source lands at clock0, so the local count drops from the generic v2 budget5 to4. Existing r3 count gives headfree>=3 at A7 and the last A6 contributes >=2. This is the adopted analytic chain. The abandoned five-word/30cell layout is not a dependency.

Lower4 audit: same target at B=4S+4 supplies C1/v2/R²=2S+4. Word parity makes S even and R even; counter R>=5 implies R>=6 and S>=16. Source-family local<=5 and the common-prefix old<=1 bound give last actual supply<=6. Head supply<=10 gives headfree>=S-10>=6. Here T=j+2, so head plus last actual free is sufficient with room to spare. Old supply is not erased; the E480 applicability witnesses show why retaining it matters.

Small-counter supply: the R>=5 restriction used above is not a theorem premise in the adopted full-gap theorem. If fullfree<j+1 and fullfree<=3, the existing r3 A<=2free+1 contradicts E457's actual A>=2(j+1)+2. Consequently fullfree>=4 and R>=5 are supplied inside the counter branch. This guards against the original hypothesis-supply gap.

Transport audit: the Nat helper uses actual relative positive counts. The zero/full-positive adapter obtains these by cN addition at the original base. The Intp adapter shifts the whole original prefix and both actual windows, preserving original Endable. No origin reset, independent supply tags, finite head cutoff or unproved existence direction enters.

Source-family uniqueness check: sourceAt is an actual constant-run suffix with a positive retained length, exact mass+clock=1 and key=-2. The cN<=1 proof uses the existing constant-run root uniqueness, not a finite search or an independent tag. Prepending S to a fixed suffix changes the key by -4k*cntF(x)-2k² (negative cross term); confusing it with the positive cross term for appending S would create spurious multiple-root countermodels. Prepending A has the corresponding linear key change, and an all-A suffix cannot have key -2. This audits why summing at most one per source family is legitimate before clock overlap reduces the total.
