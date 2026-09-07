# Second pass: falsify the all-period supply-signature conjecture

Owner: root. Frozen before running `periodic_search.py`.
Related card: H-20260907-07. Base revision: 612fcfa.

Question: does some positive-sum periodic sign word supply every addition phase,
where supply means a lag d with backward sign sum 1 and weighted moment 0?
A word satisfying this condition would refute the proposed combinatorial lemma,
but would not by itself construct an actual periodic Recamán orbit.

Protocol: seed 20260907; periods 19..64; 1,000 shuffled words per period with the
smallest positive sign sum (1 for odd, 2 for even), plus 100 independently sampled
positive-sum words per period. Then 10,000 swaps preserving sign sum at each of
periods 24,32,48,64, favoring fewer unsupported addition phases and restarting
every 1,000 swaps. Stop immediately at a word with every addition supplied.

Use d=q*p+r and solve q*S+prefix_sum(r)=1 exactly. Evaluate its weighted moment
by the closed formula, and independently check any reported witness by direct
summation. Validate the formula against direct summation on fixed periods 1..12.

This is a finite falsifier, not a proof or a probability estimate. The choice to
search low positive drift is motivated by its larger set of possible supplier
lags; it is not an unbiased survey of all words. Any new best example is merely
an exact finite word, not evidence of canonical behavior.

Implementation check before the search caught differing list order at period7:
the closed formula produced lags [7,3], while direct summation produced [3,7].
Sort the closed-form output before comparison. No lag set, mathematical condition,
search range, random seed, or acceptance criterion changed.
