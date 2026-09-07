# Issue 73: bounded independent literature audit

- Date: 2026-09-07; auditor: entry_barrier.
- Source revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`.
- Question fixed before searching: does an inspected primary source prove that
  standard Recaman addition/subtraction signs are not eventually periodic, or
  supply a theorem that directly establishes the positive-period P2 obstruction?
- Acceptance: an exact theorem and a checked translation of its hypotheses.
- Stop: a bounded initial literature pass; a negative result is not evidence of
  novelty and cannot certify that the question is open in all literature.
- Evidence level: `OBSERVED` bibliographic search, not a mathematical proof.

## Conclusion

No such theorem was found in the inspected sources below. Neither unboundedness
nor nonperiodicity of the value sequence establishes nonperiodicity of its
normalized signs. No inspected cycle-lemma or greedy-walk result directly gives
the simultaneous conditions `sum epsilon = 1` and `sum i*epsilon = 0`, much less
the Hall property of the minimum-lag negative-phase domains in H-09. The local
proof work should continue; no claim of novelty is justified by this search.

## Primary sources inspected and exact scope

1. [OEIS A160357](https://oeis.org/A160357) explicitly identifies the signs of
   first differences, with `a(n)=(A005132(n)-A005132(n-1))/n` for `n>=1`.
   The inspected entry supplies formulas, data, and cross-references but no
   eventual-periodicity theorem or proof reference. Related entries A057165,
   A057166, A160356, A076213 and A160351 were also checked. In particular,
   A160356 contains the unnormalized differences, whose magnitudes grow with n;
   that observation does not decide A160357 periodicity.
2. [N. J. A. Sloane, “A Handbook of Integer Sequences” Fifty Years Later,
   arXiv:2301.03149](https://arxiv.org/pdf/2301.03149), section 4.1, gives the
   standard recurrence, late first appearances, and the unresolved coverage
   question. The inspected Recaman section contains no sign-periodicity proof.
   His earlier [My Favorite Integer Sequences](https://neilsloane.com/doc/sg.pdf)
   introduces the Recaman sequences and asks about growth, without such a proof.
3. [Benjamin Chaffin's account](https://benchaffin.com/recaman/recaman.html),
   dated 2026-02-07, describes his finite computation and compressed alternating
   “pingpong” intervals. Finite alternating intervals, however large, do not
   establish an infinite eventual-periodicity or nonperiodicity assertion.
4. [Alekseyev et al., Three Cousins of Recaman's Sequence,
   arXiv:2004.14000](https://arxiv.org/pdf/2004.14000), inspected author manuscript
   v2, introduces standard Recaman in its introduction but proves results about
   different additive/divisibility, multiplicative, and concatenation rules.
   Those results cannot be transferred to the present sign word without a new
   argument. A text search for “period” found no match in the manuscript.
5. [Armstrong, Mingo, Speicher and Wilson, The Non-Commutative Cycle Lemma,
   author paper](https://www-users.cse.umn.edu/~reiner/Classes/Math8680Fall2014Papers/ArmstrongMingoSpeicherWilsonCycleLemma.pdf),
   DOI [10.1016/j.jcta.2009.12.002](https://doi.org/10.1016/j.jcta.2009.12.002),
   recalls that a +/-1 word of positive sum k has exactly k cyclic rotations
   with all partial sums strictly positive, then develops a free-group version.
   The stated hypotheses/conclusions do not impose zero weighted first moment
   or give an injection from P2-supplied positive positions to negative phases.
   Any application to H-09 still requires an additional proved translation.
6. [Foss, Rolla and Sidoravicius, Greedy walk on the real line,
   arXiv:1111.4846](https://arxiv.org/abs/1111.4846) and
   [Gabrysch and Thornblad, The greedy walk on an inhomogeneous Poisson process,
   arXiv:1611.09568](https://arxiv.org/abs/1611.09568), primary abstracts inspected,
   concern nearest-customer or nearest-unvisited-point walks in Poisson models.
   Their randomness, state space and step-selection assumptions differ from
   fixed-clock Recaman steps and do not directly settle P2.

## Access and completeness limitations

- [OEIS A005132](https://oeis.org/A005132) lists Chaffin, Sloane and Wilks,
  “On sequences of Recaman type”, paper in preparation, 2006. No accessible
  manuscript was linked there. Its contents were not checked; this is a real
  literature gap, not evidence that no theorem exists.
- A search lead for Ricardo Hernandez Reveles, “Structural Invariants and
  External Connections of Recaman's Sequence” (2026), resolves to
  [Zenodo DOI 10.5281/zenodo.20018436](https://doi.org/10.5281/zenodo.20018436).
  The primary record/full text could not be accessed during the pass. An
  aggregator abstract was not used as mathematical evidence.
- An [individual GitHub draft](https://github.com/EncapsulatorP/recaman/blob/main/supporting_docs/recaman_final_math.md)
  asks an operator-word periodicity question. Its operator encoding differs
  from the raw signs, and its claims were not independently certified. It is
  neither a proof nor an authoritative statement of the literature's frontier.
- Original Dvoretzky--Motzkin metadata and other lattice-path cycle-lemma
  abstracts were located, but no uninspected full theorem was imported.

## Search record and next decision

Representative literal queries used with web search: `Recaman sequence "sign"
"periodic"`; `Recamán "addition" "subtraction" "periodic"`; `"Recamán"
"eventually periodic"`; `"Recaman" "sign sequence"`; `"Recaman" "direction
sequence" theorem`; `"Recaman" "periodic" site:arxiv.org`; `"Recaman"
"A160357" proof`; `"Recaman" "loop-closing"`; `"Recaman" "cycle lemma"`;
`"Recamán" "Hall"`; `"cycle lemma" "weighted sum" "zero"`; `"Hall"
"cycle lemma" lattice paths`; `"greedy" "walk" "increasing step" mathematics`.

Read H-07, H-09 and the existing periodic-candidate no-go to distinguish the
precise target from already excluded bounded-candidate schedules. No new
mathematical definition or theorem was proposed by this audit, so no separate
hypothesis card was opened. Next decision: independently audit the proposed
short-lag injection; if a broader theorem is later prepared for publication,
resolve the inaccessible leads before asserting novelty.
