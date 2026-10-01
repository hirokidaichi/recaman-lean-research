# Hypothesis card: fixed-SS2 word offset span

- ID: `H-20261001-05`
- Owner: Codex, proposer/falsifier/paper writer/auditor passes
- Created: 2026-10-01
- Status: `PROVED-PAPER` (E-365, historical paper unit). The all-k Lean proof
  and independent review are complete in E-367; see
  [follow-up card](HYPOTHESIS_CARD_2026-10-01_SS2_WORD_OFFSET_SPAN_LEAN.md).
- Base: `cbe51b7`, separate docs/experiment unit, not part of #76's Lean module.
- Bounded question for #73: do word-level minimality, NoSAAS and SS=2,
  even with terminal A length zero, bound the distance between a marked
  S and the true oldest S? Test the fixed family below, not a new owner
  or matching conjecture.

## Exact statement and acceptance

For all natural k, with C=SAAASSAAASS, define the explicit newest-first
word V_k=(SA)^k C (AS)^(3k). Claim:

```text
P2(V_k), no positive proper P2 prefix, ssCount(V_k)=2;
A::V_k contains no SAAS substring;
length(V_k)=8k+11;
the newest S has offset 1, the true oldest S has offset 8k+11;
terminal A-run t=0, their distance Delta=8k+10.
```

Hence no constant word-only bound Delta<=C0 follows from these premises.
This marks an actual S in a word, not an owner supplied by a Hall-tight
family. It does not refute an owner-delta bound that uses those additional
conditions, and it does not refute #73 or claim orbit realization.

Acceptance: complete paper proof, exact finite falsifier and boundary
controls, explicit quantifiers and limitation above. No new Lean module
or PROVED-LEAN row is planned for this unit. Computation alone is insufficient.

## Search and dependency chain

- E-122 OneSSMultiplicity already uses the same padding form with a
  different SS=1 core. This unit is its fixed-SS2 analogue, not a new
  padding method or a new many-source capacity result.
- Searched registry, portfolio, OneSSMultiplicity and existing SS2 modules;
  no registered fixed-SS2 offset-span family was found.
- Existing alt mass/moment: mass(SA)^k=mass(AS)^k=0,
  moment(SA)^k=k, moment(AS)^k=-k.
- C has mass1, moment0, two SS; its proper mass-one prefixes are at
  3,5,7 with moments 4,3,4. Derive the complete prefix classification
  after padding: core visits get +3k; final AS pairs reduce moment by
  one each until 0 only at the last pair. Initial SA prefixes have mass<=0.
- Verify NoSAAS inside the fixed core, alternating blocks and all joins,
  and true first/last S offsets. Then Delta grows linearly in k.

## Falsification and stop

- Discovery k=0..10; disjoint claim-specific holdout k=11..80. Freeze
  script/card digest before both runs. Previous unrelated word enumeration
  is not claimed to be untouched data for this question.
- Weakened-history model is the abstract word itself. The explicit
  current A prefix is included, but no recurrence or finite-history greedy
  realizability is assumed.
- Negative control: replace the core by AAASSSASASA. At k=1 an earlier
  P2 occurs; its padding is not minimal. Replace 3k final AS pairs by
  3k+1: final moment is -1 and an earlier P2 occurs.
- Stop on any failure of the fixed family or absence of a complete prefix
  argument within 20 minutes. No core search or owner-family assumption
  repair. Do not register arithmetic or finite computation as a theorem.

## Audit / next decision

Separate the proposed word-only bound from actual owner delta. A single
word has no member set, owner map, tightness, onto condition or periodicity.
If the family passes, stop word-only constant-offset routes and require
an explicitly stated owner-family input for the next #73 unit. Independent
review of #74/#75/#76 remains separate and pending.


## Evidence and decision

- Complete paper proof: SS2_WORD_OFFSET_SPAN_2026-10-01.md. The exact
  three-region prefix classification gives only positive proper mass-one
  moments, including k=0. No counterexample or statement repair occurred.
- COMPUTED: frozen discovery k=0..10 (11 words), holdout k=11..80
  (70 words), zero family-property or classification violations. Largest
  word length651, marked-to-oldest span650.
- Negative controls: the wrong core at k=1 has P2 prefixes [7,19];
  one extra AS has moment -1 and an earlier P2 at19. Both fail minimality.
- Kernel checks only the fixed core's mass/moment/SS count, complete
  mass-one prefix table and NoSAAS finite scan. No all-k Lean result.
- Hash verification and commands/outputs are in
  data/ss2_word_offset_span_20261001. Base cbe51b7; scripts frozen before runs.
- The complete route was recorded by 09:03 UTC, within the 20-minute stop
  gate that began at09:00 UTC.
- Same-session semantic audit confirms that the marked S is an actual
  word position and that it is not an owner of a tight family. No
  evidence level is transferred from the kernel core controls to all k.
- Stop word-only constant-span routes. Continue only with a concrete
  additional owner-family condition, under a new bounded card.

- Saved on its own branch codex/ss2-word-offset-span and managed worktree,
  independently of the #76 Lean branch. Copied files were SHA-256 checked.
