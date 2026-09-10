# Hypothesis card: finite-history control for the absent one-SS family B

- ID: `H-20260910-24`
- Status: `REFUTED` (E-124), with a Lean-checked exact replay
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles sequential.

## Bounded question

H23b found70,375 one-SS minimum supply windows through10^7 actual steps,
all family A and none B. Can absence of B be deduced merely from the exact
greedy finite-history recurrence, with arbitrary finite initial history?
Falsify that implication using the explicitly proposed state at base clock10:
value100, seen[100,64,76,86,83,80]. It should run through signs
SSAAASASASAA, making the current A at sign time21 have minimum P2 lag11
and preceding newest-first word ASASASAAASS (family B,n5,j3,z4).

Acceptance: independently replay the greedy updates and check both freshness
and each A blocker; certify the state, signs, minimum lag and family B word
in Lean. Stop if any stored value is silently added during the replay.
No canonical reachability of the initial state is claimed.
This control prevents a zero finite census from becoming a false structural
exclusion. The canonical B question remains separate.

## Evidence

- Independent Python replay confirms all12 exact greedy steps, every A blocker and S freshness, and minimum lag11; `family_b_seeded_control.txt`.
- `PROVED-LEAN`: `OneSSSeededB` certifies the exact values/signs, family B word, current A, all smaller lags failing, NoSAAS and SS1.
- Full audit PASS,1,566 declarations; `check24_family_b_seeded_control.txt`.
- The finite-history exclusion is refuted. This state was not claimed canonically reachable. H25 separately found a canonical occurrence and verified it with an independent full replay.
