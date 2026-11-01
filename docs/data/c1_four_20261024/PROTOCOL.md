# H-20261024-01/02, frozen before new graph execution

Goal: the independently necessary old-signature model for AN≤4 is closed before11A
using A-event gap19 compression. Every gap0..19 and both supplied/nonsupplied tags must be represented.
No cap on actual A transitions: reaching11A is a model counterexample and stops this certificate route.
The actual-word macro simulation has already passed individual Lean checking, separately from this graph.

Exploration CPU reallocation, before execution: 0 ->120 CPU seconds, ≤100wall seconds total;
50CPU/45wall per discovery and independent job, ≤10CPU serialization/controls reserve.
At most2 minutes are taken from C1's remaining exploitation time, no extension past08:00.
Discovery: python3 docs/data/c1_four_20261024/macro_graph.py
Independent holdout: python3 docs/data/c1_four_20261024/macro_independent.py
The second implementation uses reverse mass/moment and DFS; checks every state/edge independently.
Unused long-gap controls: j20/37/257/4097, both tags, first32 lexicographic states per AN0..4.
Expected endpoint classes are compared to yesterday's saved r4 root set, but not assumed in graph generation.
Acceptance: full finite closure, no11A, all normalized states/edges agree; then kernel-check the certificate.
A runtime/state guard means INCOMPLETE, never absence. No same-model time extension on failure.
If the stronger model has a witness, record it separately from a true C1 counterexample and switch to terminal certificate.
Lean compilation and kernel verification are validation CPU, measured separately where available.
Frozen HEAD/dirty source/source hashes/argv are in RUNS.json and start artifacts.
