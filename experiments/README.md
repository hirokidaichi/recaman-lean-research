# Empirical probes

These programs are exploratory companions to the Lean development. Their output is
evidence for choosing conjectures; it is not imported into any Lean proof.

Build with a C++20 compiler:

```bash
c++ -O3 -std=c++20 experiments/recaman_empirical.cpp -o /tmp/recaman_empirical
c++ -O3 -std=c++20 experiments/recaman_b1_history.cpp -o /tmp/recaman_b1_history
```

Example runs:

```bash
/tmp/recaman_empirical 1000000
/tmp/recaman_b1_history 1000000
```

The reported billion-step run used `1000000000` as the final argument. It requires
substantial time and memory because exact history membership is stored as a bitset.
`recaman_empirical.cpp` checks the borrow-coordinate transition equations while it
runs; a mismatch exits nonzero. `recaman_b1_history.cpp` performs the focused
one-borrow and first-occurrence audit described in the main README.

