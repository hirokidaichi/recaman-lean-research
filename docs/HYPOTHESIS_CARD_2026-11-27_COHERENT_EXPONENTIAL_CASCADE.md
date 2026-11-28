# Hypothesis Card: H-20261127-07 — Coherent Greedy (`E-759 = (0,0)`) Exponential Height Cascade

- **ID**: `H-20261127-07`
- **Parent Cycle**: `R-20261127-02` (Track 2A: resolving the `CURRENT_FRONTIER.md` / `HYPOTHESIS_CARD_2026-11-28_CROSS_HEIGHT_CAPACITY.md` open question)
- **Status**: `PROVED-PAPER` (`E-789`, `docs/RESEARCH_NOTE_2026-11-27_COHERENT_EXPONENTIAL_CASCADE.md`)
- **Depth-general classification**: `depth_general_progress` (all-`k` constructive family refuting every polynomial-in-`H` capacity bound even under full `E-759 = (0, 0)` coherent finite-State greedy realizability and all 8 canonical filters of `E-782`).

## Bounded Research Question

Does requiring `E-759 (I)/(II) = (0, 0)` (hence coherent finite-State greedy realizability passing all 8 canonical filters of `E-782`) eliminate the exponential height growth `Ω((5/3)^H)` of `E-786`, or does an explicit all-`k` coherent greedy family inside relative height band `[-1, 3k + 2]` still achieve `A / F = Ω(c^H)` for some `c > 1`?

## Exact Quantifiers & Claim

For every integer `k ≥ 1` and every `ε > 0`, there exists an explicit balanced sign word `B_k` confined to relative height band `[-1, 3k + 2]` (total span `H = 3k + 3`) such that:
1. `E-759 (I)/(II) = (0, 0)` (zero Type-I and zero Type-II subtraction collisions, hence coherent finite-State greedy realizable through the 8-filter spatial bridge grid of `E-782`), and
2. `A(B_k) / F(B_k) ≥ (1 - ε) * 3^k = Ω(3^{H / 3}) = Ω(1.44225^H)`.

## Falsifier & Evidence

- Script: `docs/data/depth_general_20261127/coherent_exponential_cascade_audit.py`
- Discovery (`K_0 = 6`):
  - `k = 1` (`h = 4`, `[0, 5]`): `len = 808`, `A/F = 2.1838`, `E-759 = (0, 0)`.
  - `k = 2` (`h = 7`, `[-1, 8]`): `len = 46,134`, `A/F = 4.0625`, `E-759 = (0, 0)`.
  - `k = 3` (`h = 10`, `[-1, 11]`): `len = 1,825,686`, `A/F = 4.4346`, `E-759 = (0, 0)`.
- Holdout (`K_0 = 12`, larger `R`):
  - `k = 1`: `len = 3,318`, `A/F = 2.4113`, `E-759 = (0, 0)`.
  - `k = 2`: `len = 334,184`, `A/F = 5.2697`, `E-759 = (0, 0)`.
  - `k = 3`: `len = 15,023,282`, `A/F = 5.2650`, `E-759 = (0, 0)`.
- All-height corridor separation invariants verified at every `r ∈ [-1, 3k + 2]` across all levels.
- Exact `E-782` 8-filter spatial bridge greedy replay verified (`True`) on `B_1` (`len = 578`, `A/F = 2.0942`, `E-759 = (0, 0)`).
- Negative controls: omitting `(SA)^{p_k}` (`p_k = 0`) causes exact Type-I collision at `r = h_{k-1} - 2` (`4` collisions at `k = 3, R = 4`); omitting `V0_k`'s `lift` clearance causes Type-I collision at `r = h_k - 1`.

## Boundaries & Non-Claims

- Not yet formalized in Lean 4 (`PROVED-PAPER`, human review pending).
- Coherent finite-State greedy realizability (`E-759 = (0, 0)` + `E-782` 8 filters) does NOT supply canonical clock-0 reachability from `a 0 = 0`, and `D_depth = 0`, `F → ∞`, so `B_k` is NOT a `C1` / `E-001` / `E-067` / `E-070` counterexample.
- Tightens the coherent-greedy actual-`EndN` exponential growth bracket to **`[3^(1/3), 199/110] = [1.4422, 1.8091]`** (and `[5/3, 199/110]` on raw sign words).
