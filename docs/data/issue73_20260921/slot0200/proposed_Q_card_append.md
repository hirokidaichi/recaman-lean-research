## 2026-09-21: E-360 registration

`PROVED-LEAN` E-360 registers
`Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor` at frozen source SHA-256
`bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
For every positive-period sign word, if a nodup tight B consists of in-range current-A phases whose
windows are minimal P2 with lag in `{3,7,11}`, and the donor is a minimal lag-11 P2 window with
SS count 2, its true oldest S phase is outside `neighborhood e p B lag`. There is no period upper
bound. Ambient U, an assumed Hall condition, and positive drift are absent because the theorem
proves Hall for every short sublist from the existing short selector.

This proves the original card's Q. `U.Nodup` plus `B.Sublist U` gives `B.Nodup`; U completeness
gives phase bounds, current-A and P2 windows for B; the old minimal-lag condition gives B's
minimality hypothesis; and `u0 ∈ U` with `lag u0 = 11` gives donor P2 and minimality. The old
positive drift, remaining ambient-U completeness, assumed Hall, and `u0 ∉ B` are unused in the
E-360 application. Thus the exact original Q follows from E-360 without changing the original
quantifiers. General Gate T6, arbitrary lag, actual Recamán orbits, E-070/E-067, and surjectivity of the
Recamán sequence remain unproved. The used p32/33 holdout remains finite evidence, not the proof.

The registration was independently checked against the three frozen source hashes, all 10 core
theorems and two existing constructors, nonempty and weakened-model controls, and official G5.
The missing daytime entry audit and the 01:00 checker-source retention gap remain historical
process debt; the later audit does not rewrite that history.
