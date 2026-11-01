# Pending candidates excluded from this core review

The review boundary ends at `short_tight_avoids_ss2_donor` (source line 358). None of the following
is approved, refuted, registered, or promoted by this slot.

- `short_supply_donor_deletion` (lines 360-389): deletion consequence for an entire short minimal
  supply list. Not part of core Q/W review.
- `ss2Windows`, `mem_ss2Windows`, `ss2_oldest_cover_table`, `owner_member_avoids_ss2_window`, and
  `short_tight_avoids_ss2_window` (lines 393-528): donor minimality removal. H-20260920-02 is
  `CONJECTURED`; daytime same-session evidence only.
- `exists_minimal_p2_prefix`, `neighborhood_prefix_sublist`,
  `tight_neighborhood_eq_of_p2_prefix`, `short_p2_tight_avoids_ss2_window`, and
  `short_p2_ss2_deletion` (lines 530-639): prefix reduction and nonminimal short windows.
  H-20260920-03 is `CONJECTURED`; not mixed into the core result.
- `donorLength15Stream` and `nonminimal_donor_length15_counterexample` (lines 641-669): length-15
  literal countermodel. H-20260920-04 is labelled `REFUTED` by the daytime same-session card, with
  registry promotion review pending. Independent audit is unfinished; this night grants no approval.
- H-20260920-05, arbitrary-length minimal SS2 donor patterns, is `CONJECTURED` and outside this
  module's reviewed core.
- `Recaman/SS2OldestPattern.lean` is a separate untracked module and wholly unreviewed here. It is
  also the current reason `./scripts/check.sh` stops at the root-closure gate.

The p=32/33 holdout was used by the daytime session (2,000 accepted words for each period, no
reported Q/W violations). Its second implementation was written by the same author/session, so it
is algorithmic cross-checking rather than the weekly plan's independent-agent approval.
