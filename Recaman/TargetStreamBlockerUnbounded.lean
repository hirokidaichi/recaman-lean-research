import Recaman.TargetTailResidualKernel
import Recaman.TargetCombSemanticMount
import Recaman.TargetCombFiniteCeiling

namespace Recaman

/-! # Unbounded blockers inside an unbounded right terminal stream

An unbounded right terminal stream keeps every terminal-comb entry on or to
the right of its fixed separator root.  This module extracts two further
quantitative consequences.

First, the semantic mount turns the entry floor into a blocker floor: every
comb strictly inside the stream has terminal blocker at least the root.

Second, the stream is chronologically unbounded, so a choice chain of
pairwise disjoint completed combs can be extracted, one strictly after the
final time of the previous one.  Distinct final times force distinct
blockers, and the finite ceiling pigeonhole then produces a comb whose
blocker exceeds any prescribed bound.  Consequently both the blockers and
the comb entries of the stream escape every fixed ceiling, while remaining
at or above the separator root.
-/

/-- Inside the strict tail of an unbounded right terminal stream, the
separator root bounds every terminal blocker from below: the entry floor
of the stream forbids the entry-below branch of the semantic mount. -/
theorem UnboundedRightTerminalStream.blocker_floor
    {target tailStart root rootFirstTime : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (hrootFirst : FirstAt a root rootFirstTime)
    (hrootTime : rootFirstTime ≤ tailStart)
    {start length blocker : Nat}
    (hstart : tailStart < start)
    (hcomb : HistoryTerminatedComb start length blocker) :
    root ≤ blocker := by
  have hentry : root ≤ a start :=
    hstream.1 start length blocker (Nat.le_of_lt hstart) hcomb
  have hfirstTime : rootFirstTime < start :=
    Nat.lt_of_le_of_lt hrootTime hstart
  rcases hcomb.entry_below_or_anchor_le_blocker hrootFirst hfirstTime with
    hbelow | hfloor
  · exact False.elim (by omega)
  · exact hfloor

/-- Packaged form of the second stream conjunct: for every cutoff there is
a target-low completed comb whose start lies strictly after the cutoff and
strictly inside the tail. -/
private theorem UnboundedRightTerminalStream.exists_lowCombTriple
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (cutoff : Nat) :
    ∃ t : Nat × Nat × Nat,
      cutoff < t.1 ∧
      tailStart < t.1 ∧
      nextSubtractionCandidate t.1 < target ∧
      HistoryTerminatedComb t.1 t.2.1 t.2.2 := by
  rcases hstream.2 (Nat.max cutoff tailStart) with
    ⟨start, length, blocker, hstart, _htailStart, hlow, hcomb⟩
  exact ⟨(start, length, blocker),
    Nat.lt_of_le_of_lt (Nat.le_max_left cutoff tailStart) hstart,
    Nat.lt_of_le_of_lt (Nat.le_max_right cutoff tailStart) hstart,
    hlow, hcomb⟩

/-- Choice function selecting, after any cutoff, one target-low completed
comb of the stream as a start/length/blocker triple. -/
private noncomputable def streamPick
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (cutoff : Nat) : Nat × Nat × Nat :=
  Classical.choose (hstream.exists_lowCombTriple cutoff)

/-- Defining property of `streamPick`. -/
private theorem streamPick_spec
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (cutoff : Nat) :
    cutoff < (streamPick hstream cutoff).1 ∧
    tailStart < (streamPick hstream cutoff).1 ∧
    nextSubtractionCandidate (streamPick hstream cutoff).1 < target ∧
    HistoryTerminatedComb (streamPick hstream cutoff).1
      (streamPick hstream cutoff).2.1 (streamPick hstream cutoff).2.2 :=
  Classical.choose_spec (hstream.exists_lowCombTriple cutoff)

/-- Chronological chain of stream combs: each link is chosen strictly after
the final time of the previous one. -/
private noncomputable def streamChain
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root) :
    Nat → Nat × Nat × Nat
  | 0 => streamPick hstream tailStart
  | i + 1 =>
      streamPick hstream
        ((streamChain hstream i).1 + 2 * (streamChain hstream i).2.1)

/-- Every chain link is a target-low completed comb strictly inside the
tail. -/
private theorem streamChain_spec
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (i : Nat) :
    tailStart < (streamChain hstream i).1 ∧
    nextSubtractionCandidate (streamChain hstream i).1 < target ∧
    HistoryTerminatedComb (streamChain hstream i).1
      (streamChain hstream i).2.1 (streamChain hstream i).2.2 := by
  cases i with
  | zero =>
      have hchain : streamChain hstream 0 = streamPick hstream tailStart := by
        simp only [streamChain]
      rw [hchain]
      have hspec := streamPick_spec hstream tailStart
      exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩
  | succ j =>
      have hchain : streamChain hstream (j + 1) =
          streamPick hstream
            ((streamChain hstream j).1 + 2 * (streamChain hstream j).2.1) := by
        simp only [streamChain]
      rw [hchain]
      have hspec := streamPick_spec hstream
        ((streamChain hstream j).1 + 2 * (streamChain hstream j).2.1)
      exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩

/-- Chain links start strictly inside the tail. -/
private theorem streamChain_tail
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (i : Nat) :
    tailStart < (streamChain hstream i).1 :=
  (streamChain_spec hstream i).1

/-- Chain links have target-low subtraction candidates. -/
private theorem streamChain_low
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (i : Nat) :
    nextSubtractionCandidate (streamChain hstream i).1 < target :=
  (streamChain_spec hstream i).2.1

/-- Chain links are completed terminal combs. -/
private theorem streamChain_comb
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (i : Nat) :
    HistoryTerminatedComb (streamChain hstream i).1
      (streamChain hstream i).2.1 (streamChain hstream i).2.2 :=
  (streamChain_spec hstream i).2.2

/-- Consecutive chain links have strictly increasing final times. -/
private theorem streamChain_final_lt_succ
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (i : Nat) :
    (streamChain hstream i).1 + 2 * (streamChain hstream i).2.1 <
      (streamChain hstream (i + 1)).1 +
        2 * (streamChain hstream (i + 1)).2.1 := by
  have hchain : streamChain hstream (i + 1) =
      streamPick hstream
        ((streamChain hstream i).1 + 2 * (streamChain hstream i).2.1) := by
    simp only [streamChain]
  rw [hchain]
  have hstart := (streamPick_spec hstream
    ((streamChain hstream i).1 + 2 * (streamChain hstream i).2.1)).1
  omega

/-- Chain final times are strictly monotone. -/
private theorem streamChain_final_lt_of_lt
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (i : Nat) :
    ∀ j, i < j →
      (streamChain hstream i).1 + 2 * (streamChain hstream i).2.1 <
        (streamChain hstream j).1 + 2 * (streamChain hstream j).2.1 := by
  intro j
  induction j with
  | zero =>
      intro hij
      exact False.elim (by omega)
  | succ n ih =>
      intro hij
      by_cases hin : i < n
      · exact Nat.lt_trans (ih hin) (streamChain_final_lt_succ hstream n)
      · have hieq : i = n := by omega
        subst hieq
        exact streamChain_final_lt_succ hstream i

/-- Chain final times determine the chain index. -/
private theorem streamChain_final_injective
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    {i j : Nat}
    (heq : (streamChain hstream i).1 + 2 * (streamChain hstream i).2.1 =
      (streamChain hstream j).1 + 2 * (streamChain hstream j).2.1) :
    i = j := by
  by_cases hlt : i < j
  · have hmono := streamChain_final_lt_of_lt hstream i j hlt
    omega
  · by_cases hgt : j < i
    · have hmono := streamChain_final_lt_of_lt hstream j i hgt
      omega
    · omega

/-- The terminal blockers of an unbounded right terminal stream escape
every fixed ceiling: any `B + 2` chain links have pairwise distinct final
times, so the finite ceiling pigeonhole yields a blocker above `B`. -/
theorem UnboundedRightTerminalStream.exists_blocker_gt
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (B : Nat) :
    ∃ start length blocker,
      tailStart < start ∧
      nextSubtractionCandidate start < target ∧
      HistoryTerminatedComb start length blocker ∧
      B < blocker := by
  classical
  have hinj : Function.Injective
      (fun i : Fin (B + 2) =>
        (streamChain hstream i.val).1 +
          2 * (streamChain hstream i.val).2.1) := by
    intro i j heq
    have hval : i.val = j.val := streamChain_final_injective hstream heq
    exact Fin.eq_of_val_eq hval
  have hmany := HistoryTerminatedComb.exists_blocker_gt_of_many
    (B := B)
    (s := fun i : Fin (B + 2) => (streamChain hstream i.val).1)
    (k := fun i : Fin (B + 2) => (streamChain hstream i.val).2.1)
    (blocker := fun i : Fin (B + 2) => (streamChain hstream i.val).2.2)
    (fun i => streamChain_comb hstream i.val) hinj
  rcases hmany with ⟨i, hblocker⟩
  exact ⟨(streamChain hstream i.val).1, (streamChain hstream i.val).2.1,
    (streamChain hstream i.val).2.2, streamChain_tail hstream i.val,
    streamChain_low hstream i.val, streamChain_comb hstream i.val, hblocker⟩

/-- The comb entries of the stream also escape every fixed ceiling: each
entry exceeds its own terminal blocker. -/
theorem UnboundedRightTerminalStream.exists_entry_gt
    {target tailStart root : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (B : Nat) :
    ∃ start length blocker,
      tailStart < start ∧
      HistoryTerminatedComb start length blocker ∧
      B < a start := by
  rcases hstream.exists_blocker_gt B with
    ⟨start, length, blocker, htail, _hlow, hcomb, hblocker⟩
  have hentry := hcomb.entry_eq_blocker_add_length
  exact ⟨start, length, blocker, htail, hcomb, by omega⟩

/-- Packaged kernel form: with a certified separator root, the stream
contains target-low combs whose blockers are simultaneously at least the
root and above any prescribed ceiling. -/
theorem UnboundedRightTerminalStream.blockers_escape_every_ceiling
    {target tailStart root rootFirstTime : Nat}
    (hstream : UnboundedRightTerminalStream target tailStart root)
    (hrootFirst : FirstAt a root rootFirstTime)
    (hrootTime : rootFirstTime ≤ tailStart)
    (B : Nat) :
    ∃ start length blocker,
      tailStart < start ∧
      nextSubtractionCandidate start < target ∧
      HistoryTerminatedComb start length blocker ∧
      root ≤ blocker ∧
      B < blocker := by
  rcases hstream.exists_blocker_gt B with
    ⟨start, length, blocker, htail, hlow, hcomb, hblocker⟩
  exact ⟨start, length, blocker, htail, hlow, hcomb,
    hstream.blocker_floor hrootFirst hrootTime htail hcomb, hblocker⟩

end Recaman
