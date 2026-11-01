import Recaman.SSFreeSupply
import Recaman.NoDoubleAdditionRun

namespace Recaman.CanonicalSSFreeSupply

open LeadingRunSupply LocalParitySupply SSFreeSupply

/-! The word theorem is connected to the actual standard recurrence.
Only nonnegative sign times are used by a window with d <= t. -/

def canonicalSign (t : Int) : Bool :=
  decide (¬ CanSubtract (t.toNat+1) (stateAt t.toNat))

theorem canonicalSign_nat (n : Nat) :
    canonicalSign n = decide (¬ CanSubtract (n+1) (stateAt n)) := by
  simp [canonicalSign]

theorem past_get (e : Int → Bool) (t : Int) (d i : Nat) (hi : i < d) :
    (past e t d)[i]'(by simpa [past] using hi) = e (t-((i+1 : Nat) : Int)) := by
  simp [past]

theorem canonical_noSAAS (t d : Nat) (hd : d ≤ t) : NoSAAS (past canonicalSign t d) := by
  intro u v heq
  have hlen := congrArg List.length heq
  simp only [past,List.length_map,List.length_range,List.length_append,List.length_cons] at hlen
  have hlt : u.length+3 < d := by omega
  have hget (j : Nat) (hj : j < 4) :
      canonicalSign ((t : Int)-((u.length+j+1 : Nat) : Int)) =
        (false::true::true::false::v)[j]'(by simp; omega) := by
    have hi : u.length+j < d := by omega
    rw [← past_get canonicalSign t d (u.length+j) hi]
    simp only [heq,List.getElem_append_right (by omega : u.length ≤ u.length+j)]
    simp
  let n := t-(u.length+4)
  have htime (j : Nat) (hj : j ≤ 3) :
      (t : Int)-((u.length+j+1 : Nat) : Int) = ((n+(3-j) : Nat) : Int) := by
    dsimp [n]
    omega
  have hs0 : canonicalSign n = false := by
    have h := hget 3 (by decide)
    rw [htime 3 (by decide)] at h
    simpa using h
  have ha1 : canonicalSign ((n+1 : Nat) : Int) = true := by
    have h := hget 2 (by decide)
    rw [htime 2 (by decide)] at h
    simpa using h
  have ha2 : canonicalSign ((n+2 : Nat) : Int) = true := by
    have h := hget 1 (by decide)
    rw [htime 1 (by decide)] at h
    simpa using h
  have hs3 : canonicalSign ((n+3 : Nat) : Int) = false := by
    have h := hget 0 (by decide)
    rw [htime 0 (by decide)] at h
    simpa using h
  rw [canonicalSign_nat] at hs0 hs3
  rw [canonicalSign_nat] at ha1 ha2
  have hsub : CanSubtract (n+1) (stateAt n) := by
    have h := of_decide_eq_false hs0
    exact Classical.byContradiction h
  have hadd1 : ¬ CanSubtract (n+2) (stateAt (n+1)) := by
    simpa [Nat.add_assoc] using of_decide_eq_true ha1
  have hadd2 : ¬ CanSubtract (n+3) (stateAt (n+2)) := by
    simpa [Nat.add_assoc] using of_decide_eq_true ha2
  have hsub3 : CanSubtract (n+4) (stateAt (n+3)) := by
    have h := of_decide_eq_false hs3
    simpa [Nat.add_assoc] using Classical.byContradiction h
  exact (double_forcedAddition_extends hsub hadd1 hadd2) hsub3

/-- Every SS-free finite-history P2 window on the actual canonical sequence
has the clean parity pattern. No assumed sign-language restriction remains. -/
theorem canonical_noSS_clean (t d : Nat) (hd : d ≤ t)
    (hss : NoSS (past canonicalSign t d)) (hP : ShortPeriodicSupply.P2 canonicalSign t d) :
    EvenBackA canonicalSign t d :=
  stream_noSS_clean canonicalSign t d hss (canonical_noSAAS t d hd) hP

theorem canonical_noSS_iff_clean (t d : Nat) (hd : d ≤ t)
    (hP : ShortPeriodicSupply.P2 canonicalSign t d) :
    NoSS (past canonicalSign t d) ↔ EvenBackA canonicalSign t d := by
  constructor
  · exact fun hss => canonical_noSS_clean t d hd hss hP
  · intro ha
    exact evenSlots_noSS _ ((evenSlots_past_iff canonicalSign t d).mpr ha)

end Recaman.CanonicalSSFreeSupply
