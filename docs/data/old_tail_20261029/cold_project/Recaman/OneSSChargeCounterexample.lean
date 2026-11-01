import Recaman.ShortLocalParityCapacity

namespace Recaman.OneSSChargeCounterexample

open ShortPeriodicSupply ShortReservoirCapacity SharpPeriodicSupply

/-! The centered one-SS extension fails even in the no-SAAS periodic
language. The counterexample does not refute unrestricted capacity. -/

def witness (t : Int) : Bool :=
  !([0,1,6,8,10] : List Nat).contains (t % 12).toNat

def centeredOff (e : Int → Bool) (t : Int) (d : Nat) : Nat :=
  let h := (d+3)/2
  if e (t-h) then if e (t-1) then h-1 else h+1 else h

theorem witness_periodic (t : Int) : witness (t+12) = witness t := by
  simp [witness]

theorem witness_shift_mod (t j : Int) : witness (t+j) = witness (t%12+j) := by
  simp [witness,Int.add_emod]

theorem witness_noSAAS (t : Int) :
    ¬ (witness t = false ∧ witness (t+1) = true ∧
      witness (t+2) = true ∧ witness (t+3) = false) := by
  have hfinite : ∀ q : Fin 12,
      ¬ (witness q.val = false ∧ witness ((q.val : Int)+1) = true ∧
        witness ((q.val : Int)+2) = true ∧ witness ((q.val : Int)+3) = false) := by decide
  have hlo : 0 ≤ t%12 := Int.emod_nonneg t (by decide)
  have hhi : t%12 < 12 := Int.emod_lt_of_pos t (by decide)
  let q : Fin 12 := ⟨(t%12).toNat,by omega⟩
  have hq : (q.val : Int) = t%12 := Int.toNat_of_nonneg hlo
  have h := hfinite q
  rw [hq] at h
  have h0 : witness t = witness (t%12) := by simpa using witness_shift_mod t 0
  rwa [h0,witness_shift_mod t 1,witness_shift_mod t 2,witness_shift_mod t 3]

theorem minimum_lags_certificate :
    witness 4 = true ∧ witness 7 = true ∧ witness 9 = true ∧
    P2 witness 4 3 ∧ P2 witness 7 7 ∧ P2 witness 9 15 ∧
    (∀ d : Fin 7, ¬ P2 witness 7 d.val) ∧
    (∀ d : Fin 15, ¬ P2 witness 9 d.val) := by
  unfold P2
  decide

theorem window_certificate :
    LeadingRunSupply.past witness 9 15 =
      [false,true,false,true,true,true,true,false,false,true,false,true,false,true,false] ∧
    ((List.range 14).filter (fun i =>
      !witness (9-((i+1 : Nat) : Int)) && !witness (9-((i+2 : Nat) : Int)))).length = 1 := by
  decide

/-- The new lag15 source and old lag7 source both land on phase0. -/
theorem centered_charge_collision :
    shortOff witness 7 = 7 ∧ centeredOff witness 9 15 = 9 ∧
    phase 12 ((9 : Int)-centeredOff witness 9 15) = 0 ∧
    phase 12 ((7 : Int)-shortOff witness 7) = 0 ∧ witness 0 = false := by
  decide

/-- Keeping the old two images, phase6 is still free for the new source.
Thus this example is a map failure, not a failure of the capacity bound. -/
theorem alternative_injection_certificate :
    shortOff witness 4 = 3 ∧ shortOff witness 7 = 7 ∧
    witness 1 = false ∧ witness 0 = false ∧ witness 6 = false ∧
    ([1,0,6] : List Nat).Nodup ∧
    3 ≤ subtractionCount witness 0 12 := by
  decide

end Recaman.OneSSChargeCounterexample
