import Recaman.PermanentAboveCorridorFixedPointShape

namespace Recaman

noncomputable section

/-! # Below-target corridors of both fixed points

The all-below corridor proved for the discharge replay is an instance of a
general fact: up to a canonical first upcrossing from a below-target start,
the orbit never reaches the target, because an intermediate at-or-above
value would produce an earlier weak upcrossing.  Stating the general lemma
once equips the landing fixed point with the same corridor: between the
fresh landing and its reproduction crossing every orbit value is below the
target.  Both fixed points therefore trap a below-target corridor whose
right endpoint carries the parent anchor.
-/

/-- Up to a canonical first upcrossing, the orbit stays below the target. -/
theorem FirstWeakUpcrossingStep.all_below
    {target start time : Nat}
    (h : FirstWeakUpcrossingStep target start time)
    (hstart : a start < target) :
    ∀ t, start ≤ t → t ≤ time → a t < target := by
  intro t hstartLe hle
  by_cases hbelow : a t < target
  · exact hbelow
  · have hge : target ≤ a t := Nat.le_of_not_lt hbelow
    rcases exists_weakUpcrossingStep_between hstartLe hstart hge with
      ⟨witness, hwitness, hwitnessBefore⟩
    have hbefore : witness < time := by omega
    exact False.elim (h.first witness hbefore hwitness)

/-- The landing fixed point traps the same below-target corridor as the
discharge replay: from the fresh landing to the reproduction crossing the
orbit never reaches the target. -/
theorem landing_cycle_corridor_below
    {target value landingTime crossingTime : Nat}
    (value_below : value < target)
    (landing_first : FirstAt a value landingTime)
    (next_crossing : FirstWeakUpcrossingStep target landingTime
      crossingTime) :
    ∀ t, landingTime ≤ t → t ≤ crossingTime → a t < target := by
  have hstart : a landingTime < target := by
    rw [landing_first.1]
    exact value_below
  exact next_crossing.all_below hstart

end

end Recaman
