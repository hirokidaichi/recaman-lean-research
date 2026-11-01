import Recaman.PermanentAboveTail

namespace Recaman

/-! # Coordinate audit of the permanent-tail minimum

The global tail minimum forces two consecutive additions.  This is genuine
local structure, but it does not impose a uniform direction on the existing
signed coordinate potential.  Two kernel-checked orbit examples realize
opposite potential drifts, so any new tail rank must use the historical
blocker or another global certificate in addition to `potential`.
-/

/-- The local transition pattern forced at a permanent-tail minimum. -/
structure DoubleForcedAdditionAt (time : Nat) : Prop where
  first_forced : ¬ CanSubtract (time + 1) (stateAt time)
  followup_forced : ¬ CanSubtract (time + 2) (stateAt (time + 1))

/-- Forget the remaining minimum/history fields and retain the two-step
coordinate-relevant pattern. -/
theorem PermanentTailMinimumCertificate.doubleForced
    {target start time firstTime : Nat}
    (h : PermanentTailMinimumCertificate target start time firstTime) :
    DoubleForcedAdditionAt time :=
  ⟨h.first_forced, h.followup_forced⟩

/-- At time four, the actual double forced addition `2 → 7 → 13` strictly
decreases the signed potential from `2` to `-2`. -/
theorem doubleForced_potential_decrease_actual_example :
    DoubleForcedAdditionAt 4 ∧
      CoordinatesAt 4 0 2 ∧
      CoordinatesAt 6 2 1 ∧
      potential 2 1 < potential 0 2 := by
  exact ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    by decide⟩

/-- At time five, the overlapping actual double forced addition
`7 → 13 → 20` strictly increases the signed potential from `1` to `3`. -/
theorem doubleForced_potential_increase_actual_example :
    DoubleForcedAdditionAt 5 ∧
      CoordinatesAt 5 1 2 ∧
      CoordinatesAt 7 2 6 ∧
      potential 1 2 < potential 2 6 := by
  exact ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    by decide⟩

/-- Consequently the two-forced-addition pattern alone supports neither a
nonincreasing nor a nondecreasing potential invariant. -/
theorem doubleForced_potential_has_both_directions :
    (∃ time q r nextQ nextR,
      DoubleForcedAdditionAt time ∧
      CoordinatesAt time q r ∧
      CoordinatesAt (time + 2) nextQ nextR ∧
      potential nextQ nextR < potential q r) ∧
    (∃ time q r nextQ nextR,
      DoubleForcedAdditionAt time ∧
      CoordinatesAt time q r ∧
      CoordinatesAt (time + 2) nextQ nextR ∧
      potential q r < potential nextQ nextR) := by
  refine ⟨⟨4, 0, 2, 2, 1, ?_⟩, ⟨5, 1, 2, 2, 6, ?_⟩⟩
  · simpa using doubleForced_potential_decrease_actual_example
  · simpa using doubleForced_potential_increase_actual_example

end Recaman
