import Recaman.BlockSuffixPositivity

namespace Recaman.BalancedInsertionArea

open Recaman.BlockSuffixPositivity Recaman.LeadingRunSupply

/-- A zero-mass insertion retains the cut-to-source height term in
its exact chronological area update. -/
theorem zero_mass_insertion_area (u z v : List Bool) (hz : mass z=0) :
    areaW (u++z++v)=areaW (u++v)+areaW z+(z.length : Int)*mass u := by
  simp only [areaW_append,mass_append,hz]
  grind only

/-- Nonempty zero-mass insertions cannot keep zero area across two
different source-to-cut heights, even if their own area is allowed
to compensate one of the windows. -/
theorem two_source_splice_height_agreement (u1 v1 u2 v2 z : List Bool)
    (hz : mass z=0) (hpos : 0<z.length)
    (hOld1 : areaW (u1++v1)=0) (hOld2 : areaW (u2++v2)=0)
    (hNew1 : areaW (u1++z++v1)=0) (hNew2 : areaW (u2++z++v2)=0) :
    mass u1=mass u2 := by
  have h1 := zero_mass_insertion_area u1 z v1 hz
  have h2 := zero_mass_insertion_area u2 z v2 hz
  rw [hOld1,hNew1] at h1
  rw [hOld2,hNew2] at h2
  have hm : (z.length : Int)*(mass u1-mass u2)=0 := by
    have hd : (z.length : Int)*(mass u1-mass u2)=
        (z.length : Int)*mass u1-(z.length : Int)*mass u2 := by grind only
    rw [hd]
    omega
  rcases Int.mul_eq_zero.mp hm with h | h
  · omega
  · omega

/-- At its own source height a zero-mass, zero-area insertion preserves
the selected window's mass-one/area-zero test. This is a single-window
contract, not preservation of original EndN or free counts. -/
theorem source_level_window_test (u z v : List Bool)
    (hz : mass z=0) (ha : areaW z=0) (hc : mass u=0) :
    (mass (u++z++v)=1 ∧ areaW (u++z++v)=0) ↔
      (mass (u++v)=1 ∧ areaW (u++v)=0) := by
  have harea := zero_mass_insertion_area u z v hz
  rw [ha,hc] at harea
  have hm : mass (u++z++v)=mass (u++v) := by simp [mass_append,hz]
  rw [hm]
  have he : areaW (u++z++v)=areaW (u++v) := by omega
  rw [he]

end Recaman.BalancedInsertionArea
