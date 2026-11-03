import Recaman.MassTwoThreeKeys

namespace Recaman.MassTwoShortOldKeys

theorem short_old_parameters (R S K ku ks v : Int) (hR : 5≤R) (hS : S≤18-v)
    (hv : v=3 ∨ v=4) (hK : 3≤K)
    (hku : ku= -2 ∨ ku=0) (hks : ks= -2 ∨ ks=0 ∨ ks=2)
    (hjoint : ¬(ku= -2 ∧ ks= -2))
    (hdiff : ku-ks=4*S+4*v+2-2*R^2)
    (hkey : ku=2*S^2-4*K-8*(S+v)+2*v^2-2*R^2) :
    R=6 ∧ ((v=3 ∧ S=14 ∧ K=51 ∧ ku= -2 ∧ ks=0) ∨
      (v=3 ∧ S=15 ∧ K=63 ∧ ku=0 ∧ ks= -2) ∨
      (v=4 ∧ S=13 ∧ K=41 ∧ ku= -2 ∧ ks=0) ∨
      (v=4 ∧ S=14 ∧ K=52 ∧ ku=0 ∧ ks= -2)) := by
  have hR6 : R≤6 := by
    by_cases h6 : R≤6
    · exact h6
    have hs:=Recaman.ShortCounterFactorBounds.square_lower R 7 (by omega) (by omega)
    rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
  rcases (show R=5 ∨ R=6 by omega) with rfl|rfl
  · rcases hv with rfl|rfl
    · have hs : S=8 ∨ S=9 := by
        rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
      rcases hs with rfl|rfl <;> rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
    · have hs : S=7 ∨ S=8 := by
        rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
      rcases hs with rfl|rfl <;> rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
  · constructor
    · rfl
    rcases hv with rfl|rfl
    · have hs : S=14 ∨ S=15 := by
        rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
      rcases hs with rfl|rfl <;> rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
    · have hs : S=13 ∨ S=14 := by
        rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
      rcases hs with rfl|rfl <;> rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega

end Recaman.MassTwoShortOldKeys
