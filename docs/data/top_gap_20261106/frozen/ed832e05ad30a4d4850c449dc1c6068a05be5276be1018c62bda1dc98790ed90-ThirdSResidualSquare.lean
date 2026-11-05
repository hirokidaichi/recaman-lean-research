import Recaman.ThirdSTargetProfile
import Recaman.ThirdSShortTwo

namespace Recaman.ThirdSResidualSquare

open Recaman.ShortCounterFactorBounds Recaman.ThirdSShortTwo
open Recaman.FourthSourceFamilies

private theorem square_not_between (x lo : Int) (hx : 0≤x)
    (hl : 0≤lo) (h1 : lo^2<x^2) (h2 : x^2<(lo+1)^2) : False := by
  by_cases he : x≤lo
  · have h:=square_lower lo x hx he
    omega
  · have h:=square_lower x (lo+1) (by omega) (by omega)
    omega

private theorem square_sum_197 (a b : Int) (ha : 2≤a) (hb : 2≤b)
    (ha' : a≤13) (hb' : b≤13) (he : a^2+b^2=197) : False := by
  have check (x y : Int) (hy : 0≤y) (hx : 10≤x) (hx' : x≤13)
      (h : x^2+y^2=197) : False := by
    rcases (show x=10 ∨ x=11 ∨ x=12 ∨ x=13 by omega) with h10|h11|h12|h13
    · subst x
      exact square_not_between y 9 hy (by decide) (by grind only) (by grind only)
    · subst x
      exact square_not_between y 8 hy (by decide) (by grind only) (by grind only)
    · subst x
      exact square_not_between y 7 hy (by decide) (by grind only) (by grind only)
    · subst x
      exact square_not_between y 5 hy (by decide) (by grind only) (by grind only)
  by_cases h10 : 10≤a
  · exact check a b (by omega) h10 ha' he
  by_cases h10' : 10≤b
  · exact check b a (by omega) h10' hb' (by omega)
  have a9:=square_lower 9 a (by omega) (by omega)
  have b9:=square_lower 9 b (by omega) (by omega)
  grind only

/-- At total residual S length fourteen, the selected third-S
target and a supplier in that same separator cannot coexist. -/
theorem third_S_source_excludes_residual_fourteen (q s U v T j i : Nat) (hj : 1≤j)
    (hv : 1≤v) (hU : 1≤U)
    (hbalance : T+U=j+1+q+v)
    (hsq : ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int))
    (hs : sourceAt false s (List.replicate U true++List.replicate v false) i) :
    q+v≠14 := by
  intro h14
  obtain ⟨_,k,hk,_,hkq,_,hfac⟩:=
    Recaman.ThirdSTargetProfile.third_S_same_separator_clock q s U v T j i hj hbalance hsq hs
  have hqv : (q : Int)+(v : Int)=14 := by omega
  have hR : (j : Int)+1≤13 := by
    by_cases h : (j : Int)+1≤13
    · exact h
    exfalso
    have hm:=square_lower ((j : Int)+1) 14 (by decide) (by omega)
    have hp:=Int.mul_pos (show 0<(U : Int) by omega) (show 0<(v : Int) by omega)
    rw [hqv] at hsq
    grind only
  apply square_sum_197 ((j : Int)+1) ((k : Int)+(v : Int)) (by omega) (by omega) hR (by omega)
  have hkey : ((q : Int)+(v : Int))^2-((k : Int)+(v : Int))^2=((j : Int)+1)^2-1 := by
    grind only
  rw [hqv] at hkey
  grind only

end Recaman.ThirdSResidualSquare
