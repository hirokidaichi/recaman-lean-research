import Recaman.ThirdSSmallCircle

namespace Recaman.ThirdSSaturationAlgebra

open Recaman.ShortCounterFactorBounds Recaman.ThirdSShortTwo
open Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

/-- The saturated original count equations cannot coexist with both
concrete late source families. No source clock is identified with the other. -/
theorem saturation_equations_impossible (W L s U v T q j r i k : Nat)
    (hW : L+1≤W) (hv : 1≤v) (hU : 1≤U) (hq : 4≤q) (hqs : q≤s)
    (h16 : W+q+v=16) (hr : 4≤r) (hrj : r≤j)
    (hT : 7≤T) (hfree : T+r≤j+7)
    (hbal : T+U=j+1+q+v)
    (hsq : ((q : Int)+(v : Int))^2=((j : Int)+1)^2+2*(U : Int)*(v : Int))
    (ha : sourceAt true L
      (List.replicate s false++(List.replicate U true++List.replicate v false)) i)
    (hs : sourceAt false s (List.replicate U true++List.replicate v false) k) : False := by
  by_cases hlarge : 12≤q+v
  · exact Recaman.ThirdSResidualSquare.second_A_third_S_key_collision
      L s U v i k (by omega) (by omega) ha hs
  obtain ⟨_,b,hb,_,hbq,_,hfac⟩:=
    Recaman.ThirdSTargetProfile.third_S_same_separator_clock q s U v T j k
      (by omega) hbal hsq hs
  have hRp : (j : Int)+1<(q : Int)+(v : Int) := by
    by_cases hh : (j : Int)+1<(q : Int)+(v : Int)
    · exact hh
    · have hlow:=square_lower ((j : Int)+1) ((q : Int)+(v : Int)) (by omega) (by omega)
      have hpos:=Int.mul_pos (show 0<(U : Int) by omega) (show 0<(v : Int) by omega)
      grind only
  have hcircle : ((q : Int)+(v : Int))^2+1=((j : Int)+1)^2+((b : Int)+(v : Int))^2 := by
    grind only
  rcases Recaman.ThirdSSmallCircle.small_source_circle
      ((q : Int)+(v : Int)) ((j : Int)+1) ((b : Int)+(v : Int))
      (by omega) (by omega) (by omega) hRp (by omega) (by omega) hcircle with h7|h8
  · obtain ⟨hp,hR,_⟩:=h7
    have hj : j=4 := by omega
    have hTv : T=7 := by omega
    have hU5 : U=5 := by omega
    rw [hj,hU5] at hsq
    have hdiv : 10*(v : Int)=24 := by
      rw [show (q : Int)+(v : Int)=7 by omega] at hsq
      grind only
    omega
  · obtain ⟨hp,hR,_⟩:=h8
    have hj : j=6 := by omega
    rw [hj,show (q : Int)+(v : Int)=8 by omega] at hsq
    have hdiv : 2*((U : Int)*(v : Int))=15 := by grind only
    omega

end Recaman.ThirdSSaturationAlgebra
