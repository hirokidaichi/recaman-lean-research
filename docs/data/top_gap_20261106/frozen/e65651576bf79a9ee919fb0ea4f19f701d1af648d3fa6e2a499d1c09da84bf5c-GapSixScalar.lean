import Recaman.ShortCounterFactorBounds

namespace Recaman.GapSixScalar

open Recaman.ShortCounterFactorBounds

private theorem square_impossible (R X Q C R0 X0 Q0 : Int)
    (hR0 : 0≤R0) (hR : R0≤R) (hX0 : 0≤X) (hX : X≤X0) (hQ : Q0≤Q)
    (hC : 2≤C) (hnum : X0^2+1<4+R0^2+2*Q0) (h : C^2+R^2+2*Q≤X^2+1) : False := by
  have hr:=square_lower R R0 hR0 hR
  have hx:=square_lower X0 X hX0 hX
  have hc:=square_lower C 2 (by decide) hC
  omega

/-- The scalar end of the single-pair-clock argument. A remaining
gap6 candidate requires head saturation and an AS cross at most ten. -/
theorem gap_six_candidate (j C A N T I v EH E F : Nat)
    (hj : 6≤j) (hC : 2≤C) (hI : 3≤I) (hv : 1≤v)
    (hA : 2*j+3≤A) (hAeq : A=N+T) (hcounts : A=EH+E+F)
    (hEH : EH≤10) (hE : E≤1) (hF : F≤j) (hT : T+3≤j)
    (h : (C : Int)^2+((j : Int)+1)^2+2*((N : Int)*(v : Int)+(I : Int))≤
      ((A : Int)-((j : Int)+1))^2+1) :
    j=6 ∧ A=17 ∧ EH=10 ∧ I≤10 := by
  let R:=(j : Int)+1
  let X:=(A : Int)-R
  let Q:=(N : Int)*(v : Int)+(I : Int)
  change (C : Int)^2+R^2+2*Q≤X^2+1 at h
  have hX0 : 0≤X := by dsimp [X,R]; omega
  have hvN := Int.mul_nonneg (show 0≤(N : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hQ : (N : Int)+(I : Int)≤Q := by dsimp [Q]; grind only
  have hj6 : j=6 := by
    by_cases hj8 : j=8
    · exfalso
      exact square_impossible R X Q (C : Int) 9 10 17 (by decide)
        (by dsimp [R]; omega) hX0 (by dsimp [X,R]; omega) (by omega) (by omega) (by decide) h
    · by_cases hj7 : j=7
      · exfalso
        by_cases h17 : A≤17
        · exact square_impossible R X Q (C : Int) 8 9 16 (by decide)
            (by dsimp [R]; omega) hX0 (by dsimp [X,R]; omega) (by omega) (by omega) (by decide) h
        · exact square_impossible R X Q (C : Int) 8 10 17 (by decide)
            (by dsimp [R]; omega) hX0 (by dsimp [X,R]; omega) (by omega) (by omega) (by decide) h
      · omega
  have hA17 : A=17 := by
    by_cases h16 : A≤16
    · exact False.elim (square_impossible R X Q (C : Int) 7 9 15 (by decide)
        (by dsimp [R]; omega) hX0 (by dsimp [X,R]; omega) (by omega) (by omega) (by decide) h)
    · omega
  have hR7 : R=7 := by dsimp [R]; omega
  have hX10 : X=10 := by dsimp [X,R]; omega
  rw [hR7,hX10] at h
  have hc := square_lower (C : Int) 2 (by decide) (by omega)
  have hQ24 : Q≤24 := by grind only
  exact ⟨hj6,hA17,by omega,by omega⟩

/-- Charging a residual local budget below the head free count. -/
theorem last_pair_budget (j T r W E : Nat) (hj : 6≤j) (hr : 4≤r)
    (hW : W≤r+5) (hfree : T+r≤j+E)
    (hcut : E≤max (T-j) (W+T-(2*j+1))+1) :
    E≤1 ∧ T+3≤j := by
  have hT : T+r≤j+1 := by
    by_cases he : T+r≤j+1
    · exact he
    · by_cases hmax : T-j≤W+T-(2*j+1)
      · rw [Nat.max_eq_right hmax] at hcut
        omega
      · rw [Nat.max_eq_left (by omega)] at hcut
        omega
  have hband : max (T-j) (W+T-(2*j+1))=0 := by
    rw [Nat.sub_eq_zero_of_le (show T≤j by omega),
      Nat.sub_eq_zero_of_le (show W+T≤2*j+1 by omega)]
  rw [hband] at hcut
  exact ⟨by omega,by omega⟩

end Recaman.GapSixScalar
