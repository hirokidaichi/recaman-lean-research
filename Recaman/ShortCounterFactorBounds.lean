import Recaman.RunSupplyKeys

namespace Recaman.ShortCounterFactorBounds

/-- Arithmetic support for the actual-history cut. This helper alone is
not a registered research result; actual count bounds must be supplied. -/
theorem factor_cuts (S C v R : Int) (hS : 0<S) (hC : 4≤C)
    (hv : 1≤v) (hvC : v<C) (hR : 5≤R)
    (hcircle : R^2+C^2+2*C*v-v^2-1≤(S-C)^2)
    (hfour : S+v≤C+13) (hthree : v+2≤C → S+v≤C+12) :
    2*C<S ∧ (C=v+1 → C≤5) ∧ (v+2≤C → v≤3) := by
  have hRR:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hCv:=Int.mul_nonneg (show 0≤v by omega) (show 0≤2*C-v by omega)
  have hSC : 2*C<S := by
    by_cases hh : 2*C<S
    · exact hh
    have hp:=Int.mul_nonneg (show 0≤S by omega) (show 0≤2*C-S by omega)
    exfalso
    grind only
  refine ⟨hSC,?_,?_⟩
  · intro hclose
    have hx : 0<S-C := by omega
    have hxB : S-C≤14-C := by omega
    have hp:=Int.mul_nonneg (show 0≤(14-C)-(S-C) by omega)
      (show 0≤(14-C)+(S-C) by omega)
    have hsq : (S-C)^2≤(14-C)^2 := by
      have heq : (14-C)^2-(S-C)^2=((14-C)-(S-C))*((14-C)+(S-C)) := by grind only
      omega
    have hform : R^2+C^2+2*C*v-v^2-1=R^2+2*C^2-2 := by
      rw [hclose]
      grind only
    have hupper : (14-C)^2=196-28*C+C^2 := by grind only
    have hbound : R^2+C^2+28*C≤198 := by omega
    by_cases hh : C≤5
    · exact hh
    have hC6:=Int.mul_nonneg (show 0≤C-6 by omega) (show 0≤C+6 by omega)
    have heC : (C-6)*(C+6)=C^2-36 := by grind only
    have heR : (R-5)*(R+5)=R^2-25 := by grind only
    omega
  · intro hdeep
    have hsize:=hthree hdeep
    have hx : 0<S-C := by omega
    have hxB : S-C≤12-v := by omega
    have hp:=Int.mul_nonneg (show 0≤(12-v)-(S-C) by omega)
      (show 0≤(12-v)+(S-C) by omega)
    by_cases hh : v≤3
    · exact hh
    have hC2:=Int.mul_nonneg (show 0≤C-(v+2) by omega) (show 0≤C+(v+2) by omega)
    have hCv2:=Int.mul_nonneg (show 0≤C-(v+2) by omega) (show 0≤v by omega)
    have hv4:=Int.mul_nonneg (show 0≤v-4 by omega) (show 0≤v+4 by omega)
    exfalso
    grind only

/-- A square comparison retains the sign of both factors. -/
theorem square_lower (x a : Int) (ha : 0≤a) (hxa : a≤x) : a^2≤x^2 := by
  have hp:=Int.mul_nonneg (show 0≤x-a by omega) (show 0≤x+a by omega)
  have he : (x-a)*(x+a)=x^2-a^2 := by grind only
  omega

theorem close_quadratic (S C v R : Int) (hSC : 2*C<S) (hC : 0≤C)
    (hclose : C=v+1) (hsize : S+v≤C+13)
    (hcircle : R^2+C^2+2*C*v-v^2-1≤(S-C)^2) :
    R^2+C^2+28*C≤198 := by
  have hx : 0≤S-C := by omega
  have hupper : S-C≤14-C := by omega
  have hsq:=square_lower (14-C) (S-C) hx hupper
  have hf : R^2+C^2+2*C*v-v^2-1=R^2+2*C^2-2 := by rw [hclose]; grind only
  have he : (14-C)^2=196-28*C+C^2 := by grind only
  omega

theorem deep_quadratic (S C v R : Int) (hSC : 2*C<S) (hC : 0≤C)
    (hsize : S+v≤C+12)
    (hcircle : R^2+C^2+2*C*v-v^2-1≤(S-C)^2) :
    R^2+(C-v)^2+4*(C-v)*v+v^2+24*v≤145 := by
  have hx : 0≤S-C := by omega
  have hupper : S-C≤12-v := by omega
  have hsq:=square_lower (12-v) (S-C) hx hupper
  have he : (12-v)^2=144-24*v+v^2 := by grind only
  have hf : R^2+(C-v)^2+4*(C-v)*v+v^2+24*v =
      R^2+C^2+2*C*v-v^2-1-(144-24*v+v^2)+145 := by grind only
  omega

end Recaman.ShortCounterFactorBounds
