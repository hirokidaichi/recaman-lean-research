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
    by_cases hh : C≤5
    · exact hh
    have hC6:=Int.mul_nonneg (show 0≤C-6 by omega) (show 0≤C+6 by omega)
    exfalso
    grind only
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

end Recaman.ShortCounterFactorBounds
