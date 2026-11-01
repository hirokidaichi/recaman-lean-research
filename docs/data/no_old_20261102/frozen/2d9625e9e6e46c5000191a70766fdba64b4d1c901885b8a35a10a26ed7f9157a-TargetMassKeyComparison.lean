import Recaman.MomentTargetProfile

namespace Recaman.TargetMassKeyComparison

/-- Increasing the measured target mass above three only lowers the
same-target key at fixed separator difference. No other old mass is cut. -/
theorem target_mass_key_upper (ku kz C S v R d : Int)
    (hC : 3≤C) (hS : 0≤S) (hv : v=C+d)
    (he : ku= -kz-4*C*(S+v)+2*v^2-2*R^2) :
    ku≤ -kz-12*S-18+2*d^2-2*R^2 := by
  have hp:=Int.mul_nonneg (show 0≤C-3 by omega) (show 0≤C+3+2*S by omega)
  grind only

end Recaman.TargetMassKeyComparison
