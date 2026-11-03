import Recaman.MassTwoSmallHeadKey

namespace Recaman.UnitTargetSmallHeadKey

theorem small_head_residual (S v R K r : Int)
    (hS : 3≤S) (hv : 1≤v) (hR : 5≤R) (hK : 3≤K)
    (hr : 0≤r) (hr3 : r≤3) (hSv : r+v≤6) (hSr : S≤2*r+1)
    (hkey : R^2=S^2+v^2-2*(S+v)-2*K) :
    r=3 ∧ S=7 ∧ v=2 ∧ R=5 ∧ K=5 := by
  have hR25:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hr123 : r=1 ∨ r=2 ∨ r=3 := by omega
  have hrval : r=3 := by
    rcases hr123 with hr1|hr2|hr3
    · have hs3:=Int.mul_nonneg (show 0≤3-S by omega) (show 0≤S+1 by omega)
      have hv5:=Int.mul_nonneg (show 0≤5-v by omega) (show 0≤v+3 by omega)
      grind only
    · have hs5:=Int.mul_nonneg (show 0≤5-S by omega) (show 0≤S+3 by omega)
      have hv4:=Int.mul_nonneg (show 0≤4-v by omega) (show 0≤v+2 by omega)
      grind only
    · exact hr3
  have hv3 : v≤3 := by omega
  have hs7:=Int.mul_nonneg (show 0≤7-S by omega) (show 0≤S+5 by omega)
  have hvv:=Int.mul_nonneg (show 0≤3-v by omega) (show 0≤v+1 by omega)
  have hR5 : R=5 := by
    by_cases he : R=5
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤R-6 by omega) (show 0≤R+6 by omega)
      grind only
  have hS7 : S=7 := by
    by_cases he : S=7
    · exact he
    · have hp:=Int.mul_nonneg (show 0≤6-S by omega) (show 0≤S+4 by omega)
      grind only
  rw [hR5,hS7] at hkey
  have hv123 : v=1 ∨ v=2 ∨ v=3 := by omega
  rcases hv123 with hv1|hv2|hv3
  · rw [hv1] at hkey
    omega
  · rw [hv2] at hkey
    exact ⟨hrval,hS7,hv2,hR5,by omega⟩
  · rw [hv3] at hkey
    omega

end Recaman.UnitTargetSmallHeadKey
