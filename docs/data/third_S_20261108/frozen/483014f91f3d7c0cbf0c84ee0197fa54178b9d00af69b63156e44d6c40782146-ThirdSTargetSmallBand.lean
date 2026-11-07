import Recaman.MixedShortAPairBudget

namespace Recaman.ThirdSTargetSmallBand

/-- Complete arithmetic certificate for 6 p values, 6 R values and
5 v values. Original histories are not enumerated. -/
private theorem target_certificate :
    ∀ p∈([6,7,8,9,10,11] : List Int), ∀ R∈([5,6,7,8,9,10] : List Int),
      ∀ v∈([1,2,3,4,5] : List Int), R<p →
      (p^2-R^2)%(2*v)=0 → 2*v*p≤p^2-R^2 → p^2-R^2<2*v*(p+R) →
      (p=11 ∧ R=5 ∧ v=4) ∨ (p=11 ∧ R=7 ∧ v=3) := by decide

/-- Pure arithmetic support only. Every input is internally supplied
from the same actual target and measured counts in the main theorem. -/
theorem small_target_band (p R U v T : Int)
    (hp : 6≤p) (hp11 : p≤11) (hR : 5≤R) (hRp : R<p)
    (hU : p≤U) (hv : 1≤v) (hT : 1≤T)
    (hbal : T+U=R+p) (hsq : p^2=R^2+2*U*v) :
    (p=11 ∧ R=5 ∧ U=12 ∧ v=4 ∧ T=4) ∨
    (p=11 ∧ R=7 ∧ U=12 ∧ v=3 ∧ T=6) := by
  have hv5 : v≤5 := by
    by_cases h : v≤5
    · exact h
    · have hp1:=Int.mul_nonneg (show 0≤U-p by omega) (show 0≤v by omega)
      have hp2:=Int.mul_nonneg (show 0≤p by omega) (show 0≤v-6 by omega)
      have hp3:=Int.mul_pos (show 0<p by omega) (show 0<12-p by omega)
      have hr2:=Recaman.ShortCounterFactorBounds.square_lower R 0 (by decide) (by omega)
      grind only
  have hD : p^2-R^2=(2*v)*U := by grind only
  have hmod : (p^2-R^2)%(2*v)=0 := by rw [hD]; simp [Int.mul_emod]
  have hlo : 2*v*p≤p^2-R^2 := by
    have he:=Int.mul_nonneg (show 0≤2*v by omega) (show 0≤U-p by omega)
    grind only
  have hhi : p^2-R^2<2*v*(p+R) := by
    have he:=Int.mul_pos (show 0<2*v by omega) (show 0<p+R-U by omega)
    grind only
  have hp_mem : p∈([6,7,8,9,10,11] : List Int) := by
    simp only [List.mem_cons,List.mem_singleton]; omega
  have hR_mem : R∈([5,6,7,8,9,10] : List Int) := by
    simp only [List.mem_cons,List.mem_singleton]; omega
  have hv_mem : v∈([1,2,3,4,5] : List Int) := by
    simp only [List.mem_cons,List.mem_singleton]; omega
  rcases target_certificate p hp_mem R hR_mem v hv_mem hRp hmod hlo hhi with h1|h2
  · obtain ⟨rfl,rfl,rfl⟩:=h1
    have hU12 : U=12 := by grind only
    exact Or.inl ⟨rfl,rfl,hU12,rfl,by omega⟩
  · obtain ⟨rfl,rfl,rfl⟩:=h2
    have hU12 : U=12 := by grind only
    exact Or.inr ⟨rfl,rfl,hU12,rfl,by omega⟩

end Recaman.ThirdSTargetSmallBand
