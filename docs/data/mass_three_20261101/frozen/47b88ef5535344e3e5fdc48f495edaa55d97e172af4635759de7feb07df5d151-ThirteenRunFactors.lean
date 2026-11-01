import Recaman.RunSupplyKeys

namespace Recaman.ThirteenRunFactors

theorem second_double_six (M m L s q i : Int)
    (hM : 1≤M) (hm : 1≤m) (hL : 3≤L) (hs : 1≤s) (hq : 1≤q)
    (hi : 0≤i) (hiL : i<L) (hi2 : i≠2) (hsum : M+L≤12)
    (hIlo : 23≤M*(m+s)+L*s) (hIhi : M*(m+s)+L*s≤25)
    (hbal : M+i=q+m+1) (hkey : (q+m)^2=2*(M*m)+1) :
    (M=4 ∧ m=1 ∧ L=6 ∧ s=2) ∨ (M=4 ∧ m=1 ∧ L=3 ∧ s=3) ∨
    (M=6 ∧ m=2 ∧ L=5 ∧ s=1) ∨ (M=6 ∧ m=2 ∧ L=6 ∧ s=1) ∨
    (M=3 ∧ m=4 ∧ L=8 ∧ s=1) ∨ (M=3 ∧ m=4 ∧ L=9 ∧ s=1) := by
  have hp:=Int.mul_nonneg (show 0≤s-1 by omega) (show 0≤M+L by omega)
  have hcost : M*m+M+L≤25 := by grind only
  have hQ5 : q+m≤5 := by
    by_cases hh : q+m≤5
    · exact hh
    · have hn:=Int.mul_nonneg (show 0≤q+m-6 by omega) (show 0≤q+m+6 by omega)
      have hsquare : 36≤(q+m)^2 := by grind only
      omega
  have hQ : q+m=2 ∨ q+m=3 ∨ q+m=4 ∨ q+m=5 := by omega
  have hroot : q+m=3 ∨ q+m=5 := by
    rcases hQ with h|h|h|h <;> rw [h] at hkey <;> omega
  have hshape : (M=4 ∧ m=1) ∨ (M=6 ∧ m=2) ∨ (M=3 ∧ m=4) := by
    rcases hroot with h|h
    · have hMm : M*m=4 := by rw [h] at hkey; omega
      have hmv : m=1 ∨ m=2 := by omega
      rcases hmv with rfl|rfl
      · exact Or.inl ⟨by omega,rfl⟩
      · omega
    · have hMm : M*m=12 := by rw [h] at hkey; omega
      have hmv : m=1 ∨ m=2 ∨ m=3 ∨ m=4 := by omega
      rcases hmv with rfl|rfl|rfl|rfl
      · omega
      · exact Or.inr (Or.inl ⟨by omega,rfl⟩)
      · omega
      · exact Or.inr (Or.inr ⟨by omega,rfl⟩)
  rcases hshape with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have hp:=Int.mul_nonneg (show 0≤L-3 by omega) (show 0≤s by omega)
    have hsv : s=1 ∨ s=2 ∨ s=3 := by grind only
    rcases hsv with rfl|rfl|rfl
    · omega
    · exact Or.inl ⟨rfl,rfl,by omega,rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl,by omega,rfl⟩)
  · have hp:=Int.mul_nonneg (show 0≤L-3 by omega) (show 0≤s by omega)
    have hs1 : s=1 := by grind only
    subst s
    have hv : L=5 ∨ L=6 := by omega
    rcases hv with rfl|rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,rfl⟩)))
  · have hL4 : 4≤L := by omega
    have hp:=Int.mul_nonneg (show 0≤L-4 by omega) (show 0≤s by omega)
    have hs1 : s=1 := by grind only
    subst s
    have hv : L=8 ∨ L=9 := by omega
    rcases hv with rfl|rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,rfl,rfl⟩))))

end Recaman.ThirteenRunFactors
