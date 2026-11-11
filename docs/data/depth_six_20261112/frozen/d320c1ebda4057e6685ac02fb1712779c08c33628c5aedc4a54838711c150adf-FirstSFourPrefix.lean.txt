import Recaman.LevelTriangleArea

namespace Recaman.FirstSFourPrefix

open Recaman.LevelTriangleArea Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality

/-- Four original signs beginning S and ending two levels lower have
only these three forms. -/
theorem first_S_four_words (f : Nat → Bool) (n : Nat) (hS : f n=false)
    (hEnd : Fw f (n+4)=Fw f n-2) :
    seg f n 4=[false,true,false,false] ∨ seg f n 4=[false,false,true,false] ∨
      seg f n 4=[false,false,false,true] := by
  have h0 : Fw f (n+1)=Fw f n-1 := by
    rcases fw_cases f n with ⟨_,h⟩ | ⟨h,_⟩
    · simp [hS] at h
    · exact h
  have h1 := fw_cases f (n+1)
  have h2 := fw_cases f (n+2)
  have h3 := fw_cases f (n+3)
  rw [show n+1+1=n+2 by omega] at h1
  rw [show n+2+1=n+3 by omega] at h2
  rw [show n+3+1=n+4 by omega] at h3
  have hWord : seg f n 4=[false,f (n+1),f (n+2),f (n+3)] := by
    change [f (n+0),f (n+1),f (n+2),f (n+3)]=_
    rw [Nat.add_zero,hS]
  rcases h1 with ⟨h1,a1⟩ | ⟨h1,a1⟩ <;>
    rcases h2 with ⟨h2,a2⟩ | ⟨h2,a2⟩ <;>
    rcases h3 with ⟨h3,a3⟩ | ⟨h3,a3⟩ <;>
    simp [hWord,a1,a2,a3] <;> omega

/-- The common source-relative area of that original four-clock prefix
is at most four. This is a word lemma, not an orbit reachability claim. -/
theorem first_S_four_area_le_four (f : Nat → Bool) (n : Nat) (hS : f n=false)
    (hEnd : Fw f (n+4)=Fw f n-2) :
    areaFromLevel f n (Fw f n-2) 4≤4 := by
  unfold areaFromLevel
  rw [show Fw f n-(Fw f n-2)=2 by omega,Ar_areaW]
  rcases first_S_four_words f n hS hEnd with h | h | h <;> rw [h] <;> decide

/-- No clock before that original four-sign source is above the boundary. -/
theorem first_S_four_ceiling (f : Nat → Bool) (n : Nat) (hS : f n=false)
    (hEnd : Fw f (n+4)=Fw f n-2) :
    ∀ i, n≤i → i<n+4 → Fw f i≤Fw f n := by
  have hCount := cN_walk f n 4
  rw [hEnd] at hCount
  have hA : cN (fun i => f i=true) n 4=1 := by omega
  have hS1 : cN (fun i => f i=false) n 1=1 := by
    rw [cN_succ_pos _ n 0 (by rwa [Nat.add_zero])]
    rfl
  intro i hni hin
  by_cases h : i=n
  · rw [h]
    omega
  · have hAW := count_prefix_le (fun i => f i=true) n (i-n) 4 (by omega)
    have hSW := count_prefix_le (fun i => f i=false) n 1 (i-n) (by omega)
    have hi := cN_walk f n (i-n)
    rw [show n+(i-n)=i by omega] at hi
    omega

end Recaman.FirstSFourPrefix
