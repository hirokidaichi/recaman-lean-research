import Recaman.BlockSuffixPositivity

namespace Recaman.SevenWindowPrefixFive

open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private theorem five_step_minus_one (f : Nat → Bool) (t : Nat)
    (hRise : Fw f (t+5)=Fw f t+1) (hArea : Ar f t 5= -1) :
    f t=false ∧ f (t+1)=true ∧ f (t+2)=false ∧ f (t+3)=true ∧ f (t+4)=true := by
  have h0 := fw_cases f t
  have h1 := fw_cases f (t+1)
  have h2 := fw_cases f (t+2)
  have h3 := fw_cases f (t+3)
  have h4 := fw_cases f (t+4)
  rw [show t+1+1=t+2 by omega] at h1
  rw [show t+2+1=t+3 by omega] at h2
  rw [show t+3+1=t+4 by omega] at h3
  rw [show t+4+1=t+5 by omega] at h4
  have hExpand : Ar f t 5=(Fw f (t+1)-Fw f t)+(Fw f (t+2)-Fw f t)+
      (Fw f (t+3)-Fw f t)+(Fw f (t+4)-Fw f t)+(Fw f (t+5)-Fw f t) := by
    simp [Ar]
  rw [hExpand] at hArea
  rcases h0 with ⟨h0,a0⟩ | ⟨h0,a0⟩ <;>
    rcases h1 with ⟨h1,a1⟩ | ⟨h1,a1⟩ <;>
    rcases h2 with ⟨h2,a2⟩ | ⟨h2,a2⟩ <;>
    rcases h3 with ⟨h3,a3⟩ | ⟨h3,a3⟩ <;>
    rcases h4 with ⟨h4,a4⟩ | ⟨h4,a4⟩ <;>
    first
    | exact ⟨a0,a1,a2,a3,a4⟩
    | (exfalso; omega)

/-- A complete five-sign linear certificate identifies the original
length-seven window ending S,A, without a reverse-word area interface. -/
theorem actual_seven_ending_SA (f : Nat → Bool) (t : Nat) (hWin : Win f t 7)
    (hS : f (t+5)=false) (hA : f (t+6)=true) :
    seg f t 7=[false,true,false,true,true,false,true] := by
  have h5 := fw_cases f (t+5)
  have h6 := fw_cases f (t+6)
  have hStepS : Fw f (t+6)=Fw f (t+5)-1 := by
    rcases h5 with ⟨_,h⟩ | ⟨h,_⟩
    · simp [hS] at h
    · simpa only [show t+5+1=t+6 by omega] using h
  have hStepA : Fw f (t+7)=Fw f (t+6)+1 := by
    rcases h6 with ⟨h,_⟩ | ⟨_,h⟩
    · simpa only [show t+6+1=t+7 by omega] using h
    · simp [hA] at h
  have hRise := hWin.2.1
  have hAr := hWin.2.2
  change Ar f t 5+(Fw f (t+6)-Fw f t)+(Fw f (t+7)-Fw f t)=0 at hAr
  obtain ⟨h0,h1,h2,h3,h4⟩ := five_step_minus_one f t (by omega) (by omega)
  change [f (t+0),f (t+1),f (t+2),f (t+3),f (t+4),f (t+5),f (t+6)]=_
  simp only [Nat.add_zero,h0,h1,h2,h3,h4,hS,hA]

end Recaman.SevenWindowPrefixFive
