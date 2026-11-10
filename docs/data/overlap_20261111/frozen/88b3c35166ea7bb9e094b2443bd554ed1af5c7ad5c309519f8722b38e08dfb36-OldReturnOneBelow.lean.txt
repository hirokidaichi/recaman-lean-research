import Recaman.BlockSameMassSpan

namespace Recaman.OldReturnOneBelow

open Recaman.BlockSameMassSpan Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.LeadingRunSupply Recaman.CapacityEqualityInduction

private theorem adjacent_level_budget (f : Nat → Bool) (b k : Nat)
    (h1 : Fw f b-1≤Fw f (b+k+1)) (h2 : Fw f b-1≤Fw f (b+k+2)) :
    Fw f b*2-1≤Fw f (b+k+1)+Fw f (b+k+2) := by
  rcases fw_cases f (b+k+1) with ⟨h,_⟩ | ⟨h,_⟩ <;>
    rw [show b+k+1+1=b+k+2 by omega] at h <;> omega

private theorem paired_area (f : Nat → Bool) (b : Nat) (hA : f b=true) :
    ∀ k : Nat, (∀ i : Nat, i≤2*k+2 → Fw f b-1≤Fw f (b+i)) →
      (k : Int)+3≤Ar f b (2*k+2)+((2*k+2 : Nat) : Int) := by
  have hfirst : Fw f (b+1)=Fw f b+1 := by
    rcases fw_cases f b with ⟨h,_⟩ | ⟨_,h⟩
    · exact h
    · simp [hA] at h
  intro k
  induction k with
  | zero =>
    intro _
    change 3≤Ar f b 2+2
    rw [Ar2,hfirst]
    rcases fw_cases f (b+1) with ⟨h,_⟩ | ⟨h,_⟩ <;>
      rw [show b+1+1=b+2 by omega,hfirst] at h <;> omega
  | succ k ih =>
    intro h
    have hp := ih (fun i hi => h i (by omega))
    have h1 : Fw f b-1≤Fw f (b+(2*k+2)+1) := by
      rw [show b+(2*k+2)+1=b+(2*k+3) by omega]
      exact h (2*k+3) (by omega)
    have h2 : Fw f b-1≤Fw f (b+(2*k+2)+2) := by
      rw [show b+(2*k+2)+2=b+(2*k+4) by omega]
      exact h (2*k+4) (by omega)
    have hadd := adjacent_level_budget f b (2*k+2) h1 h2
    have hl : 2*(k+1)+2=(2*k+2)+1+1 := by omega
    rw [hl,Ar_succ,Ar_succ,show b+(2*k+2+1)+1=b+(2*k+2)+2 by omega]
    omega

/-- An original same-level old return confined to one step below its
endpoint has gap two, or gap four with both middle signs subtractions. -/
theorem old_return_gap_one_below (f : Nat → Bool) (n a t u b c : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (ht : t<n) (hu : u<n) (hnb : n≤b) (hbc : b<c)
    (hwb : Win f t (b-t)) (hwc : Win f u (c-u)) (hlevel : Fw f b=Fw f c)
    (hA : f b=true) (hfloor : ∀ i, i≤c-b → Fw f b-1≤Fw f (b+i)) :
    c=b+2 ∨ (c=b+4 ∧ f (b+1)=false ∧ f (b+2)=false ∧ f (b+3)=true) := by
  have hold := same_level_old_window_areas f n a t u b c hw hpre ht hu hnb
    (by omega) hwb hwc hlevel
  have hs := area_split_at f n b c hnb (by omega)
  have hlen : ((c-n : Nat) : Int)=((b-n : Nat) : Int)+((c-b : Nat) : Int) := by omega
  rw [hlen,Int.add_mul,hs,hlevel] at hold
  have he :
      ((c-b : Nat) : Int)*(Fw f n-Fw f c+1)
        + ((c-b : Nat) : Int)*(Fw f c-Fw f n) = (c-b : Nat) := by
    rw [←Int.mul_add,show Fw f n-Fw f c+1+(Fw f c-Fw f n)=1 by omega,Int.mul_one]
  have hband : Ar f b (c-b)+(c-b : Nat)≤4 := by omega
  have hpar := mass_eq (seg f b (c-b))
  rw [seg_length,seg_mass,show b+(c-b)=c by omega,←hlevel] at hpar
  let k := (c-b-2)/2
  have hk : 2*k+2=c-b := by dsimp [k]; omega
  have hlo := paired_area f b hA k
  rw [hk] at hlo
  have hlo := hlo hfloor
  by_cases h2 : c=b+2
  · exact Or.inl h2
  · have h4 : c=b+4 := by omega
    have hArea : Ar f b 4≤0 := by
      rw [show c-b=4 by omega] at hband
      omega
    have hfirst : Fw f (b+1)=Fw f b+1 := by
      rcases fw_cases f b with ⟨h,_⟩ | ⟨_,h⟩
      · exact h
      · simp [hA] at h
    rw [Ar4,hfirst,←h4,←hlevel] at hArea
    have hlow := hfloor 3 (by omega)
    have hS1 : f (b+1)=false := by
      rcases fw_cases f (b+1) with ⟨h,_⟩ | ⟨_,h⟩
      · rw [show b+1+1=b+2 by omega,hfirst] at h
        omega
      · exact h
    have hf2 : Fw f (b+2)=Fw f b := by
      rcases fw_cases f (b+1) with ⟨_,h⟩ | ⟨h,_⟩
      · simp [hS1] at h
      · rw [show b+1+1=b+2 by omega,hfirst] at h
        omega
    have hS2 : f (b+2)=false := by
      rcases fw_cases f (b+2) with ⟨h,_⟩ | ⟨_,h⟩
      · rw [show b+2+1=b+3 by omega,hf2] at h
        omega
      · exact h
    have hA3 : f (b+3)=true := by
      rcases fw_cases f (b+2) with ⟨_,h⟩ | ⟨hF3,_⟩
      · simp [hS2] at h
      · rw [show b+2+1=b+3 by omega,hf2] at hF3
        rcases fw_cases f (b+3) with ⟨_,h⟩ | ⟨hF4,_⟩
        · exact h
        · rw [show b+3+1=c by omega,←hlevel,hF3] at hF4
          omega
    exact Or.inr ⟨h4,hS1,hS2,hA3⟩

end Recaman.OldReturnOneBelow
