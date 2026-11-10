import Recaman.BlockSuffixPositivity

namespace Recaman.OldWindowLocalReplacement

open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

private theorem area_at_next_clock (f : Nat → Bool) (t i : Nat) (hti : t≤i) :
    Ar f t (i+1-t)=Ar f t (i-t)+(Fw f (i+1)-Fw f t) := by
  rw [show i+1-t=(i-t)+1 by omega,Ar_succ,show t+(i-t)+1=i+1 by omega]

/-- If the future drops at most one below an old starting height, a
genuine old window has a replacement starting after the block boundary.
The original area first becomes negative one clock after the new start. -/
theorem replace_old_window_at_one_below (f : Nat → Bool) (n a t b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (ht : t<n) (hnb : n≤b) (hwin : Win f t (b-t))
    (hfloor : ∀ i, n≤i → i≤b → Fw f t-1≤Fw f i) :
    ∃ u, n≤u ∧ u<b ∧ Win f u (b-u) := by
  have hpos := (block_suffix_positive_walk f 0 n a hw hpre t
    (Nat.zero_le _) (by omega)).2
  simp only [Nat.zero_add] at hpos
  have hb : n<b := by
    have hz := hwin.2.2
    by_cases h : n=b
    · rw [←h] at hz
      omega
    · omega
  have hlevel := hwin.2.1
  rw [show t+(b-t)=b by omega] at hlevel
  have hbefore := area_at_next_clock f t (b-1) (by omega)
  rw [show b-1+1=b by omega,hwin.2.2,hlevel] at hbefore
  let P := fun i => n≤i ∧ Ar f t (i-t)<0
  obtain ⟨r,hr,hP,hfirst⟩ := first_mark P (b-1) ⟨b-1,by omega,by
    exact ⟨by omega,by omega⟩⟩
  have hnr : n<r := by
    have hN := hP.1
    have hp := hP.2
    by_cases hh : n=r
    · rw [←hh] at hp
      omega
    · omega
  let u := r-1
  have hur : u+1=r := by dsimp [u]; omega
  have hnu : n≤u := by dsimp [u]; omega
  have hu0 : 0≤Ar f t (u-t) := by
    by_cases h : 0≤Ar f t (u-t)
    · exact h
    · exact (hfirst u (by omega) ⟨hnu,by omega⟩).elim
  have hstep := area_at_next_clock f t u (by omega)
  rw [hur] at hstep
  have hfr := hfloor r hP.1 (by omega)
  have har := hP.2
  have huArea : Ar f t (u-t)=0 := by omega
  have hru : Fw f r=Fw f t-1 := by omega
  have huLevel : Fw f u=Fw f t := by
    have hfu := hfloor u hnu (by omega)
    rcases fw_cases f u with ⟨hh,_⟩ | ⟨hh,_⟩ <;>
      rw [hur,hru] at hh <;> omega
  have hsplit := area_split_at f t u b (by omega) (by omega)
  rw [hwin.2.2,huArea,huLevel,Int.sub_self,Int.mul_zero] at hsplit
  exact ⟨u,hnu,by omega,by omega,by rw [show u+(b-u)=b by omega,huLevel,hlevel],by omega⟩

end Recaman.OldWindowLocalReplacement
