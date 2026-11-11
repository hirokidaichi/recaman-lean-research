import Recaman.DepthSixOldHead

namespace Recaman.DepthSixFirstHead

open Recaman.DepthSixOldHead Recaman.DepthSixGapResidual Recaman.DepthSixFreeLocation
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The first addition of any depth-six gap-six positive counter is
preceded by exactly five or six original subtractions. -/
theorem gap_six_first_addition_head (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+6 → f i=false) (he : EndN f 0 (b+6))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤6) :
    ∃ h, (h=5 ∨ h=6) ∧ n+h<b ∧
      (∀ i, n≤i → i<n+h → f i=false) ∧ f (n+h)=true := by
  obtain ⟨_,_,_,htarget,_⟩ := positive_depth_six_counter_profile f n a b 6 hw hpre
    hnb hfloor hpos hS he hcounter
  have hdown := fw_false_run f b 6 hS
  have hHigh := positive_depth_six_counter_high_free f n a b 6 hw hpre hnb hfloor hpos hS he hcounter
  simp only [if_true] at hHigh
  have hb : Fw f n+1≤Fw f b := by omega
  obtain ⟨i,hni,hib,_,hiA⟩ := ivt f b (Fw f n+1) hb (b-n) n (by omega) (by omega)
  let P := fun u => n≤u ∧ f u=true
  obtain ⟨u,hub,hu,hfirst⟩ := first_mark P (b-1) ⟨i,by omega,hni,hiA⟩
  have hnu := hu.1
  have huA := hu.2
  have hBefore (i : Nat) (hni : n≤i) (hiu : i<u) : f i=false := by
    cases hA : f i
    · rfl
    · exact (hfirst i hiu ⟨hni,hA⟩).elim
  have huWalk := fw_false_run f n (u-n) (fun i hi hj => hBefore i hi (by omega))
  rw [show n+(u-n)=u by omega] at huWalk
  have hNo : ¬EndN f 0 u := by
    apply block_prefix_low_clock_not_endable f n a u hw hpre hnu (Fw f u)
    · intro i hni hiu
      have hiWalk := fw_false_run f n (i-n) (fun z hz hzj => hBefore z hz (by omega))
      rw [show n+(i-n)=i by omega] at hiWalk
      omega
    · omega
  have hLow : Fw f u≤Fw f n-5 := by
    by_cases h : Fw f u≤Fw f n-5
    · exact h
    · exact (not_of_cN_zero (fun i => Fw f n-4≤Fw f i ∧ f i=true ∧ ¬EndN f 0 i)
        n (b-n) (by omega) u hnu (by omega) ⟨by omega,huA,hNo⟩).elim
  have hMin := hfloor u hnu (by omega)
  refine ⟨u-n,by omega,by omega,?_,?_⟩
  · intro i hni hiu
    exact hBefore i hni (by omega)
  · rwa [show n+(u-n)=u by omega]

/-- If the same final target has an old source, the five-subtraction
head is excluded and the original counter starts with six S and an A. -/
theorem old_gap_six_first_head_six (f : Nat → Bool) (n a b t : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+6 → f i=false) (he : EndN f 0 (b+6))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤6)
    (htn : t<n) (hwin : Win f t (b+6-t)) :
    n+6<b ∧ (∀ i, n≤i → i<n+6 → f i=false) ∧ f (n+6)=true := by
  obtain ⟨h,hh,hnbh,hHead,hA⟩ := gap_six_first_addition_head f n a b hw hpre
    hnb hfloor hpos hS he hcounter
  rcases hh with rfl | rfl
  · exact (old_gap_six_excludes_head_five f n a b t hw hpre hnb hfloor hpos hS he
      hcounter htn hwin hnbh hHead hA).elim
  · exact ⟨hnbh,hHead,hA⟩

end Recaman.DepthSixFirstHead
