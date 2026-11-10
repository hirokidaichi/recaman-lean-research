import Recaman.DepthSixSourceClock

namespace Recaman.DepthSixSourceArea

open Recaman.LeadingRunSupply
open Recaman.DepthSixSourceClock Recaman.DepthSixGapResidual Recaman.LevelTriangleArea
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The gap-six target of an original depth-six positive counter has one
of three source-area values. Old sources have the two exact mass-two
suffix areas; local sources start at the internally supplied second clock. -/
theorem gap_six_actual_source_area_spectrum (f : Nat → Bool) (n a b : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+6 → f i=false) (he : EndN f 0 (b+6))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤6) :
    areaFromLevel f n (Fw f n-2) (b+6-n)= -3 ∨
      areaFromLevel f n (Fw f n-2) (b+6-n)= -2 ∨
      areaFromLevel f n (Fw f n-2) (b+6-n)=1 := by
  obtain ⟨_,_,_,htarget,_⟩ := positive_depth_six_counter_profile f n a b 6 hw hpre
    hnb hfloor hpos hS he hcounter
  obtain ⟨_,t,k,_,htk,hk,hLev,hArea⟩ := he
  rw [htk] at hLev
  have htb : t<b := by
    by_cases h : t<b
    · exact h
    · have h1 := fw_false_run f b (t-b) (fun i hi hj => hS i hi (by omega))
      rw [show b+(t-b)=t by omega] at h1
      have h2 := fw_false_run f b 6 hS
      omega
  have hwin : Win f t (b+6-t) := by
    rw [show b+6-t=k by omega]
    exact ⟨hk,by rwa [htk],hArea⟩
  have htF : Fw f t=Fw f n-2 := by omega
  by_cases htn : t<n
  · have hfull : BlockWord (seg f 0 n) := by
      rw [hpre]
      exact block_append hw (block_replicate_A a)
    have hsplit := suffix_split f 0 n t (by omega) (by omega)
    simp only [Nat.zero_add,Nat.sub_zero] at hsplit
    have hsuffix := block_suffix hfull _ _ hsplit.symm
    have hmass : mass (seg f t (n-t))=2 := by
      rw [seg_mass,show t+(n-t)=n by omega,htF]
      omega
    have hOldArea : Ar f t (n-t)=3 ∨ Ar f t (n-t)=2 := by
      rw [Ar_areaW]
      rcases block_mass_two hsuffix hmass with hAA | hSA
      · left
        rw [hAA]
        decide
      · right
        rw [hSA]
        decide
    have hsum := area_split_at f t n (b+6) (by omega) (by omega)
    rw [show b+6-t=k by omega,hArea,htF] at hsum
    have hDelta : Fw f n-(Fw f n-2)=2 := by omega
    rw [hDelta] at hsum
    unfold areaFromLevel
    have hDiff : Fw f n-(Fw f n-2)=2 := by omega
    rw [hDiff]
    rcases hOldArea with h3 | h2
    · left; omega
    · right; left; omega
  · have hnt : n≤t := by omega
    obtain ⟨hTime,hFirstS⟩ := gap_six_local_source_clock_two f n a b t hw hpre
      hnb hfloor hpos hS (show EndN f 0 (b+6) from ⟨by assumption,t,k,by omega,htk,hk,by rwa [htk],hArea⟩)
      hcounter hnt htb hwin
    have hfirstWord : seg f n 2=List.replicate 2 false :=
      seg_false f n 2 (fun i hi hj => hFirstS i hi (by omega))
    have hFirstArea : Ar f n (t-n)= -3 := by
      rw [show t-n=2 by omega,Ar_areaW,hfirstWord]
      decide
    have hsum := area_split_at f n t (b+6) hnt (by omega)
    rw [hFirstArea,show b+6-t=k by omega,hArea,htF] at hsum
    have hDelta : (Fw f n-2)-Fw f n= -2 := by omega
    rw [hDelta] at hsum
    right; right
    unfold areaFromLevel
    have hDiff : Fw f n-(Fw f n-2)=2 := by omega
    rw [hDiff]
    omega

end Recaman.DepthSixSourceArea
