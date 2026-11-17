import Recaman.FloorVisitFreeCount

namespace Recaman.FivePeriodSourceCost

open Recaman.SingleWindowEquality Recaman.BlockSuffixPositivity
open Recaman.CapacityEqualityInduction Recaman.LowFreeFourFloor
open Recaman.FloorVisitFreeCount Recaman.SuffixHallOwnerMap
open Recaman.LeadingRunSupply

set_option maxHeartbeats 2000000

private def fivePeriods : List Bool :=
  (List.replicate 5 [true,false,false,false,false,true,true,true]).flatten

private theorem prefix_floor : ∀ k : Fin 41, -3≤mass (fivePeriods.take k.val) := by decide

private theorem first_family : ∀ j : Fin 5,
    mass (fivePeriods.take (8*j.val+5)) = -3 ∧
    areaW (fivePeriods.take (8*j.val+5)) = -((8*j.val+5 : Nat) : Int) := by decide

/-- Every original source, including every alternative witness, of the
first family lies before T and has its prescribed height and area key. -/
theorem plateau_source_key (f : Nat → Bool) (T j u k : Nat)
    (hword : seg f T 40 =
      (List.replicate 5 [true,false,false,false,false,true,true,true]).flatten)
    (hj : j<5) (huk : u+k=T+8*j+5) (hw : Win f u k) :
    u<T ∧ Fw f u=Fw f T-4 ∧ Ar f u (T-u)=-(24*(j : Int)+15) := by
  have htake := seg_take f T 40 (8*j+5) (by omega)
  change seg f T 40=fivePeriods at hword
  rw [hword] at htake
  have hfirst := first_family ⟨j,hj⟩
  change mass (fivePeriods.take (8*j+5)) = -3 ∧
    areaW (fivePeriods.take (8*j+5)) = -((8*j+5 : Nat) : Int) at hfirst
  rw [htake,seg_mass,←Ar_areaW] at hfirst
  have hwinF := hw.2.1
  rw [huk] at hwinF
  have hsrc : Fw f u=Fw f T-4 := by
    rw [show T+(8*j+5)=T+8*j+5 by omega] at hfirst
    omega
  have huT : u<T := by
    by_cases h : u<T
    · exact h
    · have hub : u-T<41 := by have := hw.1; omega
      have hp := prefix_floor ⟨u-T,hub⟩
      change -3≤mass (fivePeriods.take (u-T)) at hp
      have ht := seg_take f T 40 (u-T) (by omega)
      rw [hword] at ht
      rw [ht,seg_mass,Nat.add_sub_cancel' (by omega : T≤u)] at hp
      omega
  have ha := area_split_at f u T (T+8*j+5) (by omega) (by omega)
  rw [show T+8*j+5-u=k by omega,hw.2.2,
    show T+8*j+5-T=8*j+5 by omega,hfirst.2] at ha
  have hd : Fw f T-Fw f u=4 := by omega
  rw [hd] at ha
  simp only [Int.natCast_add,Int.natCast_mul] at ha
  exact ⟨huT,hsrc,by omega⟩

private theorem count_filter (P : Nat → Prop) : ∀ K,
    cN P 0 K=((List.range K).filter (fun i => @decide (P i) (Classical.propDecidable _))).length
  | 0 => rfl
  | k+1 => by
    have ih := count_filter P k
    by_cases h : P k
    · rw [cN_succ_pos P 0 k (by simpa using h),ih]
      simp [List.range_succ,List.filter_append,h]
    · rw [cN_succ_neg P 0 k (by simpa using h),ih]
      simp [List.range_succ,List.filter_append,h]

theorem five_distinct_original_sources (f : Nat → Bool) (T : Nat)
    (hword : seg f T 40 =
      (List.replicate 5 [true,false,false,false,false,true,true,true]).flatten)
    (hactual : ∀ j, j<5 → EndN f 0 (T+8*j+5)) :
    5≤cN (fun u => Fw f u=Fw f T-4) 0 T := by
  classical
  have hex (j : Nat) (hj : j<5) :
      ∃ u, u<T ∧ Fw f u=Fw f T-4 ∧ Ar f u (T-u)=-(24*(j : Int)+15) := by
    obtain ⟨_,u,k,_,huk,hw⟩ := hactual j hj
    exact ⟨u,plateau_source_key f T j u k hword hj huk hw⟩
  let src := fun j => if hj : j<5 then Classical.choose (hex j hj) else 0
  have hsrc (j : Nat) (hj : j<5) :
      src j<T ∧ Fw f (src j)=Fw f T-4 ∧ Ar f (src j) (T-src j)=-(24*(j : Int)+15) := by
    simp only [src,dif_pos hj]
    exact Classical.choose_spec (hex j hj)
  have hn := nodup_map_of_inj (List.range 5) src List.nodup_range (by
    intro i hi j hj he
    have hki := (hsrc i (List.mem_range.mp hi)).2.2
    have hkj := (hsrc j (List.mem_range.mp hj)).2.2
    rw [he] at hki
    omega)
  let L := (List.range T).filter
    (fun u => @decide (Fw f u=Fw f T-4) (Classical.propDecidable _))
  have hsub : (List.range 5).map src ⊆ L := by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hu
    have hs := hsrc j (List.mem_range.mp hj)
    simp only [L,List.mem_filter,List.mem_range,decide_eq_true_eq]
    exact ⟨hs.1,hs.2.1⟩
  have hl := hn.length_le_of_subset hsub
  rw [count_filter]
  simpa only [L,List.length_map,List.length_range] using hl

/-- The literal five-period inventory forces five original low free A.
Only the first family is needed, so imposing the second family and all
boundary-source conditions cannot restore a low-free-four example. -/
theorem five_periods_need_five_low_free (f : Nat → Bool) (h T : Nat)
    (hh : 1≤h) (hS : ∀ i, i<h → f i=false) (hend : Fw f T=2-(h : Int))
    (hword : seg f T 40 =
      (List.replicate 5 [true,false,false,false,false,true,true,true]).flatten)
    (hactual : ∀ j, j<5 → EndN f 0 (T+8*j+5)) :
    5≤cN (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤1-(h : Int)) 0 T := by
  by_cases hfive : 5≤cN (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤1-(h : Int)) 0 T
  · exact hfive
  · have hfloor := low_four_original_floor f h T hh hS hend (by omega)
    have hv := original_floor_visit_count f T (-(h : Int)-4) hfloor (by omega)
    have hs := five_distinct_original_sources f T hword hactual
    have he : Fw f T-4=-(h : Int)-4+2 := by omega
    rw [he] at hs
    have hm := cN_mono
      (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤-(h : Int)-4+2)
      (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤1-(h : Int)) 0 T
      (by intro q _ _ hq; exact ⟨hq.1,hq.2.1,by have := hq.2.2; omega⟩)
    omega

/-- Raw original boundary-window version of the M=5 lower bound. No
old-area admission, low-to-total budget, truncated history or upper
excursion limit is assumed. -/
theorem original_boundary_five_period_cost (f : Nat → Bool) (h T : Nat)
    (hh : 1≤h) (hT : h≤T) (hS : ∀ i, i<h → f i=false)
    (hboundary : Win f (h-1) (T-(h-1)))
    (hword : seg f T 40 =
      (List.replicate 5 [true,false,false,false,false,true,true,true]).flatten)
    (hactual : ∀ j, j<5 → EndN f 0 (T+8*j+5)) :
    5≤cN (fun q => f q=true ∧ ¬EndN f 0 q ∧ Fw f q≤1-(h : Int)) 0 T := by
  have hs := fw_false_run f 0 (h-1) (by intro i _ hi; exact hS i (by omega))
  simp only [Nat.zero_add,Fw] at hs
  have hb := hboundary.2.1
  rw [Nat.add_sub_cancel' (by omega : h-1≤T)] at hb
  exact five_periods_need_five_low_free f h T hh hS (by omega) hword hactual

end Recaman.FivePeriodSourceCost
