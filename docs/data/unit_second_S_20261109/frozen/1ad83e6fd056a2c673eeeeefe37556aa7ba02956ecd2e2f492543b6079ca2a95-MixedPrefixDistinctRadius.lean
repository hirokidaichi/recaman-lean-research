import Recaman.MixedPrefixDistinctClock
import Recaman.PrimitiveLayerActualFree

namespace Recaman.MixedPrefixDistinctRadius

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The earlier source starts at the original BlockWord boundary.
For an arbitrary mixed prefix with at most three actual free additions,
the inner primitive clock is at most r(r+1), hence at most twelve.
No BlockWord reset at an inner source is used. -/
theorem actual_distinct_small_free_clock_radius (f : Nat → Bool) (n K B i j : Nat)
    (w p u : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hseg : seg f n K=p)
    (hpos : ∀ k, 0<k → k≤K → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hr : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n K≤3)
    (hfull : seg f 0 B=w++p++u) (hlast : ∀ r, r≤max i j → f (B+r)=true)
    (hij : i≠j) (hkey : runKey u= -2) (hnewkey : runKey (p++u)= -2)
    (hm : mass u+(i : Int)=1) (hn : mass (p++u)+(j : Int)=1) :
    let r:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n K
    (i : Int)≤(r : Int)*((r : Int)+1) ∧ i≤12 ∧ j≤17 ∧ EndN f 0 (B+i) ∧ EndN f 0 (B+j) := by
  dsimp only
  let r:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n K
  change r≤3 at hr
  have hraw:=Recaman.MixedPrefixDistinctClock.distinct_clock_square p u i j hij hkey hnewkey hm hn
  have hAraw:=positive_r3_additions_free_bound f n 0 K hw
    (by simpa only [List.replicate_zero,List.append_nil] using hpre) hpos hr
  change cN (fun x=>f x=true) n K≤2*r+1 at hAraw
  have hp:=ones_seg_eq_count f n K
  rw [hseg] at hp
  have hA : ones p≤2*(r : Int)+1 := by omega
  have hA0:=(ones_bounds p).1
  have hs:=Recaman.ShortCounterFactorBounds.square_lower (2*(r : Int)+1) (ones p) hA0 hA
  have hid : (2*(r : Int)+1)^2=4*((r : Int)*((r : Int)+1))+1 := by grind only
  have hir : (i : Int)≤(r : Int)*((r : Int)+1) := by omega
  have hs7:=Recaman.ShortCounterFactorBounds.square_lower 7 (ones p) hA0 (by omega)
  have hi12 : i≤12 := by omega
  have hj17 : j≤17 := by
    by_cases hh : i<j
    · have hc:=(Recaman.MixedPrefixClockSquare.mixed_prefix_clock_square p u i j hh hkey hnewkey hm hn).1
      omega
    · omega
  have hFodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
  have hFcount:=cntF_int u
  have hones:=(ones_bounds u).1
  have hu : 0<u.length := by omega
  let V:=p++u
  have hVkey : runKey V= -2 := hnewkey
  have hVmass : mass V+(j : Int)=1 := hn
  have hVlen : 0<V.length := by simp only [V,List.length_append]; omega
  have hd : V.drop p.length=u := by
    change (p++u).drop p.length=u
    simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]
  have hlocali:= (localSupply_A_S_iff V i 0).mpr
    ⟨p.length,by simp only [V,List.length_append]; omega,
      by rw [hd]; exact hm,by rw [hd,hkey]; decide⟩
  have hlocalj:= (localSupply_A_S_iff V j 0).mpr
    ⟨0,hVlen,by simpa only [List.drop_zero,Int.natCast_zero,Int.zero_add] using hVmass,
      by simp only [List.drop_zero,hVkey]; decide⟩
  have hbase : seg f 0 B=w++V := by simpa only [V,List.append_assoc] using hfull
  have hend (r : Nat) (hr : r≤max i j)
      (hloc : Recaman.ThreeNonsuppliedData.localSupply (V++List.replicate r true)=true) : EndN f 0 (B+r) := by
    have hsegA : seg f B r=List.replicate r true := by
      apply seg_A
      intro t ht htr
      have he:=hlast (t-B) (by omega)
      rwa [Nat.add_sub_cancel' ht] at he
    have hword : seg f 0 (B+r)=w++V++List.replicate r true := by
      rw [seg_add,Nat.zero_add,hbase,hsegA]
    have hl : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (B+r))=true := by
      rw [hword]
      exact (ray_supply_append_iff w V r).mpr (Or.inr hloc)
    exact (localSupply_seg_iff f 0 (B+r) (by omega) (hlast r hr)).mp hl
  have hli : Recaman.ThreeNonsuppliedData.localSupply (V++List.replicate i true)=true := by
    simpa only [List.replicate_zero,List.append_nil] using hlocali
  have hlj : Recaman.ThreeNonsuppliedData.localSupply (V++List.replicate j true)=true := by
    simpa only [List.replicate_zero,List.append_nil] using hlocalj
  exact ⟨hir,hi12,hj17,hend i (by omega) hli,hend j (by omega) hlj⟩

end Recaman.MixedPrefixDistinctRadius
