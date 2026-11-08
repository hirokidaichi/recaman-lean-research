import Recaman.PrimitiveLayerClockCost

namespace Recaman.PrimitiveLayerActualFree

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The outermost layer's clock increment is paid by its own actual first-A
free count. The arbitrary old BlockWord and unchanged mixed future are retained;
this cannot be iterated by resetting an inner prefix to BlockWord. -/
theorem outer_layer_actual_free_charge (f : Nat → Bool) (n h a b B i j : Nat)
    (w u : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (hb : 1≤b)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ r, r<a → f (n+h+r)=true)
    (hfull : seg f 0 B=w++List.replicate h false++List.replicate a true++List.replicate b false++u)
    (hlast : ∀ r, r≤j → f (B+r)=true)
    (hkey : runKey u= -2)
    (hnewkey : runKey (List.replicate a true++(List.replicate b false++u))= -2)
    (hm : mass u+(i : Int)=1)
    (hnewmass : mass (List.replicate a true++(List.replicate b false++u))+(j : Int)=1) :
    i+2≤j ∧ j-i≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) (n+h) a ∧
      EndN f 0 (B+i) ∧ EndN f 0 (B+j) := by
  obtain ⟨hij,hcost⟩:=Recaman.PrimitiveLayerClockCost.layer_clock_A_cost u a b i j hb hkey hnewkey hm hnewmass
  have hfree:=single_A_run_free_budget f n h a w hw hpre hS hA
  have hFodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd u hkey
  have hFu : 1≤cntF u := by omega
  have hFcount:=cntF_int u
  have hones:=(ones_bounds u).1
  have hu : 0<u.length := by omega
  let pfx:=List.replicate a true++List.replicate b false
  let V:=pfx++u
  let P:=w++List.replicate h false
  have hVkey : runKey V= -2 := by simpa only [V,pfx,List.append_assoc] using hnewkey
  have hVmass : mass V+(j : Int)=1 := by simpa only [V,pfx,List.append_assoc] using hnewmass
  have hVlen : 0<V.length := by simp only [V,List.length_append]; omega
  have hd : V.drop pfx.length=u := by
    change (pfx++u).drop pfx.length=u
    simp only [List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append]
  have hlocali:= (localSupply_A_S_iff V i 0).mpr
    ⟨pfx.length,by simp only [V,List.length_append]; omega,
      by rw [hd]; exact hm,by rw [hd,hkey]; decide⟩
  have hlocalj:= (localSupply_A_S_iff V j 0).mpr
    ⟨0,hVlen,by simpa only [List.drop_zero,Int.natCast_zero,Int.zero_add] using hVmass,
      by simp only [List.drop_zero,hVkey]; decide⟩
  have hbase : seg f 0 B=P++V := by simpa only [P,V,pfx,List.append_assoc] using hfull
  have hend (r : Nat) (hr : r≤j)
      (hloc : Recaman.ThreeNonsuppliedData.localSupply (V++List.replicate r true)=true) : EndN f 0 (B+r) := by
    have hsegA : seg f B r=List.replicate r true := by
      apply seg_A
      intro t ht htr
      have he:=hlast (t-B) (by omega)
      rwa [Nat.add_sub_cancel' ht] at he
    have hword : seg f 0 (B+r)=P++V++List.replicate r true := by
      rw [seg_add,Nat.zero_add,hbase,hsegA]
    have hl : Recaman.ThreeNonsuppliedData.localSupply (seg f 0 (B+r))=true := by
      rw [hword]
      exact (ray_supply_append_iff P V r).mpr (Or.inr hloc)
    exact (localSupply_seg_iff f 0 (B+r) (by omega) (hlast r hr)).mp hl
  have hli : Recaman.ThreeNonsuppliedData.localSupply (V++List.replicate i true)=true := by
    simpa only [List.replicate_zero,List.append_nil] using hlocali
  have hlj : Recaman.ThreeNonsuppliedData.localSupply (V++List.replicate j true)=true := by
    simpa only [List.replicate_zero,List.append_nil] using hlocalj
  exact ⟨hij,by omega,hend i (by omega) hli,hend j (by omega) hlj⟩

end Recaman.PrimitiveLayerActualFree
