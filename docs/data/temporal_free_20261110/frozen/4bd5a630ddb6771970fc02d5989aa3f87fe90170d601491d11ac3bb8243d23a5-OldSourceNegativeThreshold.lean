import Recaman.NonnegativeFutureOldSource
import Recaman.MixedASQuarterBudget

namespace Recaman.OldSourceNegativeThreshold

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- A mixed future with an old source must have a sufficiently negative
key. An even subtraction count also excludes the mass-one old suffix. -/
theorem old_source_key_threshold (w x : List Bool) (i : Nat) (hw : BlockWord w)
    (hF : 1≤cntF x) (hs : tailOldRay w x i) :
    runKey x≤ -4*(cntF x : Int)-2 ∧
      (cntF x%2=0 → runKey x≤ -8*(cntF x : Int)) := by
  obtain ⟨t,ht,hm,hk⟩:=hs
  have hdrop:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne : w.drop t≠[] := by
    intro he
    have hl:=congrArg List.length he
    simp only [List.length_drop,List.length_nil] at hl
    omega
  have hC := ((sufPos_block hdrop) [] (w.drop t) (by simp) hne).1
  have hLo : -2≤runKey (w.drop t) := by
    have h:=block_area_quadratic_lower hdrop
    unfold runKey
    omega
  by_cases h1 : mass (w.drop t)=1
  · have hz:=block_mass_one hdrop h1
    have hsKey : runKey (w.drop t++x)= -2 := by rw [runKey_append,hk]
    rw [hz] at hsKey
    have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd ([true]++x) hsKey
    rw [cntF_append,show cntF [true]=0 by decide,Nat.zero_add] at hodd
    rw [h1,hz,show runKey [true]=0 by decide] at hk
    constructor
    · omega
    · intro he
      omega
  · have hP:=Int.mul_nonneg (show 0≤mass (w.drop t)-2 by omega)
        (show 0≤(cntF x : Int) by omega)
    have h8 : runKey x≤ -8*(cntF x : Int) := by grind only
    exact ⟨by omega,fun _=>h8⟩

/-- The lower threshold holds for the full original history. The local
certificate is evaluated only on the explicitly supplied current word. -/
theorem actual_free_above_old_threshold (f : Nat → Bool) (n K : Nat) (w x : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hseg : seg f n K=x)
    (ha : f (n+K)=true) (hk : -4*(cntF x : Int)≤runKey x)
    (hl : Recaman.ThreeNonsuppliedData.localSupply x=false) :
    ¬EndN f 0 (n+K) := by
  intro he
  have hwhole : seg f 0 (n+K)=w++x := by rw [seg_add,Nat.zero_add,hpre,hseg]
  have hL:=(localSupply_seg_iff f 0 (n+K) (Nat.zero_le _) ha).mpr he
  have hC : Recaman.ThreeNonsuppliedData.localSupply ((w++x)++List.replicate 0 true)=true := by
    simpa only [Nat.sub_zero,hwhole,List.replicate_zero,List.append_nil] using hL
  rcases (ray_supply_append_iff w x 0).mp hC with ho|hlocal
  · by_cases hF : 1≤cntF x
    · have hneg := (old_source_key_threshold w x 0 hw hF ho).1
      omega
    · have h0 : cntF x=0 := by omega
      exact Recaman.NonnegativeFutureOldSource.no_old_source w x hw (by rw [h0] at hk; omega) 0 ho
  · simp only [List.replicate_zero,List.append_nil,hl] at hlocal
    cases hlocal

/-- The odd threshold is attained with the one-A old block. -/
theorem odd_threshold_example :
    BlockWord [true] ∧ tailOldRay [true] [false,false,true,false] 2 ∧
    runKey [false,false,true,false]= -4*(cntF [false,false,true,false] : Int)-2 := by
  refine ⟨?_,⟨0,by decide,by decide,by decide⟩,by decide⟩
  exact BlockWord.free BlockWord.nil

/-- The even threshold is attained with the SAAA old block. -/
theorem even_threshold_example :
    BlockWord [false,true,true,true] ∧ tailOldRay [false,true,true,true] [false,false,false,false] 3 ∧
    runKey [false,false,false,false]= -8*(cntF [false,false,false,false] : Int) := by
  refine ⟨?_,⟨0,by decide,by decide,by decide⟩,by decide⟩
  exact BlockWord.aas BlockWord.nil

end Recaman.OldSourceNegativeThreshold
