import Recaman.BlockOldRay

namespace Recaman.NonnegativeFutureOldSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Every old source is retained; no bound on its positive mass is imposed. -/
theorem no_old_source (w x : List Bool) (hw : BlockWord w) (hk : 0≤runKey x) (i : Nat) :
    ¬tailOldRay w x i := by
  rintro ⟨t,ht,hm,hkey⟩
  have hdrop:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hne:=drop_nonempty w t ht
  have hmass : 1≤mass (w.drop t) := ((sufPos_block hdrop) [] (w.drop t) (by simp) hne).1
  have hlo : -2≤runKey (w.drop t) := by
    have he:=block_area_quadratic_lower hdrop
    unfold runKey
    omega
  by_cases hF : cntF x=0
  · have hc:=cntF_int x
    have hx:=mass_eq x
    have hones:=(ones_bounds x).1
    have hxnonneg : 0≤mass x := by omega
    have hC1 : mass (w.drop t)=1 := by omega
    have hword:=Recaman.BlockSuffixPositivity.block_mass_one hdrop hC1
    rw [hword,show runKey [true]=0 by decide,hF] at hkey
    simp only [Int.natCast_zero,Int.mul_zero] at hkey
    omega
  · have hp:=Int.mul_nonneg (show 0≤mass (w.drop t)-1 by omega)
        (show 0≤(cntF x : Int) by omega)
    grind only

/-- A source at the first A after S/A/A/S is impossible at the original
base, even with every earlier BlockWord supplier retained. -/
theorem SAAS_next_actual_free (f : Nat → Bool) (n : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n 4=[false,true,true,false]) (hA : f (n+4)=true) :
    ¬EndN f 0 (n+4) := by
  intro hend
  let x:=[false,true,true,false]
  have hwhole : seg f 0 (n+4)=w++x := by
    rw [seg_add,Nat.zero_add,hpre,hword]
  have hlocal : Recaman.ThreeNonsuppliedData.localSupply ((w++x)++List.replicate 0 true)=true := by
    have he:=(localSupply_seg_iff f 0 (n+4) (by omega) hA).mpr hend
    simpa only [Nat.sub_zero,hwhole,List.replicate_zero,List.append_nil] using he
  rcases (ray_supply_append_iff w x 0).mp hlocal with ho|hl
  · exact no_old_source w x hw (by decide) 0 ho
  · have hn : Recaman.ThreeNonsuppliedData.localSupply (x++List.replicate 0 true)=false := by decide
    rw [hn] at hl
    cases hl

end Recaman.NonnegativeFutureOldSource
