import Recaman.UnitTargetZeroCross

namespace Recaman.UnitTargetSASProfile

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

theorem cntF_A (a : Nat) : cntF (List.replicate a true)=0 := by
  have h:=mass_cntF (List.replicate a true)
  rw [mass_replicate_A,List.length_replicate] at h
  omega

theorem S_key (h : Nat) : runKey (List.replicate h false)= -2*(h : Int)^2 := by
  have hk:=runKey_prepend_S h ([] : List Bool)
  have hz : runKey ([] : List Bool)=0 := by decide
  have hc : cntF ([] : List Bool)=0 := rfl
  simp only [List.append_nil,hz,hc,Int.natCast_zero,Int.mul_zero,Int.zero_sub,Int.neg_zero] at hk
  grind only

theorem SAS_cross (h M d : Nat) :
    runKey (List.replicate h false++List.replicate M true++List.replicate d false)+
      2*(cntF (List.replicate h false++List.replicate M true++List.replicate d false) : Int)^2=
      4*(M : Int)*(d : Int) := by
  have he:=Recaman.SourceCrossSurplus.cross_append
    (List.replicate h false++List.replicate M true) (List.replicate d false)
  simp only [runKey_append_A,S_key,cntF_append,cntF_replicate_S,cntF_A,
    ones_append,ones_replicate_S,ones_replicate_A,Nat.add_zero,Int.zero_add] at he ⊢
  omega

/-- Same mass-one target and an S-A-S source prefix. Its own remaining
S count occurs in the identity; no S count from a different source is used. -/
theorem unit_SAS_profile (x : List Bool) (h M d i T j : Nat)
    (hm1 : mass (x++List.replicate i true)=1)
    (ha1 : areaW (x++List.replicate i true)=0)
    (hm2 : mass ([true]++(List.replicate h false++List.replicate M true++List.replicate d false)++x++
      List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW ([true]++(List.replicate h false++List.replicate M true++List.replicate d false)++x++
      List.replicate T true++List.replicate j false)=0) :
    ((h : Int)+(d : Int)-1)^2=((j : Int)+1)^2+2*(M : Int)*(d : Int)+
      2*((i : Int)+(j : Int)-(T : Int))*(cntF x : Int) := by
  have he:=Recaman.SourceCrossSurplus.two_source_cross_identity [true]
    (List.replicate h false++List.replicate M true++List.replicate d false) x i T j hm1 ha1 hm2 ha2
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  rw [hmu,hku,SAS_cross,ones_append,ones_append,ones_replicate_S,ones_replicate_S,ones_replicate_A] at he
  have hb : (M : Int)-((i : Int)+(j : Int)-(T : Int))=(h : Int)+(d : Int)-1 := by
    simp only [mass_append,mass_replicate_A,mass_rep_false,hmu] at hm1 hm2
    omega
  simp only [Int.zero_add,Int.add_zero] at he
  rw [hb] at he
  grind only

end Recaman.UnitTargetSASProfile
