import Recaman.UnitTargetPrefixParity
import Recaman.OldThreeKeyParity

namespace Recaman.UnitTargetTwoS

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- A mass-one target cannot coexist with a local source preceded by
at most two S signs, regardless of the later mixed word or global area. -/
theorem two_S_source_excluded (x : List Bool) (d i T j : Nat) (hd : d≤2) (hj : 2≤j)
    (hm1 : mass (x++List.replicate i true)=1)
    (ha1 : areaW (x++List.replicate i true)=0)
    (hm2 : mass ([true]++List.replicate d false++x++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW ([true]++List.replicate d false++x++List.replicate T true++List.replicate j false)=0) : False := by
  have he:=Recaman.SourceCrossSurplus.two_source_cross_identity [true] (List.replicate d false) x i T j hm1 ha1 hm2 ha2
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  have hSkey : runKey (List.replicate d false)= -2*(d : Int)^2 := by
    have hz:=runKey_prepend_S d ([] : List Bool)
    have hn : runKey ([] : List Bool)=0 := by decide
    have hc : cntF ([] : List Bool)=0 := rfl
    simpa only [List.append_nil,hn,hc,Int.natCast_zero,Int.mul_zero,Int.zero_sub,Int.neg_zero] using hz
  rw [hmu,hku,hSkey,cntF_replicate_S,ones_replicate_S] at he
  have hmass : (i : Int)+(j : Int)-(T : Int)=1-(d : Int) := by
    simp only [mass_append,mass_replicate_A,mass_rep_false,hmu] at hm1 hm2
    omega
  rw [hmass] at he
  have hid : ((j : Int)+1)^2=((d : Int)-1)^2+2*((d : Int)-1)*(cntF x : Int) := by grind only
  have hk:=source_key_before_gap x i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hkx : runKey x= -2 := by simpa using hk
  obtain ⟨Q,hQ⟩:=Recaman.UnitTargetPrefixParity.cross_four x
  obtain ⟨a,ha⟩:=Recaman.OldThreeKeyParity.square_even_delta (cntF x : Int)
  have hNodd : (cntF x : Int)%2=1 := by rw [hkx,ha] at hQ; omega
  have hR9:=Int.mul_nonneg (show 0≤(j : Int)+1-3 by omega) (show 0≤(j : Int)+1+3 by omega)
  rcases (show d=0 ∨ d=1 ∨ d=2 by omega) with hd|hd|hd
  · rw [hd] at hid
    grind only
  · rw [hd] at hid
    grind only
  · rw [hd] at hid
    have he2 : ((j : Int)+1)^2=1+2*(cntF x : Int) := by grind only
    obtain ⟨b,hb⟩:=Recaman.OldThreeKeyParity.square_even_delta ((j : Int)+1)
    have hRodd : ((j : Int)+1)%2=1 := by omega
    obtain ⟨q,hq⟩:=Recaman.OldThreeKeyParity.odd_square_eight ((j : Int)+1) hRodd
    omega

end Recaman.UnitTargetTwoS
