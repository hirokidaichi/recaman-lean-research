import Recaman.MassTwoPrefixKey

namespace Recaman.MassTwoThreeKeys

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem mass_two_keys (u : List Bool) (hu : BlockWord u) (hm : mass u=2) :
    runKey u= -2 ∨ runKey u=0 := by
  rcases block_mass_two hu hm with rfl|rfl <;> decide

theorem mass_three_keys (u : List Bool) (hu : BlockWord u) (hm : mass u=3) :
    runKey u= -2 ∨ runKey u=0 ∨ runKey u=2 := by
  rcases block_mass_three hu hm with rfl|rfl|rfl <;> decide

/-- The two key-2 signatures require incompatible suffix words in one common prefix. -/
theorem joint_minus_two_excluded (w : List Bool) (hw : BlockWord w) (t r : Nat)
    (ht : t<w.length) (hr : r<w.length) (hC : mass (w.drop t)=2) (hD : mass (w.drop r)=3)
    (hkt : runKey (w.drop t)= -2) (hkr : runKey (w.drop r)= -2) : False := by
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hv:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hut : w.drop t=aasW := by
    rcases block_mass_two hu hC with hu0|hu1
    · rw [hu0] at hkt
      have hz : runKey [true,true]=0 := by decide
      rw [hz] at hkt
      contradiction
    · exact hu1
  have hvr : w.drop r=[false,true,true,true,true] := by
    rcases block_mass_three hv hD with hv0|hv1|hv2
    · rw [hv0] at hkr
      have hz : runKey [true,true,true]=0 := by decide
      rw [hz] at hkr
      contradiction
    · exact hv1
    · rw [hv2] at hkr
      have hz : runKey [true,false,true,true,true]=2 := by decide
      rw [hz] at hkr
      contradiction
  have htl : w.length-t=4 := by
    have hl:=List.length_drop (l:=w) (i:=t)
    rw [hut] at hl
    change 4=w.length-t at hl
    omega
  have hrl : w.length-r=5 := by
    have hl:=List.length_drop (l:=w) (i:=r)
    rw [hvr] at hl
    change 5=w.length-r at hl
    omega
  have htr : t=r+1 := by omega
  have hd : (w.drop r).drop 1=w.drop t := by rw [List.drop_drop,htr]
  rw [hut,hvr] at hd
  have hn : ([false,true,true,true,true] : List Bool).drop 1≠aasW := by decide
  exact hn hd

theorem old_pair_parameters (R S K ku ks : Int) (hR : 5≤R) (hS : S≤R+9)
    (hku : ku= -2 ∨ ku=0) (hks : ks= -2 ∨ ks=0 ∨ ks=2)
    (hjoint : ¬(ku= -2 ∧ ks= -2))
    (hdiff : ku-ks=4*S+10-2*R^2)
    (hkey : ku=2*S^2-4*K-8*S-8-2*R^2) : R=6 ∧ S=15 ∧ K=63 := by
  have hR6 : R≤6 := by
    by_cases h6 : R≤6
    · exact h6
    have hp:=Int.mul_nonneg (show 0≤R-7 by omega) (show 0≤R+5 by omega)
    have he : (R-7)*(R+5)=R^2-2*R-35 := by grind only
    rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
  rcases (show R=5 ∨ R=6 by omega) with rfl|rfl
  · have hS9 : S=9 ∨ S=10 := by
      rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
    rcases hS9 with rfl|rfl <;> rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
  · have hS15 : S=15 := by
      rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega
    rw [hS15] at hkey
    exact ⟨rfl,hS15,by rcases hku with hku|hku <;> omega⟩

end Recaman.MassTwoThreeKeys
