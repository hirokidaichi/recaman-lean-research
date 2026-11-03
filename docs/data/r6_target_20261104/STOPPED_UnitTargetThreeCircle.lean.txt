import Recaman.LowTargetSeedParity

namespace Recaman.UnitTargetThreeCircle

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem old_three_target_circle (w : List Bool) (hw : BlockWord w) (t r h M m L s U v i T j : Nat)
    (ht : t<w.length) (hr : r<w.length) (hC : mass (w.drop t)=1) (hD : mass (w.drop r)=3)
    (hzero : M+L+U=h+m+s)
    (hm1 : mass (w.drop r++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate i true)=1)
    (ha1 : areaW (w.drop r++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate i true)=0)
    (hm2 : mass (w.drop t++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate T true++List.replicate j false)=0) :
    ((j : Int)+1)%2=0 ∧ ((j : Int)+1)^2=4*((h : Int)+(m : Int)+(s : Int)+(v : Int)) ∧ runKey (w.drop r)= -2 ∧ ((h : Int)+(m : Int)+(s : Int)+(v : Int))%2=0 := by
  let z:=List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  have hmz : mass z=0 := by
    dsimp [z]
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : (cntF z : Int)=(h : Int)+(m : Int)+(s : Int) := by
    have hc:=mass_cntF z
    rw [hmz] at hc
    dsimp [z] at hc ⊢
    simp only [List.length_append,List.length_replicate] at hc
    omega
  have hk1:=Recaman.ASourceReuse.source_key_before_gap (w.drop r++z++List.replicate v false) i 0
    (by simpa only [z,List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [z,List.replicate_zero,List.append_nil] using ha1)
  have hk2:=Recaman.ASourceReuse.source_key_before_gap (w.drop t++z++List.replicate v false) T j hm2 ha2
  have hseed : runKey (w.drop r++z++List.replicate v false)= -2 := by simpa using hk1
  obtain ⟨Z,hZ⟩:=Recaman.LowTargetSeedParity.seed_key_parity (w.drop r) h M m L s U v 3 hD hzero hseed
  rw [runKey_append_S,runKey_append,mass_append,hD,hmz,hSz] at hk1
  rw [runKey_append_S,runKey_append,mass_append,hC,hmz,hSz] at hk2
  have hdiff : runKey (w.drop t)-runKey (w.drop r)=
      8*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2-2*((j : Int)+1)^2 := by grind only
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hv:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hku : runKey (w.drop t)=0 := by
    rw [block_mass_one hu hC]
    decide
  have hks:=Recaman.MassTwoThreeKeys.mass_three_keys (w.drop r) hv hD
  have hdiff0 : -runKey (w.drop r)=8*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2-2*((j : Int)+1)^2 := by omega
  have heven : ((j : Int)+1)%2=0 := by
    apply Classical.byContradiction
    intro hn
    have ho : ((j : Int)+1)%2=1 := by omega
    obtain ⟨q,hq⟩:=Recaman.OldThreeKeyParity.odd_square_eight ((j : Int)+1) ho
    rw [hq] at hdiff0
    rcases hks with hs0|hs0|hs0 <;> omega
  let q:=((j : Int)+1)/2
  have hRq : (j : Int)+1=2*q := by dsimp [q]; omega
  have hsquare : ((j : Int)+1)^2=4*q^2 := by rw [hRq]; grind only
  have hminus : runKey (w.drop r)= -2 := by
    rcases hks with hm|hz|hp
    · exact hm
    · omega
    · omega
  have hcircle : ((j : Int)+1)^2=4*((h : Int)+(m : Int)+(s : Int)+(v : Int)) := by omega
  have hEeven : ((h : Int)+(m : Int)+(s : Int)+(v : Int))%2=0 := by omega
  exact ⟨heven,hcircle,hminus,hEeven⟩

end Recaman.UnitTargetThreeCircle
