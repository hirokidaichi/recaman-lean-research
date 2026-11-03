import Recaman.OldThreeKeyParity

namespace Recaman.LowTargetSeedParity

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem seed_key_parity (u : List Bool) (h M m L s U v : Nat) (D : Int)
    (hD : mass u=D) (hzero : M+L+U=h+m+s)
    (hseed : runKey (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false)= -2) :
    ∃ Z : Int, runKey u=2*((h : Int)+(m : Int)+(s : Int)+(v : Int))-2+4*Z := by
  let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  let S : Int:=(h : Int)+(m : Int)+(s : Int)
  have hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : (cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true) : Int)=S := by
    have hc:=mass_cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)
    rw [hmz] at hc
    simp only [List.length_append,List.length_replicate] at hc
    dsimp [S]
    omega
  have hkz : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=4*K-2*S^2 := by
    rw [runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
    dsimp [K,S]
    grind only
  rw [runKey_append_S,runKey_append,mass_append,hD,hmz,hSz,hkz] at hseed
  obtain ⟨a,ha⟩:=Recaman.OldThreeKeyParity.square_even_delta S
  obtain ⟨b,hb⟩:=Recaman.OldThreeKeyParity.square_even_delta (v : Int)
  refine ⟨a+b-K-D*(S+(v : Int)),?_⟩
  change runKey u=2*(S+(v : Int))-2+4*(a+b-K-D*(S+(v : Int)))
  grind only

theorem old_two_target_circle (w : List Bool) (hw : BlockWord w) (t r h M m L s U v i T j : Nat)
    (ht : t<w.length) (hr : r<w.length) (hC : mass (w.drop t)=1) (hD : mass (w.drop r)=2)
    (hzero : M+L+U=h+m+s)
    (hm1 : mass (w.drop r++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate i true)=1)
    (ha1 : areaW (w.drop r++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate i true)=0)
    (hm2 : mass (w.drop t++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate T true++List.replicate j false)=0) :
    ((j : Int)+1)%2=0 ∧ ((j : Int)+1)^2=2*((h : Int)+(m : Int)+(s : Int)+(v : Int)) := by
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
  obtain ⟨Z,hZ⟩:=seed_key_parity (w.drop r) h M m L s U v 2 hD hzero hseed
  rw [runKey_append_S,runKey_append,mass_append,hD,hmz,hSz] at hk1
  rw [runKey_append_S,runKey_append,mass_append,hC,hmz,hSz] at hk2
  have hdiff : runKey (w.drop t)-runKey (w.drop r)=
      4*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2-2*((j : Int)+1)^2 := by grind only
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hv:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hku : runKey (w.drop t)=0 := by
    rw [block_mass_one hu hC]
    decide
  have hks:=Recaman.MassTwoThreeKeys.mass_two_keys (w.drop r) hv hD
  have hdiff0 : -runKey (w.drop r)=4*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2-2*((j : Int)+1)^2 := by omega
  have heven : ((j : Int)+1)%2=0 := by
    apply Classical.byContradiction
    intro hn
    have ho : ((j : Int)+1)%2=1 := by omega
    obtain ⟨q,hq⟩:=Recaman.OldThreeKeyParity.odd_square_eight ((j : Int)+1) ho
    rw [hq] at hdiff0
    rcases hks with hs0|hs0 <;> omega
  let q:=((j : Int)+1)/2
  have hRq : (j : Int)+1=2*q := by dsimp [q]; omega
  have hcircle : ((j : Int)+1)^2=2*((h : Int)+(m : Int)+(s : Int)+(v : Int)) := by
    rcases hks with hs0|hs0
    · omega
    · have hsquare : ((j : Int)+1)^2=4*q^2 := by rw [hRq]; grind only
      omega
  exact ⟨heven,hcircle⟩

end Recaman.LowTargetSeedParity
