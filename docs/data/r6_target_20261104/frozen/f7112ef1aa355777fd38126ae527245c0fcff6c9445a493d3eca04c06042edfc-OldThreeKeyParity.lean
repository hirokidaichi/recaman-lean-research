import Recaman.MassTwoThreeKeys

namespace Recaman.OldThreeKeyParity

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply Recaman.BlockOldRay
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem square_even_delta (x : Int) : ∃ z : Int, x^2=x+2*z := by
  let q:=x/2
  rcases (show x%2=0 ∨ x%2=1 by omega) with h0|h1
  · have he : x=2*q := by dsimp [q]; omega
    refine ⟨2*q^2-q,?_⟩
    rw [he]
    grind only
  · have he : x=2*q+1 := by dsimp [q]; omega
    refine ⟨2*q^2+q,?_⟩
    rw [he]
    grind only

theorem odd_square_eight (R : Int) (hodd : R%2=1) : ∃ q : Int, R^2=8*q+1 := by
  let q:=R/4
  rcases (show R%4=1 ∨ R%4=3 by omega) with h1|h3
  · have he : R=4*q+1 := by dsimp [q]; omega
    refine ⟨2*q^2+q,?_⟩
    rw [he]
    grind only
  · have he : R=4*q+3 := by dsimp [q]; omega
    refine ⟨2*q^2+3*q+1,?_⟩
    rw [he]
    grind only

/-- Primitive key spectra and the same-head seed parity exclude every odd R. -/
theorem odd_R_keys_excluded (E R ku ks Z : Int)
    (hku : ku= -2 ∨ ku=0) (hks : ks= -2 ∨ ks=0 ∨ ks=2)
    (hjoint : ¬(ku= -2 ∧ ks= -2))
    (hseed : ks=2*E-2+4*Z) (hdiff : ku-ks=4*E+2-2*R^2) (hodd : R%2=1) : False := by
  obtain ⟨q,hq⟩:=odd_square_eight R hodd
  rw [hq] at hdiff
  rcases hku with hku|hku <;> rcases hks with hks|hks|hks <;> omega

/-- A mass3 primitive old seed after a zero-mass head has a fixed key parity. -/
theorem mass_three_seed_parity (u : List Bool) (h M m L s U v : Nat)
    (hD : mass u=3) (hzero : M+L+U=h+m+s)
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
  obtain ⟨a,ha⟩:=square_even_delta S
  obtain ⟨b,hb⟩:=square_even_delta (v : Int)
  refine ⟨a+b-K-3*(S+(v : Int)),?_⟩
  change runKey u=2*(S+(v : Int))-2+4*(a+b-K-3*(S+(v : Int)))
  grind only

/-- Two old primitive windows from the same BlockWord force an even target gap parameter. -/
theorem old_three_target_even (w : List Bool) (hw : BlockWord w) (t r h M m L s U v i T j : Nat)
    (ht : t<w.length) (hr : r<w.length) (hC : mass (w.drop t)=2) (hD : mass (w.drop r)=3)
    (hzero : M+L+U=h+m+s)
    (hm1 : mass (w.drop r++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate i true)=1)
    (ha1 : areaW (w.drop r++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate i true)=0)
    (hm2 : mass (w.drop t++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (w.drop t++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)++List.replicate v false++List.replicate T true++List.replicate j false)=0) :
    ((j : Int)+1)%2=0 := by
  let z:=List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  have hmz : mass z=0 := by
    dsimp [z]
    simp only [mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : (cntF z : Int)=(h : Int)+(m : Int)+(s : Int) := by
    have hc:=mass_cntF z
    rw [hmz] at hc
    dsimp [z] at hc
    simp only [List.length_append,List.length_replicate] at hc
    omega
  have hk1:=Recaman.ASourceReuse.source_key_before_gap (w.drop r++z++List.replicate v false) i 0
    (by simpa only [z,List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [z,List.replicate_zero,List.append_nil] using ha1)
  have hk2:=Recaman.ASourceReuse.source_key_before_gap (w.drop t++z++List.replicate v false) T j hm2 ha2
  have hseed : runKey (w.drop r++z++List.replicate v false)= -2 := by simpa using hk1
  obtain ⟨Z,hZ⟩:=mass_three_seed_parity (w.drop r) h M m L s U v hD hzero hseed
  rw [runKey_append_S,runKey_append,mass_append,hD,hmz,hSz] at hk1
  rw [runKey_append_S,runKey_append,mass_append,hC,hmz,hSz] at hk2
  have hdiff : runKey (w.drop t)-runKey (w.drop r)=
      4*((h : Int)+(m : Int)+(s : Int)+(v : Int))+2-2*((j : Int)+1)^2 := by grind only
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hv:=block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have hku:=Recaman.MassTwoThreeKeys.mass_two_keys (w.drop t) hu hC
  have hks:=Recaman.MassTwoThreeKeys.mass_three_keys (w.drop r) hv hD
  have hno : ¬(runKey (w.drop t)= -2 ∧ runKey (w.drop r)= -2) := by
    rintro ⟨h1,h2⟩
    exact Recaman.MassTwoThreeKeys.joint_minus_two_excluded w hw t r ht hr hC hD h1 h2
  rcases (show ((j : Int)+1)%2=0 ∨ ((j : Int)+1)%2=1 by omega) with heven|hodd
  · exact heven
  · exact False.elim (odd_R_keys_excluded ((h : Int)+(m : Int)+(s : Int)+(v : Int))
      ((j : Int)+1) (runKey (w.drop t)) (runKey (w.drop r)) Z hku hks hno hZ hdiff hodd)

end Recaman.OldThreeKeyParity
