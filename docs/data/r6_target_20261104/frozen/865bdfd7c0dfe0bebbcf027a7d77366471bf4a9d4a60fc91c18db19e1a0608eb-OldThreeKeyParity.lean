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

end Recaman.OldThreeKeyParity
