import Recaman.FourSInitialTarget
import Recaman.MomentFirstASource
import Recaman.LowerMomentOldClock

namespace Recaman.InitialFirstParityCollision

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- Initial-S clock0 and first-A clock1 never coexist for a zero-mass
head, at any separator length. This is a source conflict, not a full-gap
claim; no old target mass, area band or finite length bound is input. -/
theorem initial_zero_first_one_excluded_all_v (h M m L s U v : Nat) (hzero : M+L+U=h+m+s)
    (hinit : sourceAt false h (List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false) 0) :
    ¬sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) 1 := by
  intro he
  let S:=h+m+s
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  let z:=List.replicate h false++x
  have hmz : mass z=0 := by
    simp only [z,x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF z=S := by
    have hm:=mass_cntF z
    have hl : z.length=h+M+m+L+s+U := by simp only [z,x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hm
    dsimp [S]
    omega
  have hkz:=Recaman.FourSInitialTarget.initial_zero_head_key x h v hmz
    (by simpa only [x,List.append_assoc] using hinit)
  change runKey z= -4*((v : Int)+1)*(cntF z : Int) at hkz
  rw [hSz] at hkz
  have haz : areaW z= -2*((v : Int)+1)*(S : Int) := by
    unfold runKey at hkz
    rw [hmz] at hkz
    grind only
  obtain ⟨e,he,heM,hbal,hkey⟩:=he
  have heq:=Recaman.MomentFirstASource.first_A_clock_equation h M m L s U S v e 1 (2*((v : Int)+1)*(S : Int)) rfl
    (by dsimp [S]; omega)
    (by simpa only [z,x,List.append_assoc,Int.neg_mul] using haz)
    (by simpa only [List.append_assoc] using hbal)
    (by simpa only [List.append_assoc] using hkey)
  have hsq : ((h : Int)-(v : Int))^2=2*(S : Int)-1 := by grind only
  have hpar:=Recaman.LowerMomentOldClock.zero_mass_area_parity z hmz (2*((v : Int)+1)*(S : Int))
    (by simpa only [Int.neg_mul] using haz)
  rw [hSz] at hpar
  have hEven : (2*((v : Int)+1)*(S : Int))%2=0 := by
    have heq : 2*((v : Int)+1)*(S : Int)=2*(((v : Int)+1)*(S : Int)) := by grind only
    rw [heq]
    omega
  let X:=(h : Int)-(v : Int)
  have hSrep : (S : Int)=2*((S : Int)/2) := by omega
  have hXrep : X=2*(X/2) ∨ X=2*(X/2)+1 := by omega
  change X^2=2*(S : Int)-1 at hsq
  rcases hXrep with hx|hx
  · have heq : 4*((X/2)^2)=4*((S : Int)/2)-1 := by rw [hSrep,hx] at hsq; grind only
    omega
  · have heq : 4*((X/2)^2+(X/2))=4*((S : Int)/2)-2 := by rw [hSrep,hx] at hsq; grind only
    omega

end Recaman.InitialFirstParityCollision
