import Recaman.LowCrossLocalClocks

namespace Recaman.TripleRunClockResidue

open Recaman.LowCrossLocalClocks Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction

def tripleRuns : List Nat → List Bool
  | [] => []
  | h::hs => (List.replicate h false++List.replicate 3 true)++tripleRuns hs

private theorem triple_profile (hs : List Nat) :
    ones (tripleRuns hs)=3*(hs.length : Int) ∧ cross (tripleRuns hs)%12=0 := by
  induction hs with
  | nil => decide
  | cons h hs ih =>
    let v:=List.replicate h false
    let a:=List.replicate 3 true
    have hv : ones v=0 := ones_replicate_S h
    have ha : ones a=3 := ones_replicate_A 3
    have hs0 : cntF a=0 := by decide
    have h0 : cross (v++a)=0 := by
      rw [cross_append,cross_zero_of_no_A v hv,cross_zero_of_no_S a hs0,hv]
      omega
    have ha3 : ones (v++a)=3 := by rw [ones_append,hv,ha]; decide
    change ones ((v++a)++tripleRuns hs)=3*((h::hs).length : Int) ∧
      cross ((v++a)++tripleRuns hs)%12=0
    rw [ones_append,ha3,ih.1,cross_append,h0,ha3]
    simp only [List.length_cons,Int.natCast_succ]
    have hmod:=ih.2
    omega

/-- A suffix starting with any residual A and having full A-runs of
length three thereafter cannot supply a clock congruent to one. -/
theorem triple_run_residue_one_excluded (hs : List Nat) (r h i : Nat)
    (hi : i%3=1)
    (hm : mass ((List.replicate r true++tripleRuns hs)++List.replicate h false)+(i : Int)=1)
    (hk : runKey ((List.replicate r true++tripleRuns hs)++List.replicate h false)= -2) : False := by
  let a:=List.replicate r true
  let v:=tripleRuns hs
  let z:=List.replicate h false
  let w:=(a++v)++z
  let F:=(cntF w : Int)
  have hones : ones w=(r : Int)+3*(hs.length : Int) := by
    unfold w
    rw [ones_append,ones_append,show ones a=(r : Int) from ones_replicate_A r,
      show ones v=3*(hs.length : Int) from (triple_profile hs).1,
      show ones z=0 from ones_replicate_S h]
    omega
  have hm' : mass w+(i : Int)=1 := hm
  have hmass:=mass_eq w
  have hcnt:=cntF_int w
  change F=(w.length : Int)-ones w at hcnt
  have hR : (F-(r : Int))%3=0 := by omega
  have ha0 : cntF a=0 := Recaman.UnitTargetSASProfile.cntF_A r
  have hac : ones a=(r : Int) := ones_replicate_A r
  have hF : F=(cntF (v++z) : Int) := by
    unfold F w
    rw [List.append_assoc,cntF_append,ha0,Nat.zero_add]
  have htail : cross (v++z)%12=0 := by
    rw [cross_append,cross_zero_of_no_A z (ones_replicate_S h),
      show ones v=3*(hs.length : Int) from (triple_profile hs).1]
    have h0 : cross v%12=0 := (triple_profile hs).2
    have hp : 4*(3*(hs.length : Int))*(cntF z : Int)=
        12*((hs.length : Int)*(cntF z : Int)) := by grind only
    rw [hp]
    omega
  have hCross : cross w=cross (v++z)+4*(r : Int)*F := by
    unfold w
    rw [List.append_assoc,cross_append,cross_zero_of_no_S a ha0,hac,← hF]
    omega
  have hKey : cross w= -2+2*F^2 := by
    change runKey w= -2 at hk
    unfold cross
    rw [hk]
  let q:=(F-(r : Int))/3
  let k:=cross (v++z)/12
  have hq : F-(r : Int)=3*q := by dsimp [q]; omega
  have he : cross (v++z)=12*k := by dsimp [k]; omega
  have hSq : F*F+1=6*(q*F-k) := by grind only
  have hmod : (F*F+1)%3=0 := by omega
  rw [Int.add_emod (F*F) 1 3,Int.mul_emod F F 3] at hmod
  have hc : F%3=0 ∨ F%3=1 ∨ F%3=2 := by omega
  rcases hc with hc|hc|hc <;> rw [hc] at hmod <;> omega

end Recaman.TripleRunClockResidue
