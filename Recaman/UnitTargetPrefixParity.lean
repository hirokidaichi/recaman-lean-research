import Recaman.SourceCrossSurplus

namespace Recaman.UnitTargetPrefixParity

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunSupplyBudget Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality
open Recaman.LineCapacityPeriodic

/-- Every literal word has an integral AS-pair cross surplus. -/
theorem cross_four (b : List Bool) : ∃ Q : Int, runKey b+2*(cntF b : Int)^2=4*Q := by
  induction b with
  | nil => exact ⟨0,by decide⟩
  | cons a b ih =>
    obtain ⟨Q,hQ⟩:=ih
    have he:=Recaman.SourceCrossSurplus.cross_append [a] b
    cases a with
    | false =>
      refine ⟨Q,?_⟩
      have h0 : runKey [false]+2*(cntF [false] : Int)^2=0 := by decide
      have ha : ones [false]=0 := by decide
      rw [h0,ha] at he
      change runKey ([false]++b)+2*(cntF ([false]++b) : Int)^2=_
      grind only
    | true =>
      refine ⟨Q+(cntF b : Int),?_⟩
      have h0 : runKey [true]+2*(cntF [true] : Int)^2=0 := by decide
      have ha : ones [true]=1 := by decide
      rw [h0,ha] at he
      change runKey ([true]++b)+2*(cntF ([true]++b) : Int)^2=_
      grind only

private theorem square_parity (x : Int) : ∃ q : Int, x^2=x+2*q := by
  let a:=x/2
  rcases (show x%2=0 ∨ x%2=1 by omega) with h0|h1
  · have hx : x=2*a := by dsimp [a]; omega
    refine ⟨2*a^2-a,?_⟩
    rw [hx]
    grind only
  · have hx : x=2*a+1 := by dsimp [a]; omega
    refine ⟨2*a^2+a,?_⟩
    rw [hx]
    grind only

/-- A mass-one old target preserves square parity in every mixed
prefix. Positive AS surplus strengthens the strict cut by two. -/
theorem unit_target_prefix_cut (b v : List Bool) (i T j : Nat)
    (hj : 2≤j) (hband : T≤i+j)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass ([true]++b++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW ([true]++b++v++List.replicate T true++List.replicate j false)=0) :
    (j : Int)+1+((i : Int)+(j : Int)-(T : Int))≤ones b ∧
    (4≤runKey b+2*(cntF b : Int)^2 →
      (j : Int)+1+((i : Int)+(j : Int)-(T : Int))+2≤ones b) := by
  let R:=(j : Int)+1
  let d:=(i : Int)+(j : Int)-(T : Int)
  let X:=ones b-d
  have he:=Recaman.SourceCrossSurplus.two_source_cross_identity [true] b v i T j hm1 ha1 hm2 ha2
  have hmu : mass [true]=1 := by decide
  have hku : runKey [true]=0 := by decide
  rw [hmu,hku] at he
  have hid : 2*X^2=2*R^2+(runKey b+2*(cntF b : Int)^2)+4*d*(cntF v : Int) := by
    dsimp [R,X,d]
    grind only
  have hd : 0≤d := by dsimp [d]; omega
  have hcross:=runKey_count_lower b
  have hp:=Int.mul_nonneg hd (show 0≤(cntF v : Int) by omega)
  have hXlo : -1≤X := by
    have hmb:=mass_eq b
    have hc:=cntF_int b
    simp only [mass_append,mass_replicate_A,mass_rep_false,hmu] at hm1 hm2
    dsimp [X,d]
    omega
  have hR : 3≤R := by dsimp [R]; omega
  have hXR : R≤X := by
    by_cases hx : R≤X
    · exact hx
    · have hp2:=Int.mul_nonneg (show 0≤R-1-X by omega) (show 0≤R-1+X by omega)
      grind only
  refine ⟨?_,?_⟩
  · dsimp [R,X,d] at hXR
    omega
  · intro hstrict
    have hgt : R<X := by
      by_cases hx : R<X
      · exact hx
      · have hx : X=R := by omega
        rw [hx] at hid
        grind only
    obtain ⟨Q,hQ⟩:=cross_four b
    obtain ⟨a,ha⟩:=square_parity X
    obtain ⟨c,hc⟩:=square_parity R
    have hdelta : X-R=2*(c+Q+d*(cntF v : Int)-a) := by grind only
    have htwo : R+2≤X := by omega
    dsimp [R,X,d] at htwo
    omega

end Recaman.UnitTargetPrefixParity
