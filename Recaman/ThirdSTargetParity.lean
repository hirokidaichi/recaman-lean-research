import Recaman.SeparatedSActualBudget

namespace Recaman.ThirdSTargetParity

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

private theorem square_residue_four (x : Int) :
    ∃ q r : Int, (r=0 ∨ r=1) ∧ x^2=4*q+r ∧ x%2=r := by
  let t:=x/2
  rcases (show x%2=0 ∨ x%2=1 by omega) with h0|h1
  · have he : x=2*t := by dsimp [t]; omega
    exact ⟨t^2,0,Or.inl rfl,by rw [he]; grind only,h0⟩
  · have he : x=2*t+1 := by dsimp [t]; omega
    exact ⟨t^2+t,1,Or.inr rfl,by rw [he]; grind only,h1⟩

private theorem even_product_from_target (p R P : Int) (he : p^2=R^2+2*P) :
    ∃ Z : Int, P=2*Z := by
  obtain ⟨a,r,hr,hp,_⟩:=square_residue_four p
  obtain ⟨b,s,hs,hR,_⟩:=square_residue_four R
  refine ⟨a-b,?_⟩
  rcases hr with hr|hr <;> rcases hs with hs|hs <;> omega

/-- The same third-S target rules out every odd depth in the preceding
A source family. No third-S supplier is assumed. -/
theorem even_A_source_depth (q R L s U v i : Nat)
    (htarget : ((q : Int)+(v : Int))^2=(R : Int)^2+2*(U : Int)*(v : Int))
    (ha : sourceAt true L (List.replicate s false++
      (List.replicate U true++List.replicate v false)) i) :
    ∃ a, 1≤a ∧ a≤L ∧ (a : Int)%2=0 ∧
      mass (List.replicate a true++(List.replicate s false++
        (List.replicate U true++List.replicate v false)))+(i : Int)=1 ∧
      runKey (List.replicate a true++(List.replicate s false++
        (List.replicate U true++List.replicate v false)))= -2 := by
  obtain ⟨a,ha1,haL,hm,hk⟩:=ha
  have hkey:=hk
  rw [runKey_prepend_A,←List.append_assoc,runKey_S_A_S] at hkey
  simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A] at hkey
  obtain ⟨Z,hZ⟩:=even_product_from_target ((q : Int)+(v : Int)) (R : Int)
    ((U : Int)*(v : Int)) (by grind only)
  obtain ⟨b,r,hr,hx,_⟩:=square_residue_four ((s : Int)+(v : Int)-(a : Int))
  obtain ⟨c,t,ht,ha2,haodd⟩:=square_residue_four (a : Int)
  have he : ((s : Int)+(v : Int)-(a : Int))^2=(a : Int)^2+4*Z+1 := by grind only
  have heven : (a : Int)%2=0 := by
    rcases hr with hr|hr <;> rcases ht with ht|ht <;> omega
  exact ⟨a,ha1,haL,heven,hm,hk⟩

theorem unit_A_source_excluded (q R s U v i : Nat)
    (htarget : ((q : Int)+(v : Int))^2=(R : Int)^2+2*(U : Int)*(v : Int)) :
    ¬sourceAt true 1 (List.replicate s false++
      (List.replicate U true++List.replicate v false)) i := by
  intro ha
  obtain ⟨a,ha1,haL,heven,_,_⟩:=even_A_source_depth q R 1 s U v i htarget ha
  omega

/-- Without the selected target condition, a unit A source does exist. -/
theorem unit_A_without_target_witness :
    sourceAt true 1 (List.replicate 2 false++
      (List.replicate 1 true++List.replicate 1 false)) 2 := by
  exact ⟨1,by decide,by decide,by decide,by decide⟩

end Recaman.ThirdSTargetParity
