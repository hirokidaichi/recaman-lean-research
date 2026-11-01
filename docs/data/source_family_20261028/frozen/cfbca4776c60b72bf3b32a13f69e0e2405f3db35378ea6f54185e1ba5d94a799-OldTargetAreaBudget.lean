import Recaman.InitialSTargetBounds

namespace Recaman.OldTargetAreaBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount Recaman.ASourceReuse
open Recaman.InitialSTargetBounds
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc := cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

/-- The old source carries its mass and area together. The positive area
    of that same BlockWord makes the half-A bound strict. -/
theorem old_target_word_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s T j : Nat)
    (hmass : mass (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false))=1)
    (harea : areaW (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false))=0) :
    mass u=(h : Int)+(m : Int)+(s : Int)+(j : Int)+1-((M : Int)+(L : Int)+(T : Int)) ∧
    2*areaW u+mass u*(mass u-1)=
      2*((M : Int)+(L : Int)+(T : Int))*((M : Int)+(L : Int)+(T : Int)-2*((j : Int)+1))-
        4*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)) ∧
    (mass u)^2+2*((M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int))≤
      ((M : Int)+(L : Int)+(T : Int))*((M : Int)+(L : Int)+(T : Int)-2*((j : Int)+1))+1 ∧
    2*(j+1)+1≤M+L+T := by
  let A : Int := (M : Int)+(L : Int)+(T : Int)
  let H : Int := (h : Int)+(m : Int)+(s : Int)
  let R : Int := (j : Int)+1
  let I : Int := (M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
  let v := List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  have hC : mass u=H+R-A := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hmass
    dsimp [A,H,R]
    omega
  have hk := source_key_before_gap (u++v) T j
    (by simpa only [v,List.append_assoc] using hmass)
    (by simpa only [v,List.append_assoc] using harea)
  have hcS : (cntF v : Int)=H := by
    simp only [v,cntF_append,cntF_replicate_S,cntF_A,Int.natCast_add]
    dsimp [H]
    omega
  have hkv : runKey v=4*I-2*H^2 := by
    rw [runKey_five_runs]
    dsimp [I,H]
    grind
  rw [runKey_append,hkv,hcS] at hk
  have hid : 2*areaW u+mass u*(mass u-1)=2*A*(A-2*R)-4*I := by
    unfold runKey at hk
    dsimp [R] at *
    grind
  have hlow := block_area_quadratic_lower hu
  have hb : (mass u)^2+2*I≤A*(A-2*R)+1 := by grind
  obtain ⟨hCpos,hDpos⟩ := sufPos_block hu [] u rfl hne
  have hcp := Int.mul_nonneg (show 0≤mass u by omega) (show 0≤mass u-1 by omega)
  have hip : 0≤I := by
    have h1 := Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
    have h2 := Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
    dsimp [I]
    omega
  have ha : 2*R<A := by
    by_cases h : 2*R<A
    · exact h
    · have hp := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤A by dsimp [A]; omega)
        (show A-2*R≤0 by omega)
      grind
  exact ⟨hC,hid,hb,by dsimp [A,R] at ha; omega⟩

/-- The raw strict bound is sharp even with three nonempty A runs. This
    constructs P2 windows, not a free-gap or C1 counterexample. -/
theorem old_target_strict_bound_sharp (R : Nat) (hR : 3≤R) :
    let v := [true]++(List.replicate 3 false++List.replicate 1 true++
      List.replicate (R-2) false++List.replicate 1 true++List.replicate 1 false++
      List.replicate (2*R-1) true++List.replicate (R-1) false)
    mass v=1 ∧ areaW v=0 ∧ 1+1+(2*R-1)=2*R+1 := by
  let w := List.replicate 3 false++List.replicate 1 true++List.replicate (R-2) false++
    List.replicate 1 true++List.replicate 1 false
  have hcast1 : ((R-1 : Nat) : Int)=(R : Int)-1 := by omega
  have hcast2 : ((R-2 : Nat) : Int)=(R : Int)-2 := by omega
  have hcastT : ((2*R-1 : Nat) : Int)=2*(R : Int)-1 := by omega
  have hmass : mass ([true]++(w++List.replicate (2*R-1) true++List.replicate (R-1) false))=1 := by
    simp only [w,mass_append,mass_rep_false,mass_replicate_A,hcast1,hcast2,hcastT]
    have hu : mass ([true] : List Bool)=1 := by decide
    rw [hu]
    omega
  have hcS : cntF w=R+2 := by
    simp only [w,cntF_append,cntF_replicate_S,cntF_A]
    omega
  have hkw : runKey w= -2*((R : Int)+2)^2+4*(R : Int) := by
    rw [runKey_five_runs]
    simp only [hcast2]
    grind
  have hku : runKey ([true] : List Bool)=0 := by decide
  have hmu : mass ([true] : List Bool)=1 := by decide
  have hk : runKey ([true]++w)= -2*(R : Int)^2 := by
    rw [runKey_append,hku,hmu,hkw,hcS]
    simp only [Int.natCast_add,Int.natCast_ofNat]
    grind
  have hkfull : runKey (([true]++w)++List.replicate (2*R-1) true++List.replicate (R-1) false)=-2 := by
    rw [runKey_append_S,runKey_append_A,hk]
    simp only [mass_append,w,mass_rep_false,mass_replicate_A,hmu,hcast1,hcast2,hcastT]
    grind
  have har : areaW ([true]++(w++List.replicate (2*R-1) true++List.replicate (R-1) false))=0 := by
    have hkf : runKey ([true]++(w++List.replicate (2*R-1) true++List.replicate (R-1) false))=-2 := by
      simpa only [List.append_assoc] using hkfull
    unfold runKey at hkf
    rw [hmass] at hkf
    omega
  dsimp only
  exact ⟨hmass,har,by omega⟩

end Recaman.OldTargetAreaBudget
