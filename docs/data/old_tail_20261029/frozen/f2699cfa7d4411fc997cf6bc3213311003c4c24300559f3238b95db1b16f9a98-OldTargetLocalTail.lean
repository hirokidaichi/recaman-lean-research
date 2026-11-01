import Recaman.OldSourceKeyOrder

namespace Recaman.OldTargetLocalTail

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.SourceFamilyFreeCount
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A source after an initial S prefix cannot supply a final-band A
clock when a BlockWord old source supplies the endpoint after a positive
S gap. The later common word and all lengths remain unrestricted. -/
theorem initial_S_tail_exclusion (u v : List Bool) (hu : BlockWord u)
    (a i T j : Nat) (hj : 1≤j) (hband : T≤i+j)
    (hm1 : mass (v++List.replicate i true)=1)
    (ha1 : areaW (v++List.replicate i true)=0)
    (hm2 : mass (u++List.replicate a false++v++List.replicate T true++List.replicate j false)=1)
    (ha2 : areaW (u++List.replicate a false++v++List.replicate T true++List.replicate j false)=0) : False := by
  have hk1 := source_key_before_gap v i 0
    (by simpa only [List.replicate_zero,List.append_nil] using hm1)
    (by simpa only [List.replicate_zero,List.append_nil] using ha1)
  have hk2 := source_key_before_gap (u++List.replicate a false++v) T j hm2 ha2
  have hmass : 0≤mass u-(a : Int) := by
    simp only [mass_append,mass_replicate_A,mass_rep_false] at hm1 hm2
    omega
  have hlow := block_area_quadratic_lower hu
  have hku : -2≤runKey u := by unfold runKey; omega
  have hp := Int.mul_nonneg (show 0≤(a : Int) by omega)
    (show 0≤2*mass u-(a : Int) by omega)
  have hkp : -2≤runKey (u++List.replicate a false) := by
    rw [runKey_append_S]
    grind
  have hpm : 0≤mass (u++List.replicate a false) := by
    rw [mass_append,mass_rep_false]
    exact hmass
  have hcross := Int.mul_nonneg hpm (show 0≤(cntF v : Int) by omega)
  have hjprod := Int.mul_nonneg (show 0≤(j : Int)-1 by omega)
    (show 0≤(j : Int)+3 by omega)
  rw [runKey_append] at hk2
  grind

/-- The initial-S alternative of the source-complete third-ray
classifier is absent on the proved final band under the same old target. -/
theorem initial_S_clock_exclusion (u : List Bool) (hu : BlockWord u)
    (h M m L s i T j q : Nat) (hq : q≤h) (hj : 1≤j) (hband : T≤i+j)
    (hbal : (q : Int)=(i : Int)+(M : Int)+(L : Int)-(m : Int)-(s : Int)-1)
    (hquad : ((q : Int)+(m : Int)+(s : Int))^2=
      2*(M : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)+1)
    (hm : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) : False := by
  let v := List.replicate q false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  have hvm : mass (v++List.replicate i true)=1 := by
    simp only [v,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hvk : runKey v= -2 := by
    dsimp [v]
    rw [runKey_five_runs]
    grind
  have hva : areaW (v++List.replicate i true)=0 := by
    have hk : runKey (v++List.replicate i true)= -2 := by rw [runKey_append_A,hvk]
    unfold runKey at hk
    rw [hvm] at hk
    omega
  have hsplit : u++List.replicate (h-q) false++v++List.replicate T true++List.replicate j false=
      u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false := by
    simp only [v,List.append_assoc]
    rw [←List.append_assoc (List.replicate (h-q) false) (List.replicate q false),
      List.replicate_append_replicate,show h-q+q=h by omega]
  exact initial_S_tail_exclusion u v hu (h-q) i T j hj hband hvm hva
    (by simpa only [hsplit] using hm) (by simpa only [hsplit] using ha)

def tailClock (M m L s i : Nat) : Bool :=
  let e : Int := (m : Int)+(s : Int)+1-(L : Int)-(i : Int)
  let v : Int := (i : Int)+(L : Int)-(s : Int)-1
  decide (i=2 ∨
    (1≤e ∧ e≤(M : Int) ∧ 2*e*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
      ((m : Int)+(s : Int))^2-1) ∨
    (1≤v ∧ v≤(m : Int) ∧ (v+(s : Int))^2=2*(L : Int)*(s : Int)+1))

theorem old_target_tail_clock_sound (u : List Bool) (hu : BlockWord u)
    (h M m L s i T j : Nat) (hs : 1≤s) (hj : 1≤j) (hband : T≤i+j)
    (hm : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hlocal : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) :
    tailClock M m L s i=true := by
  have hc := thirdClock_sound h M m L s i hs hlocal
  simp only [thirdClock,decide_eq_true_eq] at hc
  simp only [tailClock,decide_eq_true_eq]
  rcases hc with hi|⟨hq,hqh,hquad⟩|he|hv
  · exact Or.inl hi
  · let q : Int := (i : Int)+(M : Int)+(L : Int)-(m : Int)-(s : Int)-1
    have hq0 : 0≤q := by dsimp [q]; omega
    have hqN : (q.toNat : Int)=q := Int.toNat_of_nonneg hq0
    exact False.elim (initial_S_clock_exclusion u hu h M m L s i T j q.toNat
      (by omega) hj hband (by omega) (by simpa only [hqN] using hquad) hm ha)
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr hv)

theorem tailClock_count_le_three (M m L s T : Nat) (hs : 1≤s) :
    cN (fun i => tailClock M m L s i=true) 0 T≤3 := by
  let P := fun i : Nat => i=2
  let Q := fun i : Nat =>
    let e : Int := (m : Int)+(s : Int)+1-(L : Int)-(i : Int)
    1≤e ∧ e≤(M : Int) ∧ 2*e*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
      ((m : Int)+(s : Int))^2-1
  let V := fun i : Nat =>
    let v : Int := (i : Int)+(L : Int)-(s : Int)-1
    1≤v ∧ v≤(m : Int) ∧ (v+(s : Int))^2=2*(L : Int)*(s : Int)+1
  have hp : cN P 0 T≤1 := cN_le_one_of_unique P T (by intros; omega)
  have hq : cN Q 0 T≤1 := by
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    dsimp [Q] at hi hk
    have hz : (2*((m : Int)+(s : Int)))*((i : Int)-(k : Int))=0 := by grind
    have hh := Int.mul_eq_zero.mp hz
    rcases hh with h|h <;> omega
  have hv : cN V 0 T≤1 := by
    apply cN_le_one_of_unique
    intro i _ k _ hi hk
    dsimp [V] at hi hk
    have hz : ((i : Int)-(k : Int))*((i : Int)+(k : Int)+2*(L : Int)-2)=0 := by grind
    have hp : 0<(i : Int)+(k : Int)+2*(L : Int)-2 := by omega
    rcases Int.mul_eq_zero.mp hz with h|h <;> omega
  have hqv := cN_or_le Q V T
  have hall := cN_or_le P (fun i => Q i ∨ V i) T
  have heq : cN (fun i => tailClock M m L s i=true) 0 T=
      cN (fun i => P i ∨ Q i ∨ V i) 0 T := by
    apply cN_congr
    intro i _ _
    simp only [tailClock,decide_eq_true_eq,P,Q,V]
  omega

/-- The same-prefix old-source exclusion and the new initial-S source
exclusion combine into the smaller clock predicate on the final band. -/
theorem full_old_target_tail_clock (w : List Bool) (hw : BlockWord w)
    (t h M m L s i T j : Nat) (hs : 1≤s) (hj : 2≤j) (hband : T≤i+j)
    (hm : mass (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0)
    (hlocal : Recaman.ThreeNonsuppliedData.localSupply
      (w++List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) :
    tailClock M m L s i=true := by
  let v := List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  have hml : mass (w.drop t++v++List.replicate T true++List.replicate j false)=1 := by
    simpa only [v,List.append_assoc] using hm
  have hal : areaW (w.drop t++v++List.replicate T true++List.replicate j false)=0 := by
    simpa only [v,List.append_assoc] using ha
  have hl : Recaman.ThreeNonsuppliedData.localSupply (v++List.replicate i true)=true :=
    (Recaman.OldSourceKeyOrder.old_target_tail_local_iff w v hw t T j i hj hband hml hal).mp
      (by simpa only [v,List.append_assoc] using hlocal)
  have hu := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  exact old_target_tail_clock_sound (w.drop t) hu h M m L s i T j hs (by omega) hband hm ha
    (by simpa only [v,List.append_assoc] using hl)

end Recaman.OldTargetLocalTail
