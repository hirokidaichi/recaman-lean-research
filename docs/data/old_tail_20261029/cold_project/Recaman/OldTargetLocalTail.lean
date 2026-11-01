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

private theorem cN_length_bound (P : Nat → Prop) (n : Nat) : ∀ K, cN P n K≤K
  | 0 => Nat.le_refl 0
  | K+1 => by have hh := cN_succ_le P n K; have ih := cN_length_bound P n K; omega

theorem full_old_target_ray_count (w : List Bool) (hw : BlockWord w)
    (t h M m L s T j : Nat) (hs : 1≤s) (hj : 2≤j)
    (hm : mass (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (w.drop t++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    rayCount (w++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T≤T-j+3 := by
  let P := fun i => Recaman.ThreeNonsuppliedData.localSupply
    ((w++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)++List.replicate i true)=true
  let Q := fun i => tailClock M m L s i=true
  have hb : T-j≤T := by omega
  have hp := cN_add P 0 (T-j) (T-(T-j))
  have hq := cN_add Q 0 (T-j) (T-(T-j))
  simp only [Nat.zero_add,show T-j+(T-(T-j))=T by omega] at hp hq
  have hmono : cN P (T-j) (T-(T-j))≤cN Q (T-j) (T-(T-j)) := by
    apply cN_mono
    intro i hi hiT hh
    exact full_old_target_tail_clock w hw t h M m L s i T j hs hj (by omega) hm ha hh
  have hfirst := cN_length_bound P 0 (T-j)
  have hlast := tailClock_count_le_three M m L s T hs
  change cN P 0 T≤T-j+3
  change cN Q 0 T≤3 at hlast
  omega

/-- All sources and the original base0 remain present. The lower bound
is min(T,j)-3, written without truncated subtraction on the left. -/
theorem actual_old_target_ray_free (f : Nat → Bool) (n t h M m L s T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hs : 1≤s) (hj : 2≤j)
    (hword : seg f n (h+M+m+L+s)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false)
    (hA : ∀ i, i<T → f (n+(h+M+m+L+s)+i)=true)
    (hS : ∀ x, n+(h+M+m+L+s)+T≤x → x<n+(h+M+m+L+s)+T+j → f x=false)
    (hwin : Win f t (n+(h+M+m+L+s)+T+j-t)) :
    min T j≤cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+(h+M+m+L+s)) T+3 := by
  let B := h+M+m+L+s
  let v := List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false
  have hwlen : w.length=n := by rw [←hpre,seg_length]
  have hfull : seg f 0 (n+B)=w++v := by
    rw [seg_add,show 0+n=n by omega,hpre]
    exact congrArg (fun x => w++x) hword
  have hsegA : seg f (n+B) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    have hh := hA (x-(n+B)) (by omega)
    change f (n+B+(x-(n+B)))=true at hh
    simpa only [Nat.add_sub_cancel' hx] using hh
  have htarget : seg f t (n+B+T+j-t)=w.drop t++v++List.replicate T true++List.replicate j false := by
    have hd := seg_drop f 0 (n+B) t (by omega)
    simp only [Nat.zero_add] at hd
    rw [hfull,List.drop_append,show t-w.length=0 by omega,List.drop_zero] at hd
    rw [show n+B+T+j-t=((n+B-t)+T)+j by omega,seg_add,
      show t+(n+B-t+T)=n+B+T by omega,seg_false f (n+B+T) j hS,
      seg_add,show t+(n+B-t)=n+B by omega,←hd,hsegA]
  have hm : mass (w.drop t++v++List.replicate T true++List.replicate j false)=1 := by
    rw [←htarget,seg_mass]
    have hh := hwin.2.1
    rw [show t+(n+B+T+j-t)=n+B+T+j by omega] at hh ⊢
    omega
  have ha : areaW (w.drop t++v++List.replicate T true++List.replicate j false)=0 := by
    rw [←htarget,←Ar_areaW]
    exact hwin.2.2
  have hr := endable_A_run_count f (n+B) T (w++v) hfull hA
  have hb := full_old_target_ray_count w hw t h M m L s T j hs hj
    (by simpa only [v,List.append_assoc] using hm) (by simpa only [v,List.append_assoc] using ha)
  have hc := count_A_run f (n+B) T hA
  have hp := addition_endable_partition f (n+B) T
  have hb' : rayCount (w++v) T≤T-j+3 := by simpa only [v,List.append_assoc] using hb
  change min T j≤cN (fun x => f x=true ∧ ¬EndN f 0 x) (n+B) T+3
  omega

/-- The positive-gap hypothesis matters when the general removed
BlockWord is empty. This is an auxiliary boundary, not a C1 example. -/
theorem zero_gap_initial_source_control :
    mass ([]++List.replicate 0 false++(tripW++List.replicate 8 false)++List.replicate 5 true++
      List.replicate 0 false)=1 ∧
    areaW ([]++List.replicate 0 false++(tripW++List.replicate 8 false)++List.replicate 5 true++
      List.replicate 0 false)=0 ∧
    mass ((tripW++List.replicate 8 false)++List.replicate 5 true)=1 ∧
    areaW ((tripW++List.replicate 8 false)++List.replicate 5 true)=0 := by decide

end Recaman.OldTargetLocalTail
