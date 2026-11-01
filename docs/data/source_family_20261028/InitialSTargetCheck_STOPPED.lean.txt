import Recaman.InitialSTargetBounds

namespace Recaman.InitialSTargetCheck

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.InitialSTargetBounds Recaman.SourceFamilyFreeCount
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

def rayBoolCount (w : List Bool) (K : Nat) : Nat :=
  ((List.range K).filter (fun i => Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true))).length

theorem cN_bool_filter (g : Nat → Bool) : ∀ K : Nat,
    cN (fun i => g i=true) 0 K=((List.range K).filter g).length
  | 0 => rfl
  | K+1 => by
    have ih := cN_bool_filter g K
    cases hg : g K
    · rw [cN_succ_neg (fun i => g i=true) 0 K (by simpa using hg)]
      simp [List.range_succ,List.filter_append,hg,ih]
    · rw [cN_succ_pos (fun i => g i=true) 0 K (by simpa using hg)]
      simp [List.range_succ,List.filter_append,hg,ih]

theorem rayCount_eq_boolCount (w : List Bool) (K : Nat) : rayCount w K=rayBoolCount w K := by
  exact cN_bool_filter (fun i => Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)) K

def secondBoolCount (H M m L : Nat) : Nat :=
  rayBoolCount (List.replicate H false++List.replicate M true++List.replicate m false) L

def thirdBoolCount (H M m L s T : Nat) : Nat :=
  rayBoolCount (List.replicate H false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false) T

def secondClock (h M m i : Nat) : Bool :=
  let q : Int := (i : Int)+(M : Int)-(m : Int)-1
  decide (i=2 ∨ (1≤q ∧ q≤(h : Int) ∧ (q+(m : Int))^2=2*(m : Int)*(M : Int)+1))

def thirdClock (h M m L s i : Nat) : Bool :=
  let q : Int := (i : Int)+(M : Int)+(L : Int)-(m : Int)-(s : Int)-1
  let e : Int := (m : Int)+(s : Int)+1-(L : Int)-(i : Int)
  let v : Int := (i : Int)+(L : Int)-(s : Int)-1
  decide (i=2 ∨
    (1≤q ∧ q≤(h : Int) ∧ (q+(m : Int)+(s : Int))^2=
      2*(M : Int)*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)+1) ∨
    (1≤e ∧ e≤(M : Int) ∧ 2*e*((m : Int)+(s : Int))+2*(L : Int)*(s : Int)=
      ((m : Int)+(s : Int))^2-1) ∨
    (1≤v ∧ v≤(m : Int) ∧ (v+(s : Int))^2=2*(L : Int)*(s : Int)+1))

private theorem A_S_no_key (e s : Nat) (he : 1≤e) (hs : 1≤s) :
    ¬runKey (List.replicate e true++List.replicate s false)=-2 := by
  intro hk
  rw [runKey_A_S] at hk
  have heq : (s : Int)*((s : Int)-2*(e : Int))=1 := by grind
  by_cases hn : (s : Int)-2*(e : Int)≤0
  · have hp := Int.mul_nonpos_of_nonneg_of_nonpos (show 0≤(s : Int) by omega) hn
    omega
  · have hp := Int.mul_nonneg (show 0≤(s : Int) by omega)
      (show 0≤(s : Int)-2*(e : Int)-1 by omega)
    have hs1 : s=1 := by grind
    subst s
    simp at heq
    omega

theorem secondClock_sound (h M m i : Nat) (hm : 1≤m)
    (hs : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate i true)=true) :
    secondClock h M m i=true := by
  have he := (localSupply_two_run_iff h M m i 0).mp (by simpa using hs)
  simp only [Int.natCast_zero,Int.zero_add] at he
  simp only [secondClock,decide_eq_true_eq]
  rcases he with ⟨q,hq,hqh,hbal,hkey⟩|⟨a,ha,haM,hbal,hkey⟩|⟨hi,hmi⟩
  · right
    have hiq : (i : Int)+(M : Int)-(m : Int)-1=(q : Int) := by omega
    rw [hiq]
    exact ⟨by omega,by omega,by grind⟩
  · have hk : runKey (List.replicate a true++List.replicate m false)=-2 := by
      rw [runKey_A_S]
      grind
    exact False.elim (A_S_no_key a m ha hm hk)
  · left
    omega

private theorem suffix_const (N : Nat) (b : Bool) (v : List Bool) (P : List Bool → Prop) :
    (∃ t, t<(List.replicate N b++v).length ∧ P ((List.replicate N b++v).drop t)) ↔
      (∃ k, 1≤k ∧ k≤N ∧ P (List.replicate k b++v)) ∨
      (∃ t, t<v.length ∧ P (v.drop t)) := by
  rw [exists_drop_append]
  apply or_congr
  · simp only [List.length_replicate,List.drop_replicate]
    constructor
    · rintro ⟨t,ht,hp⟩
      exact ⟨N-t,by omega,by omega,hp⟩
    · rintro ⟨k,hk,hkN,hp⟩
      exact ⟨N-k,by omega,by simpa only [show N-(N-k)=k by omega] using hp⟩
  · rfl

theorem thirdClock_sound (h M m L s i : Nat) (hs : 1≤s)
    (hlocal : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate i true)=true) :
    thirdClock h M m L s i=true := by
  obtain ⟨t,ht,hm,hk⟩ := (localSupply_A_S_iff
    (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) i 0).mp (by simpa using hlocal)
  let P := fun v : List Bool => mass v+(i : Int)=1 ∧ runKey v=-2
  have hh : ∃ t, t<(List.replicate h false++(List.replicate M true++
      (List.replicate m false++(List.replicate L true++List.replicate s false)))).length ∧
      P ((List.replicate h false++(List.replicate M true++
      (List.replicate m false++(List.replicate L true++List.replicate s false)))).drop t) := by
    exact ⟨t,by simpa only [List.append_assoc] using ht,
      by simpa [List.append_assoc,P] using hm,by simpa [List.append_assoc,P] using hk⟩
  rw [suffix_const,suffix_const,suffix_const,suffix_const] at hh
  simp only [thirdClock,decide_eq_true_eq]
  rcases hh with ⟨q,hq,hqh,hm,hk⟩|⟨e,he,heM,hm,hk⟩|⟨q,hq,hqm,hm,hk⟩|
    ⟨e,he,heL,hm,hk⟩|⟨t,ht,hm,hk⟩
  · right;left
    have hm' : mass (List.replicate q false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false)+(i : Int)=1 := by
      simpa only [List.append_assoc] using hm
    have hk' : runKey (List.replicate q false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false)=-2 := by
      simpa only [List.append_assoc] using hk
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm'
    rw [runKey_five_runs] at hk'
    have hiq : (i : Int)+(M : Int)+(L : Int)-(m : Int)-(s : Int)-1=(q : Int) := by omega
    rw [hiq]
    exact ⟨by omega,by omega,by grind⟩
  · right;right;left
    have hm' : mass (List.replicate e true++List.replicate m false++
        List.replicate L true++List.replicate s false)+(i : Int)=1 := by
      simpa only [List.append_assoc] using hm
    have hk' : runKey (List.replicate e true++List.replicate m false++
        List.replicate L true++List.replicate s false)=-2 := by
      simpa only [List.append_assoc] using hk
    have heq := runKey_five_runs 0 e m L s
    simp only [List.replicate_zero,List.nil_append] at heq
    rw [heq] at hk'
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm'
    have hie : (m : Int)+(s : Int)+1-(L : Int)-(i : Int)=(e : Int) := by omega
    rw [hie]
    exact ⟨by omega,by omega,by grind⟩
  · right;right;right
    have hm' : mass (List.replicate q false++List.replicate L true++List.replicate s false)+(i : Int)=1 := by
      simpa only [List.append_assoc] using hm
    have hk' : runKey (List.replicate q false++List.replicate L true++List.replicate s false)=-2 := by
      simpa only [List.append_assoc] using hk
    rw [runKey_S_A_S] at hk'
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm'
    have hiq : (i : Int)+(L : Int)-(s : Int)-1=(q : Int) := by omega
    rw [hiq]
    exact ⟨by omega,by omega,by grind⟩
  · exact False.elim (A_S_no_key e s he hs hk)
  · have hk' : runKey ((List.replicate s false).drop t)=-2 := hk
    have hm' : mass ((List.replicate s false).drop t)+(i : Int)=1 := hm
    rw [List.drop_replicate,runKey_S] at hk'
    rw [List.drop_replicate,mass_rep_false] at hm'
    simp only [List.length_replicate] at ht
    have hroot : s-t=1 := by
      have hp := Int.mul_pos (show 0<((s-t : Nat) : Int)+1 by omega)
        (show 0<((s-t : Nat) : Int) by omega)
      have hz : (((s-t : Nat) : Int)-1)*(((s-t : Nat) : Int)+1)=0 := by grind
      rcases Int.mul_eq_zero.mp hz with hz|hz <;> omega
    left
    rw [hroot] at hm'
    omega

def secondFastCount (H M m L : Nat) : Nat :=
  ((List.range L).filter (secondClock H M m)).length

def thirdFastCount (H M m L s T : Nat) : Nat :=
  ((List.range T).filter (thirdClock H M m L s)).length

theorem second_ray_fast_bound (H M m L : Nat) (hm : 1≤m) :
    rayCount (List.replicate H false++List.replicate M true++List.replicate m false) L≤secondFastCount H M m L := by
  rw [show secondFastCount H M m L=cN (fun i => secondClock H M m i=true) 0 L from
    (cN_bool_filter (secondClock H M m) L).symm]
  apply cN_mono
  intro i _ _ hi
  exact secondClock_sound H M m i hm hi

theorem third_ray_fast_bound (H M m L s T : Nat) (hs : 1≤s) :
    rayCount (List.replicate H false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) T≤thirdFastCount H M m L s T := by
  rw [show thirdFastCount H M m L s T=cN (fun i => thirdClock H M m L s i=true) 0 T from
    (cN_bool_filter (thirdClock H M m L s) T).symm]
  apply cN_mono
  intro i _ _ hi
  exact thirdClock_sound H M m L s i hs hi

def firstFreeFloor (M : Nat) : Nat := M-min 2 (M-2)

def countFloor (H M m L s T : Nat) : Nat :=
  firstFreeFloor M+(L-(1+secondFastCount H M m L))+(T-(1+thirdFastCount H M m L s T))

def coreValid (R K M m s : Nat) : Bool :=
  let A := K+R
  let P := (K*K-R*R)/2
  let E := P-M*(m+s)
  let L := E/s
  decide (1≤M ∧ 1≤m ∧ 1≤s ∧ m+s<K ∧ M*(m+s)<P ∧ E%s=0 ∧ 1≤L ∧ M+L<A)

def checkCore (R K M m s : Nat) : Bool :=
  if coreValid R K M m s then
    let A := K+R
    let P := (K*K-R*R)/2
    let L := (P-M*(m+s))/s
    let T := A-M-L
    decide (R≤countFloor (A-2) M m L s T)
  else true

def criticalPairs : List (Nat × Nat) := [(5,7),(5,9),(6,8),(7,9)]

def checkPair (R K : Nat) : Bool :=
  (List.range (K+R)).all (fun M => (List.range K).all (fun m =>
    (List.range K).all (fun s => checkCore R K M m s)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem critical_checked : criticalPairs.all (fun p => checkPair p.1 p.2)=true := by decide

end Recaman.InitialSTargetCheck
