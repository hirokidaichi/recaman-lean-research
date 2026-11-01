import Recaman.SourceFamilyFreeCount

namespace Recaman.SourceFamilyFirstBlock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget Recaman.SourceFamilyFreeCount
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

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

/-- The first A source cannot supply the third ray: its key would force
    an integer multiple of R+2 to equal3. There is no bound on e. -/
theorem first_A_third_ray_key (e R : Nat) (hR : 5≤R) :
    ¬runKey (List.replicate e true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  have hz := runKey_five_runs 0 e (R+1) R 1
  simp only [List.replicate_zero,List.nil_append] at hz
  rw [hz] at hk
  simp only [Int.natCast_add,Int.natCast_one] at hk
  have heq : (2*(e : Int)-(R : Int))*((R : Int)+2)=3 := by grind
  by_cases he : 2*(e : Int)-(R : Int)≤0
  · have hp := Int.mul_nonpos_of_nonpos_of_nonneg he (show 0≤(R : Int)+2 by omega)
    rw [heq] at hp
    omega
  · have hp := Int.mul_nonneg (show 0≤2*(e : Int)-(R : Int)-1 by omega)
      (show 0≤(R : Int)+2 by omega)
    grind

private theorem initial_S_third_ray_exception (q M R i : Nat) (hq : 1≤q) (hR : 5≤R)
    (hm : mass (List.replicate q false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)+(i : Int)=1)
    (hk : runKey (List.replicate q false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)=-2) :
    R=5 ∧ M=5 ∧ q=2 ∧ i=0 := by
  rw [runKey_five_runs] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A,Int.natCast_add,Int.natCast_one] at hm hk
  have hr5 : R=5 := by
    by_cases hr : R=5
    · exact hr
    · have hp := Int.mul_nonneg (show 0≤(q : Int)+3-(M : Int) by omega)
        (show 0≤2*((R : Int)+2) by omega)
      have hrp := Int.mul_nonneg (show 0≤(R : Int)-6 by omega)
        (show 0≤(R : Int)+2 by omega)
      have hqp := Int.mul_nonneg (show 0≤(q : Int) by omega) (show 0≤(q : Int) by omega)
      grind
  subst R
  have hsq : (q : Int)^2+14*(i : Int)=4 := by grind
  have hq2 : q≤2 := by
    by_cases h : q≤2
    · exact h
    · have hp := Int.mul_nonneg (show 0≤(q : Int)-3 by omega)
        (show 0≤(q : Int)+3 by omega)
      grind
  have hqq : q=1 ∨ q=2 := by omega
  rcases hqq with rfl|rfl
  · simp at hsq
    omega
  · simp at hsq
    exact ⟨rfl,by omega,rfl,by omega⟩

private theorem middle_S_third_ray_impossible (q R i : Nat) (hR : 5≤R)
    (hm : mass (List.replicate q false++List.replicate R true++List.replicate 1 false)+
      (i : Int)=1)
    (hk : runKey (List.replicate q false++List.replicate R true++List.replicate 1 false)=-2) : False := by
  rw [runKey_S_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have hp := Int.mul_nonneg (show 0≤(q : Int)+2-(R : Int) by omega)
    (show 0≤(q : Int)+(R : Int) by omega)
  have hr := Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
    (show 0≤(R : Int)+1 by omega)
  grind

/-- The exact additional source survives at R5/M5/clock0. M is otherwise
    completely unrestricted, and the same actual local suffix is used. -/
theorem third_ray_local_clocks (h M R i : Nat) (hR : 5≤R)
    (hs : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
        List.replicate R true++List.replicate 1 false++List.replicate i true)=true) :
    i=2 ∨ (R=5 ∧ M=5 ∧ i=0 ∧ 2≤h) := by
  obtain ⟨t,ht,hm,hk⟩ := (localSupply_A_S_iff
    (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) i 0).mp (by simpa using hs)
  let P := fun v : List Bool => mass v+(i : Int)=1 ∧ runKey v=-2
  have hh : ∃ t, t<(List.replicate h false++(List.replicate M true++
      (List.replicate (R+1) false++(List.replicate R true++List.replicate 1 false)))).length ∧
      P ((List.replicate h false++(List.replicate M true++
      (List.replicate (R+1) false++(List.replicate R true++List.replicate 1 false)))).drop t) := by
    exact ⟨t,by simpa only [List.append_assoc] using ht,
      by simpa [List.append_assoc,P] using hm,by simpa [List.append_assoc,P] using hk⟩
  rw [suffix_const,suffix_const,suffix_const,suffix_const] at hh
  rcases hh with ⟨q,hq,hqh,hm,hk⟩|⟨e,he,heM,hm,hk⟩|⟨q,hq,hqR,hm,hk⟩|
    ⟨e,he,heR,hm,hk⟩|⟨t,ht,hm,hk⟩
  · have he := initial_S_third_ray_exception q M R i hq hR
      (by simpa only [List.append_assoc] using hm) (by simpa only [List.append_assoc] using hk)
    right
    exact ⟨he.1,he.2.1,he.2.2.2,by omega⟩
  · exact False.elim (first_A_third_ray_key e R hR (by simpa only [List.append_assoc] using hk))
  · exact False.elim (middle_S_third_ray_impossible q R i hR
      (by simpa only [List.append_assoc] using hm) (by simpa only [List.append_assoc] using hk))
  · have heq := runKey_A_S e 1
    have hk' : runKey (List.replicate e true++List.replicate 1 false)=-2 := hk
    rw [heq] at hk'
    omega
  · simp only [List.length_replicate] at ht
    have ht0 : t=0 := by omega
    subst t
    simp only [List.drop_zero,mass_rep_false] at hm
    left
    omega

theorem third_ray_local_count_all (h M R K : Nat) (hR : 5≤R) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) K≤2 := by
  let P := fun i : Nat => i=2
  let Q := fun i : Nat => i=0
  have hp : cN P 0 K≤1 := cN_le_one_of_unique P K (by intro i _ j _ hi hj; omega)
  have hq : cN Q 0 K≤1 := cN_le_one_of_unique Q K (by intro i _ j _ hi hj; omega)
  have hm := cN_mono
    (fun i => Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate h false++List.replicate M true++List.replicate (R+1) false++
        List.replicate R true++List.replicate 1 false)++List.replicate i true)=true)
    (fun i => P i ∨ Q i) 0 K (by
      intro i _ _ hi
      rcases third_ray_local_clocks h M R i hR hi with h|h
      · exact Or.inl h
      · exact Or.inr h.2.2.1)
  have hu := cN_or_le P Q K
  unfold rayCount
  omega

theorem third_ray_local_count_M4 (h R K : Nat) (hR : 5≤R) :
    rayCount (List.replicate h false++List.replicate 4 true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) K≤1 := by
  apply cN_le_one_of_unique
  intro i _ j _ hi hj
  have hi2 := third_ray_local_clocks h 4 R i hR hi
  have hj2 := third_ray_local_clocks h 4 R j hR hj
  rcases hi2 with hi|hi <;> rcases hj2 with hj|hj <;> omega

theorem R5_M5_local_clock0 :
    Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate 2 false++List.replicate 5 true++List.replicate 6 false++
        List.replicate 5 true++List.replicate 1 false)=true := by decide

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,cntF,ih]

/-- A real supply bound in each later run, including all old starts from
    the same BlockWord. It does not assume any source tag or free count. -/
theorem family_later_supply_bounds_all (f : Nat → Bool) (n h M R : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hR : 5≤R)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+(R+1) → f x=false)
    (hA2 : ∀ i, i<R → f (n+h+M+(R+1)+i)=true)
    (hS3 : f (n+h+M+(R+1)+R)=false)
    (hA3 : ∀ i, i<R+1 → f (n+h+M+(R+1)+R+1+i)=true) :
    cN (EndN f 0) (n+h+M+(R+1)) R≤3 ∧
      cN (EndN f 0) (n+h+M+(R+1)+R+1) (R+1)≤3 ∧
      (M=4 → cN (EndN f 0) (n+h+M+(R+1)+R+1) (R+1)≤2) := by
  have ha1 : seg f (n+h) M=List.replicate M true := by
    apply seg_A
    intro x hx hxM
    simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+h)) (by omega)
  have hp2 : seg f 0 (n+h+M+(R+1))=
      w++(List.replicate h false++List.replicate M true++List.replicate (R+1) false) := by
    rw [seg_add,show 0+(n+h+M)=n+h+M by omega,seg_false f (n+h+M) (R+1) hS2,
      seg_add,show 0+(n+h)=n+h by omega,ha1,
      seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
    simp only [List.append_assoc]
  have ha2 : seg f (n+h+M+(R+1)) R=List.replicate R true := by
    apply seg_A
    intro x hx hxR
    simpa only [Nat.add_sub_cancel' hx] using hA2 (x-(n+h+M+(R+1))) (by omega)
  have hs3 : seg f (n+h+M+(R+1)+R) 1=List.replicate 1 false := by
    apply seg_false
    intro x hx hx1
    have he : x=n+h+M+(R+1)+R := by omega
    subst x
    exact hS3
  have hp3 : seg f 0 (n+h+M+(R+1)+R+1)=
      w++(List.replicate h false++List.replicate M true++List.replicate (R+1) false++
        List.replicate R true++List.replicate 1 false) := by
    rw [seg_add,show 0+(n+h+M+(R+1)+R)=n+h+M+(R+1)+R by omega,hs3,
      seg_add,show 0+(n+h+M+(R+1))=n+h+M+(R+1) by omega,ha2,hp2]
    simp only [List.append_assoc]
  have hs2 : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate (R+1) false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have hs3 : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A]
    omega
  have hb2 := block_rayCount_append hw _ hs2 R
  have hb3 := block_rayCount_append hw _ hs3 (R+1)
  have hl2 := rayCount_S_A_S h M (R+1) R
  have hl3 := third_ray_local_count_all h M R (R+1) hR
  have he2 := endable_A_run_count f (n+h+M+(R+1)) R _ hp2 hA2
  have he3 := endable_A_run_count f (n+h+M+(R+1)+R+1) (R+1) _ hp3 hA3
  refine ⟨by omega,by omega,?_⟩
  intro hm4
  subst M
  have hl4 := third_ray_local_count_M4 h R (R+1) hR
  omega

end Recaman.SourceFamilyFirstBlock
