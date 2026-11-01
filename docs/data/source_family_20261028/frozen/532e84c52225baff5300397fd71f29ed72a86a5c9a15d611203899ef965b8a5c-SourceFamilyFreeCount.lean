import Recaman.ThreeRunSupplyBudget

namespace Recaman.SourceFamilyFreeCount

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget
open Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
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

theorem runKey_five_runs (q M m L s : Nat) :
    runKey (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)=
      4*(M : Int)*((m : Int)+(s : Int))+4*(L : Int)*(s : Int)-
        2*((q : Int)+(m : Int)+(s : Int))^2 := by
  rw [runKey_append_S,runKey_append_A,runKey_S_A_S]
  simp only [mass_append,mass_rep_false,mass_replicate_A]
  grind

private theorem first_A_key_impossible (e R : Nat) (he : 1≤e) (he3 : e≤3)
    (hR : 5≤R) :
    ¬runKey (List.replicate e true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  have hz := runKey_five_runs 0 e (R+1) R 1
  simp only [List.replicate_zero,List.nil_append] at hz
  rw [hz] at hk
  simp only [Int.natCast_add,Int.natCast_one] at hk
  by_cases hr5 : R=5
  · subst R
    have hc : e=1 ∨ e=2 ∨ e=3 := by omega
    rcases hc with rfl|rfl|rfl <;> simp at hk
  · have hp := Int.mul_nonneg (show 0≤(R : Int)-6 by omega)
      (show 0≤(R : Int)+2 by omega)
    have heprod := Int.mul_nonneg (show 0≤3-(e : Int) by omega)
      (show 0≤2*((R : Int)+2) by omega)
    have eq : 2*(e : Int)*((R : Int)+2)=(R : Int)^2+2*(R : Int)+3 := by grind
    grind

private theorem first_S_key_impossible (q M R : Nat) (hq : 1≤q) (hM : M≤3)
    (hR : 5≤R) :
    ¬runKey (List.replicate q false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  rw [runKey_five_runs] at hk
  simp only [Int.natCast_add,Int.natCast_one] at hk
  have hp := Int.mul_nonneg (show 0≤(q : Int)-1 by omega)
    (show 0≤(q : Int)+2*(R : Int)+5 by omega)
  have hr := Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
    (show 0≤(R : Int)+3 by omega)
  have hm := Int.mul_nonneg (show 0≤3-(M : Int) by omega)
    (show 0≤2*((R : Int)+2) by omega)
  grind

private theorem middle_S_key_impossible (q R i : Nat) (hq : 1≤q) (hR : 5≤R)
    (hm : mass (List.replicate q false++List.replicate R true++List.replicate 1 false)+
      (i : Int)=1) :
    ¬runKey (List.replicate q false++List.replicate R true++List.replicate 1 false)=-2 := by
  intro hk
  rw [runKey_S_A_S] at hk
  simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
  have hp := Int.mul_nonneg (show 0≤(q : Int)+2-(R : Int) by omega)
    (show 0≤(q : Int)+(R : Int) by omega)
  have hr := Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
    (show 0≤(R : Int)+1 by omega)
  grind

/-- All five local source runs are retained. For this family every local
    supply along the third A ray is at clock2, for unbounded R and h. -/
theorem third_ray_local_clock (h M R i : Nat) (hM : M≤3) (hR : 5≤R)
    (hs : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
        List.replicate R true++List.replicate 1 false++List.replicate i true)=true) : i=2 := by
  obtain ⟨t,ht,hm,hk⟩ := (localSupply_A_S_iff
    (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) i 0).mp (by simpa using hs)
  let P := fun v : List Bool => mass v+(i : Int)=1 ∧ runKey v=-2
  have hh : ∃ t, t<(List.replicate h false++(List.replicate M true++
      (List.replicate (R+1) false++(List.replicate R true++List.replicate 1 false)))).length ∧
      P ((List.replicate h false++(List.replicate M true++
      (List.replicate (R+1) false++(List.replicate R true++List.replicate 1 false)))).drop t) := by
    exact ⟨t,by simpa only [List.append_assoc] using ht,
      by simpa [List.append_assoc,P] using hm,
      by simpa [List.append_assoc,P] using hk⟩
  rw [suffix_const,suffix_const,suffix_const,suffix_const] at hh
  rcases hh with ⟨q,hq,hqh,hm,hk⟩|⟨e,he,heM,hm,hk⟩|⟨q,hq,hqR,hm,hk⟩|
    ⟨e,he,heR,hm,hk⟩|⟨t,ht,hm,hk⟩
  · exact False.elim (first_S_key_impossible q M R hq hM hR (by simpa only [List.append_assoc] using hk))
  · exact False.elim (first_A_key_impossible e R he (by omega) hR (by simpa only [List.append_assoc] using hk))
  · exact False.elim (middle_S_key_impossible q R i hq hR
      (by simpa only [List.append_assoc] using hm) (by simpa only [List.append_assoc] using hk))
  · have heq := runKey_A_S e 1
    have hk' : runKey (List.replicate e true++List.replicate 1 false)=-2 := hk
    rw [heq] at hk'
    omega
  · simp only [List.length_replicate] at ht
    have ht0 : t=0 := by omega
    subst t
    simp only [List.drop_zero,mass_rep_false] at hm
    omega

/-- The second ray has the same sole local supply clock. The first S run
    may be empty; neither R nor the source length is finitely bounded. -/
theorem second_ray_local_clock (h M R i : Nat) (hM : M≤3) (hR : 5≤R)
    (hs : Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
        List.replicate i true)=true) : i=2 := by
  have he := (localSupply_two_run_iff h M (R+1) i 0).mp (by simpa using hs)
  simp only [Int.natCast_zero,Int.zero_add,Int.natCast_add,Int.natCast_one] at he
  rcases he with ⟨q,hq,hqh,hbal,hkey⟩|⟨e,he,heM,hbal,hkey⟩|⟨hi,hm⟩
  · have hp := Int.mul_nonneg (show 0≤(q : Int)-1 by omega)
      (show 0≤(q : Int)+2*(R : Int)+3 by omega)
    have hr := Int.mul_nonneg (show 0≤(R : Int)-5 by omega)
      (show 0≤(R : Int)+3 by omega)
    have hm := Int.mul_nonneg (show 0≤3-(M : Int) by omega)
      (show 0≤2*((R : Int)+1) by omega)
    grind
  · by_cases hz : (R : Int)+1-2*(e : Int)=0
    · rw [hz] at hkey
      simp at hkey
    · have hp := Int.mul_nonneg (show 0≤(R : Int)+1-2*(e : Int)-1 by omega)
        (show 0≤(R : Int)+1 by omega)
      grind
  · omega

theorem second_ray_local_count (h M R K : Nat) (hM : M≤3) (hR : 5≤R) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate (R+1) false) K≤1 := by
  apply cN_le_one_of_unique
  intro i _ j _ hi hj
  have hi2 := second_ray_local_clock h M R i hM hR hi
  have hj2 := second_ray_local_clock h M R j hM hR hj
  omega

theorem third_ray_local_count (h M R K : Nat) (hM : M≤3) (hR : 5≤R) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate (R+1) false++
      List.replicate R true++List.replicate 1 false) K≤1 := by
  apply cN_le_one_of_unique
  intro i _ j _ hi hj
  have hi2 := third_ray_local_clock h M R i hM hR hi
  have hj2 := third_ray_local_clock h M R j hM hR hj
  omega

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,cntF,ih]

/-- A real supply bound in each later run, including all old starts from
    the same BlockWord. It does not assume any source tag or free count. -/
theorem family_later_supply_bounds (f : Nat → Bool) (n h M R : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM : M≤3) (hR : 5≤R)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+(R+1) → f x=false)
    (hA2 : ∀ i, i<R → f (n+h+M+(R+1)+i)=true)
    (hS3 : f (n+h+M+(R+1)+R)=false)
    (hA3 : ∀ i, i<R+1 → f (n+h+M+(R+1)+R+1+i)=true) :
    cN (EndN f 0) (n+h+M+(R+1)) R≤2 ∧
      cN (EndN f 0) (n+h+M+(R+1)+R+1) (R+1)≤2 := by
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
  have hl2 := second_ray_local_count h M R R hM hR
  have hl3 := third_ray_local_count h M R (R+1) hM hR
  have he2 := endable_A_run_count f (n+h+M+(R+1)) R _ hp2 hA2
  have he3 := endable_A_run_count f (n+h+M+(R+1)+R+1) (R+1) _ hp3 hA3
  omega

/-- Original-base actual free A in this three-run family grow linearly in R.
    No zero, deficit, target supply or finite history bound is assumed. -/
theorem family_free_lower (f : Nat → Bool) (n h M R : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM1 : 1≤M) (hM3 : M≤3) (hR : 5≤R)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+(R+1) → f x=false)
    (hA2 : ∀ i, i<R → f (n+h+M+(R+1)+i)=true)
    (hS3 : f (n+h+M+(R+1)+R)=false)
    (hA3 : ∀ i, i<R+1 → f (n+h+M+(R+1)+R+1+i)=true) :
    2*R-2≤cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+3*R+3) := by
  let P := fun i => f i=true ∧ ¬EndN f 0 i
  have hb := family_later_supply_bounds f n h M R w hw hpre hM3 hR hS hA hS2 hA2 hS3 hA3
  have h0 : P (n+h+0) := ⟨hA 0 (by omega),
    first_two_A_not_supplied f n h M w hw hpre hS hA 0 (by omega) (by omega)⟩
  have hc0 := cN_succ_pos P (n+h) 0 h0
  have hp0 := count_prefix_le P (n+h) 1 M hM1
  have hp2 := addition_endable_partition f (n+h+M+(R+1)) R
  have hp3 := addition_endable_partition f (n+h+M+(R+1)+R+1) (R+1)
  rw [count_A_run f _ R hA2] at hp2
  rw [count_A_run f _ (R+1) hA3] at hp3
  have hfirst : 1≤cN P (n+h) M := by
    change cN P (n+h) 1=cN P (n+h) 0+1 at hc0
    omega
  have hsecond : R≤cN P (n+h+M+(R+1)) R+2 := by
    change R=_+cN P (n+h+M+(R+1)) R at hp2
    omega
  have hthird : R+1≤cN P (n+h+M+(R+1)+R+1) (R+1)+2 := by
    change R+1=_+cN P (n+h+M+(R+1)+R+1) (R+1) at hp3
    omega
  have a := cN_add P n h M
  have b := cN_add P n (h+M) (R+1)
  have c := cN_add P n (h+M+(R+1)) R
  have d := cN_add P n (h+M+(R+1)+R) 1
  have e := cN_add P n (h+M+(R+1)+R+1) (R+1)
  change 2*R-2≤cN P n (h+M+3*R+3)
  change R=_+cN P (n+h+M+(R+1)) R at hp2
  change R+1=_+cN P (n+h+M+(R+1)+R+1) (R+1) at hp3
  rw [show h+M+3*R+3=h+M+(R+1)+R+1+(R+1) by omega]
  simp only [Nat.add_assoc] at *
  omega

end Recaman.SourceFamilyFreeCount
