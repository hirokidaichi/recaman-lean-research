import Recaman.ShortCounterJointCounts
import Recaman.ShortCounterFactorBounds

namespace Recaman.HeadRunSupplyBudgets

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem count_translate (P : Nat → Prop) (N : Nat) :
    ∀ K, cN P N K=cN (fun i=>P (N+i)) 0 K
  | 0 => rfl
  | K+1 => by
      classical
      simpa only [cN,Nat.zero_add] using
        congrArg (fun z : Nat=>z+(if P (N+K) then 1 else 0)) (count_translate P N K)

/-- Under the explicit long separator condition, only clock2 can be
supplied in the first A-run. All old sources are handled by the barrier. -/
theorem first_long_clock (f : Nat → Bool) (n h M : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hlong : 2*M≤h+3)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) (i : Nat) (hi : i<M)
    (he : EndN f 0 (n+h+i)) : i=2 := by
  by_cases hi2 : i<2
  · exact False.elim (Recaman.ThreeRunSupplyBudget.first_two_A_not_supplied f n h M w hw hpre hS hA i hi hi2 he)
  have hp0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  have hword : seg f n (0+h+i+0)=[]++(List.replicate h false++List.replicate i true++List.replicate 0 false) := by
    simp only [Nat.zero_add,Nat.add_zero,List.replicate_zero,List.append_nil,List.nil_append]
    rw [seg_add,seg_false f n h hS]
    congr 1
    apply seg_A
    intro x hx hxB
    have ha:=hA (x-(n+h)) (by omega)
    rw [Nat.add_sub_cancel' hx] at ha
    exact ha
  have hiff:=endable_after_prefix_manyS_A_iff f n 0 h i 0 [] hw hp0 (by omega)
    (by simp only [ones]; omega) hword
    (by simpa only [List.length_nil,Nat.zero_add,Nat.add_zero,Nat.add_assoc] using hA i hi)
  have hx:=hiff.mp (by simpa only [List.length_nil,Nat.zero_add,Nat.add_zero,Nat.add_assoc] using he)
  omega

theorem first_long_one (f : Nat → Bool) (n h M : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hlong : 2*M≤h+3)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) : cN (EndN f 0) (n+h) M≤1 := by
  rw [count_translate (EndN f 0) (n+h) M]
  apply cN_le_one_of_unique
  intro i hi j hj hei hej
  have h1:=first_long_clock f n h M w hw hpre hlong hS hA i hi (by simpa only [Nat.add_assoc] using hei)
  have h2:=first_long_clock f n h M w hw hpre hlong hS hA j hj (by simpa only [Nat.add_assoc] using hej)
  omega

theorem first_two_zero (f : Nat → Bool) (n h M : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hM2 : M≤2)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) : cN (EndN f 0) (n+h) M=0 := by
  apply cN_zero_of
  intro x hx hxB he
  have hn:=Recaman.ThreeRunSupplyBudget.first_two_A_not_supplied f n h M w hw hpre hS hA
    (x-(n+h)) (by omega) (by omega)
  rw [Nat.add_sub_cancel' hx] at hn
  exact hn he

/-- M3/m1 has no initial-S local source because its required square is7. -/
theorem second_three_one_local (h K : Nat) :
    rayCount (List.replicate h false++List.replicate 3 true++List.replicate 1 false) K≤1 := by
  unfold rayCount
  apply cN_le_one_of_unique
  have only2 (i : Nat) (hi : Recaman.ThreeNonsuppliedData.localSupply
      ((List.replicate h false++List.replicate 3 true++List.replicate 1 false)++List.replicate i true)=true) : i=2 := by
    have he:=localSupply_two_run_iff h 3 1 i 0
    simp only [List.replicate_zero,List.append_nil,Nat.zero_add,Int.natCast_zero,Int.zero_add,Nat.mul_one,Int.one_pow] at he
    rcases he.mp hi with ⟨q,hq,hqh,hm,hk⟩|⟨a,ha,haM,hm,hk⟩|hlast
    · change (1 : Int)=((q : Int)+1)^2-6 at hk
      have hsq : ((q : Int)+1)^2=7 := by omega
      by_cases hh : q=1
      · rw [hh] at hsq; contradiction
      · have hx:=Recaman.ShortCounterFactorBounds.square_lower ((q : Int)+1) 3 (by omega) (by omega)
        omega
    · change (1 : Int)=1*((1 : Int)-2*(a : Int)) at hk
      have hx : (1 : Int)=1-2*(a : Int) := by simpa only [Int.one_mul] using hk
      omega
    · omega
  intro i hi j hj hsi hsj
  have h1:=only2 i hsi
  have h2:=only2 j hsj
  omega

private theorem cntF_A (k : Nat) : cntF (List.replicate k true)=0 := by
  have hc:=cntF_int (List.replicate k true)
  rw [List.length_replicate,ones_replicate_A] at hc
  omega

theorem second_actual_bound (f : Nat → Bool) (n h M m L b : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hsum : 3≤h+m)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L≤b) :
    cN (EndN f 0) (n+h+M+m) L≤b+1 := by
  have hp1 : seg f 0 (n+h)=w++List.replicate h false := by
    rw [seg_add,Nat.zero_add,hpre,seg_false f n h hS]
  have hp2 : seg f 0 (n+h+M+m)=w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    have hsegA : seg f (n+h) M=List.replicate M true := by
      apply seg_A
      intro x hx hxB
      have ha:=hA (x-(n+h)) (by omega)
      rw [Nat.add_sub_cancel' hx] at ha
      exact ha
    rw [show n+h+M+m=(n+h+M)+m by omega,seg_add,Nat.zero_add,
      seg_false f (n+h+M) m hS2,show n+h+M=(n+h)+M by omega,seg_add,Nat.zero_add,hp1,hsegA]
    simp only [List.append_assoc]
  have hcS : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false) := by
    simp only [cntF_append,cntF_replicate_S,cntF_A,Nat.add_zero]
    omega
  have hold:=block_rayCount_append hw _ hcS L
  have he:=endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  omega

theorem two_prefix_count (f : Nat → Bool) (n h M m L : Nat)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false) :
    cN (EndN f 0) n (h+M+m+L)=cN (EndN f 0) (n+h) M+cN (EndN f 0) (n+h+M+m) L := by
  have noS (a k : Nat) (hp : ∀ x, a≤x → x<a+k → f x=false) : cN (EndN f 0) a k=0 := by
    apply cN_zero_of
    intro x hx hxB he
    have ha:=he.1
    rw [hp x hx hxB] at ha
    contradiction
  have hz1:=noS n h hS
  have hz2:=noS (n+h+M) m hS2
  have h1:=cN_add (EndN f 0) n h M
  have h2:=cN_add (EndN f 0) n (h+M) m
  have h3:=cN_add (EndN f 0) n (h+M+m) L
  simp only [Nat.add_assoc] at *
  omega

end Recaman.HeadRunSupplyBudgets
