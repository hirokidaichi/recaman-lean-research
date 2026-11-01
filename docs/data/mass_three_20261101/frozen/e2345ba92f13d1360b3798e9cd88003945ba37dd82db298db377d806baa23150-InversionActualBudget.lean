import Recaman.InversionNine
import Recaman.SmallInversionActual
import Recaman.SmallInversionBudget

namespace Recaman.InversionActualBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem count_length (P : Nat → Prop) (n : Nat) : ∀ K, cN P n K≤K
  | 0 => by simp [cN]
  | K+1 => by
    have ih:=count_length P n K
    by_cases hp : P (n+K)
    · rw [cN_succ_pos P n K hp]; omega
    · rw [cN_succ_neg P n K hp]; omega

private theorem endable_S_count_zero (f : Nat → Bool) (s h : Nat)
    (hS : ∀ x, s≤x → x<s+h → f x=false) : cN (EndN f 0) s h=0 := by
  apply cN_zero_of
  intro x hx hxs he
  have hh:=he.1
  rw [hS x hx hxs] at hh
  contradiction

private theorem two_run_with_min_local (f : Nat → Bool) (n h M m L : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true) (hsum : 3≤h+m) :
    cN (EndN f 0) n (h+M+m+L)≤
      rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L+min M 2+1 := by
  have hp1 : seg f 0 (n+h)=w++List.replicate h false := by
    rw [seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
  have hr1 := endable_A_run_count f (n+h) M _ hp1 hA
  have hb1 := block_rayCount_after_S hw h M
  have hr1M:=count_length (EndN f 0) (n+h) M
  have hr1Min : cN (EndN f 0) (n+h) M≤min M 2 := Nat.le_min hr1M (by omega)
  have hp2 : seg f 0 (n+h+M+m)=
      w++(List.replicate h false++List.replicate M true++List.replicate m false) := by
    have hsegA : seg f (n+h) M=List.replicate M true := by
      apply seg_A
      intro x hx hxM
      simpa only [Nat.add_sub_cancel' hx] using hA (x-(n+h)) (by omega)
    rw [show n+h+M+m=(n+h+M)+m by omega,seg_add,
      show 0+(n+h+M)=n+h+M by omega,seg_false f (n+h+M) m hS2,
      show n+h+M=(n+h)+M by omega,seg_add,show 0+(n+h)=n+h by omega,hp1,hsegA]
    simp only [List.append_assoc]
  have hr2 := endable_A_run_count f (n+h+M+m) L _ hp2 hA2
  have hcnt : cntF (List.replicate h false++List.replicate M true++List.replicate m false)=h+m := by
    have aux : ∀ k : Nat, cntF (List.replicate k true)=0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ,cntF,ih]
    have ha := aux M
    simp only [cntF_append,cntF_replicate_S,ha,Nat.add_zero]
  have hb2 := block_rayCount_append hw
      (List.replicate h false++List.replicate M true++List.replicate m false) (by omega) L
  have h0 := endable_S_count_zero f n h hS
  have h2 := endable_S_count_zero f (n+h+M) m hS2
  have hc1 := cN_add (EndN f 0) n h M
  have hc2 := cN_add (EndN f 0) n (h+M) m
  have hc3 := cN_add (EndN f 0) n (h+M+m) L
  simp only [Nat.add_assoc] at *
  omega

theorem three_run_min_joint_budget (f : Nat → Bool) (n h M m L s T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hs : 1≤s) (hSsum : 3≤h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k) :
    cN (EndN f 0) n (h+M+m+L+s+T)≤
      min M 2+rayCount (List.replicate h false++List.replicate M true++List.replicate m false) L+
      rayCount (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false) T+2 := by
  let X:=List.replicate h false++List.replicate M true++List.replicate m false
  let Y:=X++List.replicate L true++List.replicate s false
  have hb2 : cN (EndN f 0) n (h+M+m+L)≤rayCount X L+min M 2+1 := by
    by_cases hh : 3≤h+m
    · exact two_run_with_min_local f n h M m L w hw hpre hS hA hS2 hA2 hh
    · have hp:=hpos (h+M+m+L) (by omega) (by omega)
      have hw2:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L 0 0
        hS hA hS2 hA2 (by intro x hx hx0; omega) (by intro i hi; omega)
      have hc:=cntF_int (seg f n (h+M+m+L))
      have hl:=seg_length f n (h+M+m+L)
      have ho:=ones_seg_eq_count f n (h+M+m+L)
      have heq : seg f n (h+M+m+L)=X++List.replicate L true := by simpa [X] using hw2
      rw [heq] at hc
      simp only [X,ones_append,ones_replicate_A,ones_replicate_S] at hc
      have hwalk:=cN_walk f n (h+M+m+L)
      rw [heq] at ho
      simp only [X,ones_append,ones_replicate_A,ones_replicate_S] at ho
      omega
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0
    hS hA hS2 hA2 hS3 (by intro i hi; omega)
  have hp : seg f 0 (n+h+M+m+L+s)=w++Y := by
    rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
    congr 1
    simpa [X,Y] using hword
  have hcS : 3≤cntF Y := by
    have ha : cntF (List.replicate M true)=0 := by
      have hc:=cntF_int (List.replicate M true)
      rw [List.length_replicate,ones_replicate_A] at hc
      omega
    have hb : cntF (List.replicate L true)=0 := by
      have hc:=cntF_int (List.replicate L true)
      rw [List.length_replicate,ones_replicate_A] at hc
      omega
    simp only [Y,X,cntF_append,cntF_replicate_S,ha,hb]
    omega
  have ho:=block_rayCount_append hw Y hcS T
  have he:=endable_A_run_count f (n+h+M+m+L+s) T _ hp hA3
  have hz:=endable_S_count_zero f (n+h+M+m+L) s hS3
  have a:=cN_add (EndN f 0) n (h+M+m+L) s
  have b:=cN_add (EndN f 0) n (h+M+m+L+s) T
  simp only [Nat.add_assoc] at a b hb2 he hz ⊢
  omega

end Recaman.InversionActualBudget
