import Recaman.OldContextBudget

namespace Recaman.ThreeRunFiniteContext

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.ThreeRunSupplyBudget
open Recaman.SeparatorSupplyReset Recaman.SeparatorTailFreeGap Recaman.InitialSeparatorTrim Recaman.OldContextBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem suffix_segment (f : Nat → Bool) (n : Nat) (u v : List Bool)
    (hword : seg f n (u.length+v.length)=u++v) : seg f (n+u.length) v.length=v := by
  have hd := seg_drop f n (u.length+v.length) u.length (by omega)
  rw [hword,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at hd
  simpa only [Nat.add_sub_cancel_left] using hd.symm

/-- A genuine arbitrary-length three-run free-gap counterexample has an
actual bounded-context representative. This reduction does not establish
absence of representatives, and assumes no zero deficit for the new prefix. -/
theorem three_run_counterexample_context (f : Nat → Bool) (n h M m L s T j : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hB : 0<h+M+m+L+s+T)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+T+j))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1) :
    ∃ (g : Nat → Bool) (N H : Nat),
      BlockWord (seg g 0 N) ∧ N≤47 ∧ H≤39 ∧ m<39 ∧ s<39 ∧ M+L+T≤20 ∧ j≤9 ∧
      N+H+M+m+L+s+T+j≤191 ∧
      seg g N (H+M+m+L+s+T+j)=List.replicate H false++List.replicate M true++
        List.replicate m false++List.replicate L true++List.replicate s false++
        List.replicate T true++List.replicate j false ∧
      EndN g 0 (N+H+M+m+L+s+T+j) ∧
      cN (fun i => g i=true ∧ ¬EndN g 0 i) N (H+M+m+L+s+T)=
        cN (fun i => f i=true ∧ ¬EndN f 0 i) n (h+M+m+L+s+T) ∧
      cN (fun i => g i=true ∧ ¬EndN g 0 i) N (H+M+m+L+s+T)<j+1 ∧
      (∀ k, 0<k → k≤H+M+m+L+s+T →
        cN (EndN g 0) N k+1≤cN (fun i => g i=false) N k) := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre hS hA hS2 hA2 hS3 hA3
    hB hpos hgap he hbad
  have hss := three_run_counterexample_internal_S_bounds f n h M m L s T j w hw hpre
    hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad
  have hshape := three_run_word f n h M m L s T hS hA hS2 hA2 hS3 hA3
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate T true
  have hxl : x.length=M+m+L+s+T := by simp only [x,List.length_append,List.length_replicate]
  have hword : seg f n (h+x.length)=List.replicate h false++x := by
    simpa only [x,List.length_append,List.length_replicate,List.append_assoc,Nat.add_assoc] using hshape
  have ho := ones_seg_eq_count f n (h+x.length)
  rw [hword,ones_append,ones_replicate_S] at ho
  have hxo : ones x≤(20 : Int) := by
    have hb : cN (fun i => f i=true) n (h+x.length)≤20 := by
      simpa only [hxl,Nat.add_assoc] using hr.2.2.1
    omega
  have hMA : M+L+T≤20 := by
    have hx : ones x=(M : Int)+(L : Int)+(T : Int) := by
      simp only [x,ones_append,ones_replicate_A,ones_replicate_S]; omega
    omega
  have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
  have hwj : seg f n (h+(x++List.replicate j false).length)=
      List.replicate h false++(x++List.replicate j false) := by
    simp only [List.length_append,List.length_replicate]
    rw [show h+(x.length+j)=h+x.length+j by omega,seg_add,
      show n+(h+x.length)=n+h+M+m+L+s+T by rw [hxl]; omega,
      seg_false f (n+h+M+m+L+s+T) j hgap,hword]
    simp only [List.append_assoc]
  by_cases hh : 39≤h
  · let g:=trimSSequence f (n+h) 39
    have ht := initial_S_counterexample_transfer f n 0 h 20 39 j x hw hpre0 hword
      (by omega) hxo hh (by omega)
      (by simpa only [hxl,Nat.add_assoc] using hgap)
      (by simpa only [hxl,Nat.add_assoc] using he)
      (by simpa only [hxl,Nat.add_assoc] using hbad)
    have hfc := initial_S_full_free_count f n 0 h 20 39 x hw hpre0 hword
      (by omega) hxo hh (by omega)
    have hfuture : seg f (n+h) (x++List.replicate j false).length=x++List.replicate j false := by
      simpa only [List.length_replicate] using suffix_segment f n (List.replicate h false)
        (x++List.replicate j false) (by simpa only [List.length_replicate] using hwj)
    have hgw : seg g 0 (39+M+m+L+s+T+j)=List.replicate 39 false++x++List.replicate j false := by
      have hp := trimS_prefix f (n+h) 39 (x++List.replicate j false).length
      rw [hfuture] at hp
      simpa only [g,hxl,List.length_append,List.length_replicate,Nat.add_assoc,List.append_assoc] using hp
    refine ⟨g,0,39,?_,by omega,by omega,hss.1,hss.2,hMA,hr.2.2.2,by omega,?_,?_,?_,?_,?_⟩
    · exact BlockWord.nil
    · simpa only [Nat.zero_add,x,List.append_assoc] using hgw
    · simpa only [g,hxl,Nat.zero_add,Nat.add_assoc] using ht.2.1
    · simpa only [g,hxl,Nat.add_assoc] using hfc.symm
    · simpa only [g,hxl,Nat.zero_add,Nat.add_assoc] using ht.1
    · intro k hk hkB
      exact ht.2.2.1 k hk (by rw [hxl]; omega)
  · let z:=List.replicate h false++(x++List.replicate j false)
    have hzl : z.length=h+M+m+L+s+T+j := by
      simp only [z,x,List.length_append,List.length_replicate]
      omega
    have hzword : seg f n z.length=z := by
      simpa only [z,List.length_append,List.length_replicate,Nat.add_assoc] using hwj
    have hzo : ones z≤(20 : Int) := by
      simp only [z,ones_append,ones_replicate_S]
      omega
    have hc := budget_context_rebase f n 0 20 z hw hpre0 hzword (by omega) hzo
    have h47 : 5*(20-1)/2=47 := by decide
    simp only [h47] at hc
    let q:=n-47
    let g:=fun i => f (q+i)
    have hN : n-q≤47 := by dsimp [q]; omega
    have hcount := hc.2.2.2.2 (h+M+m+L+s+T) (by rw [hzl]; omega)
    have hend := (hc.2.2.2.1 z.length (Nat.le_refl _)).mp (by simpa only [hzl,Nat.add_assoc] using he)
    have hp := budget_context_positive_transfer f n 0 20 (List.replicate h false++x) hw hpre0
      (by simpa only [List.length_append,List.length_replicate] using hword) (by omega)
      (by simp only [ones_append,ones_replicate_S]; omega)
      (by simpa only [hxl,List.length_append,List.length_replicate,Nat.add_assoc] using hpos)
    simp only [h47] at hp
    refine ⟨g,n-q,h,hc.1,hN,by omega,hss.1,hss.2,hMA,hr.2.2.2,by omega,?_,?_,?_,?_,?_⟩
    · have hhg := hc.2.2.1
      rw [hzl] at hhg
      simpa only [g,q,z,x,List.append_assoc] using hhg
    · simpa only [g,q,hzl,Nat.add_assoc] using hend
    · exact hcount.2.symm
    · rw [hcount.2] at hbad
      exact hbad
    · simpa only [g,q,hxl,List.length_append,List.length_replicate,Nat.add_assoc] using hp

end Recaman.ThreeRunFiniteContext
