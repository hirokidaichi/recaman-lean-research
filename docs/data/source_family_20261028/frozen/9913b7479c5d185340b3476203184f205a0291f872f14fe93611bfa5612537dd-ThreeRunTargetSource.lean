import Recaman.PenultimateRunWindow

namespace Recaman.ThreeRunTargetSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.ThreeRunSupplyBudget
open Recaman.SeparatorSupplyReset Recaman.PenultimateRunWindow
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- In a genuine three-run counterexample every target window starts before
the second A run. This leaves early local and old windows unresolved. -/
theorem three_run_target_source_before_second_A (f : Nat → Bool) (n h M m L s T j t : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
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
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T)<j+1)
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) : t<n+h+M+m := by
  have hr := three_run_free_gap_residual f n h M m L s T j w hw hpre
    hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad
  have hj4 : 4≤j := by omega
  have hM : 0<M := by
    by_cases hM0 : M=0
    · have hSm : ∀ x, n≤x → x<n+(h+m) → f x=false := by
        intro x hx hxm
        by_cases hxh : x<n+h
        · exact hS x hx hxh
        · exact hS2 x (by omega) (by omega)
      have hh := two_A_run_free_gap f n (h+m) L s T j w hw hpre hSm
        (by intro i hi; simpa only [hM0,Nat.add_zero,Nat.add_assoc] using hA2 i hi)
        (by intro x hx hxx; exact hS3 x (by omega) (by omega))
        (by intro i hi; simpa only [hM0,Nat.add_zero,Nat.add_assoc] using hA3 i hi)
        (by omega)
        (by simpa only [hM0,Nat.add_zero,Nat.add_assoc] using hpos)
        (by intro x hx hxx; exact hgap x (by omega) (by omega))
        (by simpa only [hM0,Nat.add_zero,Nat.add_assoc] using he)
      simp only [hM0,Nat.add_zero,Nat.add_assoc] at hbad hh
      omega
    · omega
  have hAT : seg f (n+h+M+m+L+s) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    have ha := hA3 (x-(n+h+M+m+L+s)) (by omega)
    simpa only [Nat.add_sub_cancel' hx] using ha
  have hnotlast : ¬n+h+M+m+L≤t := by
    intro ht
    have hlocal : EndN f (n+h+M+m+L) (n+h+M+m+L+s+T+j) :=
      ⟨he.1,t,_,ht,by have hk:=hwin.1; omega,hwin⟩
    have hword : seg f (n+h+M+m+L) (s+T+j)=List.replicate s false++
        List.replicate T true++List.replicate j false := by
      rw [seg_add,show n+h+M+m+L+(s+T)=n+h+M+m+L+s+T by omega,
        seg_false f (n+h+M+m+L+s+T) j hgap,seg_add,
        show n+h+M+m+L+s=n+h+M+m+L+s by rfl,hAT,
        seg_false f (n+h+M+m+L) s hS3]
    have hl := (localSupply_seg_iff f (n+h+M+m+L) (n+h+M+m+L+s+T+j) (by omega) he.1).mpr hlocal
    rw [show n+h+M+m+L+s+T+j-(n+h+M+m+L)=s+T+j by omega,hword] at hl
    have hclass := (localSupply_three_runs_iff s T j).mp hl
    let rs : List (Bool × Nat):=[(false,h),(true,M),(false,m),(true,L),(false,s)]
    have hshape := three_run_word f n h M m L s 0 hS hA hS2 hA2 hS3 (by intro i hi; omega)
    have hp : seg f 0 (n+h+M+m+L+s)=w++runWord rs := by
      rw [show n+h+M+m+L+s=n+(h+M+m+L+s) by omega,seg_add,Nat.zero_add,hpre]
      congr 1
      simpa only [rs,runWord,List.replicate_zero,List.append_nil,Nat.add_zero,List.append_assoc] using hshape
    have hcnt := cntF_int (runWord rs)
    simp only [rs,runWord,List.length_append,List.length_replicate,ones_append,
      ones_replicate_S,ones_replicate_A,List.length_nil,ones,Int.add_zero] at hcnt
    have hbudget := block_A_run_free_budget f (n+h+M+m+L+s) T w rs hw hp (by dsimp only [rs,runWord]; omega) hA3
    have hbl : rs.length=5 := by rfl
    rw [hbl] at hbudget
    let P:=fun i => f i=true ∧ ¬EndN f 0 i
    have hfirst : P (n+h) := by
      constructor
      · simpa only [Nat.add_zero] using hA 0 hM
      · simpa only [Nat.add_zero] using first_two_A_not_supplied f n h M w hw hpre hS hA 0 hM (by omega)
    have hsucc := cN_succ_pos P n h hfirst
    have hprior := count_prefix_le P n (h+1) (h+M+m+L+s) (by omega)
    have hsum := cN_add P n (h+M+m+L+s) T
    change T≤cN P (n+h+M+m+L+s) T+1+5 at hbudget
    change cN P n (h+M+m+L+s+T)<j+1 at hbad
    simp only [Nat.add_assoc] at hsucc hprior hsum hbudget hbad
    omega
  have hnotsecond := three_run_counterexample_not_second_A f n h M m L s T j t w hw hpre
    hS hA hS2 hA2 hS3 hA3 hB hpos hgap he hbad hwin
  omega

end Recaman.ThreeRunTargetSource
