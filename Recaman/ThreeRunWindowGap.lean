import Recaman.ThreeRunFreeGap
import Recaman.PrefixSupplyCongruence

namespace Recaman.ThreeRunWindowGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Only the primitive target window is needed. A one-clock endpoint
completion preserves every sign and EndN/free count in the strict past. -/
theorem three_run_window_gap (f : Nat → Bool) (n h M m L s T j t : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<T → f (n+h+M+m+L+s+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (hwin : Win f t (n+h+M+m+L+s+T+j-t)) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+T) := by
  let q:=n+h+M+m+L+s+T+j
  let g:=fun i=>if i=q then true else f i
  have hfg : ∀ i, i<q → f i=g i := by
    intro i hi
    simp only [g,if_neg (show i≠q by omega)]
  have ht : t<q := by have hx:=hwin.1; dsimp [q]; omega
  have hgpre : seg g 0 n=w := by
    rw [←Recaman.PrefixSupplyCongruence.segment_eq f g q 0 n hfg (by dsimp [q]; omega)]
    exact hpre
  have hge : EndN g 0 q := by
    refine ⟨by simp only [g,if_pos rfl],t,q-t,by omega,by omega,?_⟩
    exact (Recaman.PrefixSupplyCongruence.window_iff f g q t (q-t) hfg (by omega)).mp hwin
  rw [Recaman.PrefixSupplyCongruence.free_count_eq f g q 0 n (h+M+m+L+s+T) hfg (by dsimp [q]; omega)]
  apply Recaman.ThreeRunFreeGap.three_run_free_gap g n h M m L s T j w hw hgpre hM hm hL hs hT
  · intro x hx hxH
    rw [←hfg (x) (by dsimp [q]; omega)]
    exact hS x hx hxH
  · intro i hi
    rw [←hfg (n+h+i) (by dsimp [q]; omega)]
    exact hA i hi
  · intro x hx hxH
    rw [←hfg (x) (by dsimp [q]; omega)]
    exact hS2 x hx hxH
  · intro i hi
    rw [←hfg (n+h+M+m+i) (by dsimp [q]; omega)]
    exact hA2 i hi
  · intro x hx hxH
    rw [←hfg (x) (by dsimp [q]; omega)]
    exact hS3 x hx hxH
  · intro i hi
    rw [←hfg (n+h+M+m+L+s+i) (by dsimp [q]; omega)]
    exact hA3 i hi
  · intro k hk hkB
    rw [←Recaman.PrefixSupplyCongruence.supply_count_eq f g q 0 n k hfg (by dsimp [q]; omega),
      ←Recaman.PrefixSupplyCongruence.S_count_eq f g q n k hfg (by dsimp [q]; omega)]
    exact hpos k hk hkB
  · intro x hx hxB
    rw [←hfg x (by dsimp [q]; omega)]
    exact hgap x hx hxB
  · exact hge

end Recaman.ThreeRunWindowGap
