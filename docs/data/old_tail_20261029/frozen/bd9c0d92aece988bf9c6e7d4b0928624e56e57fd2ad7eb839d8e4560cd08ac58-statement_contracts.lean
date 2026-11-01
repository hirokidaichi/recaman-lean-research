import Recaman
set_option autoImplicit false
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.OldTargetMiddleCharge Recaman.InitialSTargetBounds Recaman.InitialSTargetTail
open Recaman.FreePrefixCounterexample Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
namespace Recaman.ResearchStatementContracts

def contract_E_445 : ∀ (e : Int → Bool) (p : Int) (n a t h M m L s T j : Nat) (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (ht : t<n) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T) (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false) (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true) (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false) (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true) (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false) (hA3 : ∀ i, i<T → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true) (hzero : endableCount e p n=subtractionCount e p n) (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j → endableCount e p u+1≤subtractionCount e p u) (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → e (p+(x : Int))=false) (he : Endable e p (p+((n+h+M+m+L+s+T+j : Nat) : Int))) (hwindow : P2 (past e (p+((n+h+M+m+L+s+T+j : Nat) : Int)) (n+h+M+m+L+s+T+j-t))), j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T) := @Recaman.ThreeRunOldTargetGap.three_run_old_target_free_gap_int
#check @Recaman.ThreeRunOldTargetGap.three_run_old_target_free_gap_int

def contract_E_450 : ∀ (e : Int → Bool) (p : Int) (n a h q M m L s T j : Nat) (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (hq : 1≤q) (hqh : q≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T) (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false) (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true) (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false) (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true) (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false) (hA3 : ∀ i, i<T → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true) (hzero : endableCount e p n=subtractionCount e p n) (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j → endableCount e p u+1≤subtractionCount e p u) (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → e (p+(x : Int))=false) (he : Endable e p (p+((n+h+M+m+L+s+T+j : Nat) : Int))) (hwindow : P2 (past e (p+((n+h+M+m+L+s+T+j : Nat) : Int)) (q+M+m+L+s+T+j))), j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T) := @Recaman.ThreeRunInitialSTargetGap.three_run_initial_S_target_free_gap_int
#check @Recaman.ThreeRunInitialSTargetGap.three_run_initial_S_target_free_gap_int

def contract_E_451 : ∀ (e : Int → Bool) (p : Int) (n a h M m L s T j : Nat) (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hT : 1≤T) (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false) (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true) (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false) (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true) (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false) (hA3 : ∀ i, i<T → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true) (hzero : endableCount e p n=subtractionCount e p n) (hpos : ∀ u, n<u → u≤n+h+M+m+L+s+T+j → endableCount e p u+1≤subtractionCount e p u) (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → e (p+(x : Int))=false) (he : Endable e p (p+((n+h+M+m+L+s+T+j : Nat) : Int))), j+1≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+T) := @Recaman.ThreeRunFreeGap.three_run_free_gap_int
#check @Recaman.ThreeRunFreeGap.three_run_free_gap_int

def contract_E_452 : ∀ (f : Nat → Bool) (n s z B i T j : Nat) (hw : BlockWord (seg f 0 n)) (hs : s<n) (hz : n≤z) (hzB : z≤n+B) (hi : i<T) (hj : 2≤j) (hband : T≤i+j) (hA : ∀ k, k<T → f (n+B+k)=true) (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false) (hlocal : Win f z (n+B+i-z)) (htarget : Win f s (n+B+T+j-s)), j+1≤cN (fun x => f x=true) n (z-n) := @Recaman.LocalSourcePrefixBudget.actual_local_source_prefix_A
#check @Recaman.LocalSourcePrefixBudget.actual_local_source_prefix_A

def contract_E_454 : ∀ (f : Nat → Bool) (n s z B i T j : Nat) (hkey : -2≤runKey (seg f s (n-s))) (hs : s<n) (hz : n≤z) (hzB : z≤n+B) (hi : i<T) (hj : 2≤j) (hband : T≤i+j) (hA : ∀ k, k<T → f (n+B+k)=true) (hS : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false) (hlocal : Win f z (n+B+i-z)) (htarget : Win f s (n+B+T+j-s)), j+1≤cN (fun x => f x=true) n (z-n) := @Recaman.PrefixKeySourceBudget.actual_local_source_prefix_A_of_key
#check @Recaman.PrefixKeySourceBudget.actual_local_source_prefix_A_of_key

def contract_E_453 : BlockWord (seg f 0 1) ∧ cN (EndN f 0) 0 1=cN (fun x => f x=false) 0 1 ∧ (∀ k, 1<k → k≤27 → cN (EndN f 0) 0 k+1≤cN (fun x => f x=false) 0 k) ∧ Win f 0 27 ∧ Win f 12 7 ∧ f 27=true ∧ f 19=true ∧ cN (fun x => f x=true) 1 11=5 ∧ cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 11=4 ∧ cN (fun x => f x=true ∧ ¬EndN f 0 x) 1 22=10 := @Recaman.FreePrefixCounterexample.free_before_source_counterexample
#check @Recaman.FreePrefixCounterexample.free_before_source_counterexample
end Recaman.ResearchStatementContracts
