import Recaman.FourRunSupplyBudget
set_option autoImplicit false
open Classical
open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
namespace ResearchFourRunStatementContract
def exact_original_p_type : ∀ (e : Int → Bool) (p : Int) (n a h M m L s U v T j : Nat) (w : List Bool) (hw : BlockWord w) (hpre : segment e p n=w++List.replicate a true) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hS : ∀ x, n≤x → x<n+h → e (p+(x : Int))=false) (hA : ∀ i, i<M → e (p+((n+h+i : Nat) : Int))=true) (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → e (p+(x : Int))=false) (hA2 : ∀ i, i<L → e (p+((n+h+M+m+i : Nat) : Int))=true) (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → e (p+(x : Int))=false) (hA3 : ∀ i, i<U → e (p+((n+h+M+m+L+s+i : Nat) : Int))=true) (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → e (p+(x : Int))=false) (hA4 : ∀ i, i<T → e (p+((n+h+M+m+L+s+U+v+i : Nat) : Int))=true) (hzero : endableCount e p n=subtractionCount e p n) (hpos : ∀ q, n<q → q≤n+h+M+m+L+s+U+v+T+j → endableCount e p q+1≤subtractionCount e p q) (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → e (p+(x : Int))=false) (he : Endable e p (p+((n+h+M+m+L+s+U+v+T+j : Nat) : Int))), countP (Endable e p) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤19 ∧ (countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)<j+1 → 4≤countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T) ∧ countP (fun x => e x=true ∧ ¬Endable e p x) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤17 ∧ countP (fun x => e x=true) (p+(n : Int)) (h+M+m+L+s+U+v+T)≤36 ∧ j≤17) := @Recaman.FourRunSupplyBudget.four_run_bounds_int
end ResearchFourRunStatementContract
