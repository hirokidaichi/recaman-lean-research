import Recaman.RunSupplyBudget

namespace Recaman.FirstRunPrefixCounts

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.RunSupplyBudget
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem first_run_prefix_count (f : Nat → Bool) (n h M k : Nat) (hk : k≤h+M)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) :
    cN (fun x=>f x=true) n k=k-h := by
  have hS0 : cN (fun x=>f x=true) n h=0 := by
    apply cN_zero_of
    intro x hx hxh ha
    have hf:=hS x hx hxh
    rw [hf] at ha
    contradiction
  by_cases hkh : k≤h
  · have hc : cN (fun x=>f x=true) n k=0 := by
      apply cN_zero_of
      intro x hx hxk ha
      have hf:=hS x hx (by omega)
      rw [hf] at ha
      contradiction
    omega
  · have hc:=cN_add (fun x=>f x=true) n h (k-h)
    have ha:=count_A_run f (n+h) (k-h) (fun i hi=>hA i (by omega))
    rw [show h+(k-h)=k by omega,hS0,ha] at hc
    omega

theorem middle_S_prefix_count (f : Nat → Bool) (n h M m k : Nat)
    (hk : h+M≤k) (hkm : k≤h+M+m)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false) :
    cN (fun x=>f x=true) n k=M := by
  have hp:=first_run_prefix_count f n h M (h+M) (by omega) hS hA
  have hS0 : cN (fun x=>f x=true) (n+(h+M)) (k-(h+M))=0 := by
    apply cN_zero_of
    intro x hx hxk ha
    have hf:=hS2 x (by omega) (by omega)
    rw [hf] at ha
    contradiction
  have hc:=cN_add (fun x=>f x=true) n (h+M) (k-(h+M))
  rw [show h+M+(k-(h+M))=k by omega,hS0] at hc
  omega

end Recaman.FirstRunPrefixCounts
