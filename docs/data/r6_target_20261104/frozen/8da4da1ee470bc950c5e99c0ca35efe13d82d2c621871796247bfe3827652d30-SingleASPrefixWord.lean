import Recaman.FirstRunPrefixCounts
import Recaman.SourceCrossSurplus

namespace Recaman.SingleASPrefixWord

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.RunSupplyBudget
open Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem middle_prefix_word (f : Nat → Bool) (n h M m k : Nat)
    (hk : h+M≤k) (hkm : k≤h+M+m)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false) :
    seg f n k=List.replicate h false++List.replicate M true++List.replicate (k-(h+M)) false := by
  have ha : seg f (n+h) M=List.replicate M true := by
    apply seg_A
    intro x hx hxM
    have hxA:=hA (x-(n+h)) (by omega)
    rw [Nat.add_sub_cancel' hx] at hxA
    exact hxA
  rw [show k=(h+M)+(k-(h+M)) by omega,seg_add,seg_add,seg_false f n h hS,ha]
  congr 1
  rw [show h+M+(k-(h+M))-(h+M)=k-(h+M) by omega]
  apply seg_false
  intro x hx hxB
  exact hS2 x (by omega) (by omega)

theorem first_prefix_word (f : Nat → Bool) (n h M k : Nat) (hk : h≤k) (hkM : k≤h+M)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true) :
    seg f n k=List.replicate h false++List.replicate (k-h) true := by
  rw [show k=h+(k-h) by omega,seg_add,seg_false f n h hS]
  rw [show h+(k-h)-h=k-h by omega]
  congr 1
  apply seg_A
  intro x hx hxK
  have ha:=hA (x-(n+h)) (by omega)
  rw [Nat.add_sub_cancel' hx] at ha
  exact ha

theorem S_A_S_has_pair (h M d : Nat) (hM : 1≤M) (hd : 1≤d) :
    List.replicate h false++List.replicate M true++List.replicate d false=
      (List.replicate h false++List.replicate (M-1) true)++[true,false]++List.replicate (d-1) false := by
  have ha : List.replicate M true=List.replicate (M-1) true++[true] := by
    change List.replicate M true=List.replicate (M-1) true++List.replicate 1 true
    rw [List.replicate_append_replicate,show M-1+1=M by omega]
  have hs : List.replicate d false=[false]++List.replicate (d-1) false := by
    change List.replicate d false=List.replicate 1 false++List.replicate (d-1) false
    rw [List.replicate_append_replicate,show 1+(d-1)=d by omega]
  rw [ha,hs]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

end Recaman.SingleASPrefixWord
