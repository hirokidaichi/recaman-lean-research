import Recaman.PrimitiveLayerActualFree
import Recaman.PrimitiveClockRadius

namespace Recaman.PrimitiveLayerFreeRadius

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The outermost layer's clock increment is paid by its own actual first-A
free count. The arbitrary old BlockWord and unchanged mixed future are retained;
this cannot be iterated by resetting an inner prefix to BlockWord. -/
theorem outer_layer_free_square (f : Nat → Bool) (n h a b B i j : Nat)
    (w u : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (hb : 1≤b)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ r, r<a → f (n+h+r)=true)
    (hfull : seg f 0 B=w++List.replicate h false++List.replicate a true++List.replicate b false++u)
    (hlast : ∀ r, r≤j → f (B+r)=true)
    (hkey : runKey u= -2)
    (hnewkey : runKey (List.replicate a true++(List.replicate b false++u))= -2)
    (hm : mass u+(i : Int)=1)
    (hnewmass : mass (List.replicate a true++(List.replicate b false++u))+(j : Int)=1) :
    8*(i : Int)≤((cN (fun x=>f x=true ∧ ¬EndN f 0 x) (n+h) a : Int)+2)^2 ∧
      EndN f 0 (B+i) ∧ EndN f 0 (B+j) := by
  obtain ⟨hij,hcharge,hendi,hendj⟩:=Recaman.PrimitiveLayerActualFree.outer_layer_actual_free_charge
    f n h a b B i j w u hw hpre hb hS hA hfull hlast hkey hnewkey hm hnewmass
  have hsquare:=Recaman.PrimitiveClockRadius.layer_A_square u a b i j hb hkey hnewkey hm hnewmass
  have hfree:=single_A_run_free_budget f n h a w hw hpre hS hA
  have hs:=Recaman.ShortCounterFactorBounds.square_lower
    ((cN (fun x=>f x=true ∧ ¬EndN f 0 x) (n+h) a : Int)+2) (a : Int) (by omega) (by omega)
  exact ⟨by omega,hendi,hendj⟩

theorem outer_layer_global_free_radius (f : Nat → Bool) (n h a b B i j R : Nat)
    (w u : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (hb : 1≤b)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ r, r<a → f (n+h+r)=true)
    (hfull : seg f 0 B=w++List.replicate h false++List.replicate a true++List.replicate b false++u)
    (hlast : ∀ r, r≤j → f (B+r)=true)
    (hkey : runKey u= -2)
    (hnewkey : runKey (List.replicate a true++(List.replicate b false++u))= -2)
    (hm : mass u+(i : Int)=1)
    (hnewmass : mass (List.replicate a true++(List.replicate b false++u))+(j : Int)=1)
    (hB : n+h+a≤B)
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (B+j+1-n)<R) :
    8*(i : Int)≤((R : Int)+1)^2 ∧ EndN f 0 (B+i) ∧ EndN f 0 (B+j) := by
  obtain ⟨hsquare,hendi,hendj⟩:=outer_layer_free_square f n h a b B i j w u hw hpre hb
    hS hA hfull hlast hkey hnewkey hm hnewmass
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hsplit:=cN_add P n h a
  have hmono:=Recaman.TwoRunSupply.count_prefix_le P n (h+a) (B+j+1-n) (by omega)
  have hsmall : cN P (n+h) a+2≤R+1 := by omega
  have hs:=Recaman.ShortCounterFactorBounds.square_lower ((R : Int)+1)
    ((cN P (n+h) a : Int)+2) (by omega) (by omega)
  exact ⟨by omega,hendi,hendj⟩

end Recaman.PrimitiveLayerFreeRadius
