import Recaman.LayeredPrimitiveSupply
import Recaman.InitialSeparatorTrim

namespace Recaman.InitialSPaddingPositive

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A finite chronological word, followed only by additions. -/
def finiteSign (w : List Bool) (i : Nat) : Bool :=
  if h:i<w.length then w[i] else true

theorem finiteSign_seg (w : List Bool) : seg (finiteSign w) 0 w.length=w := by
  apply List.ext_getElem
  · simp [seg]
  · intro i hi hw
    simp [seg,finiteSign,hw]

theorem finiteSign_after (w : List Bool) (i : Nat) : finiteSign w (w.length+i)=true := by
  simp [finiteSign,show ¬w.length+i<w.length from by omega]

/-- Enough initial S signs supply relative positivity for any realized
finite future, using EndN's actual endpoint sign. -/
theorem initial_S_positive (f : Nat → Bool) (h B : Nat)
    (hS : ∀ i, i<h → f i=false)
    (hA : cN (fun i=>f i=true) 0 B<h) :
    ∀ k, 0<k → k≤B → cN (EndN f 0) 0 k+1≤cN (fun i=>f i=false) 0 k := by
  intro k hk hkB
  have heA : cN (EndN f 0) 0 k≤cN (fun i=>f i=true) 0 k := by
    apply cN_mono
    intro i hi hik he
    exact he.1
  by_cases hkh : k≤h
  · have hw : seg f 0 k=List.replicate k false :=
      seg_false f 0 k (by intro i _ hik; exact hS i (by omega))
    have hc:=cntF_seg f 0 k
    have ha:=ones_seg_eq_count f 0 k
    rw [hw,cntF_replicate_S] at hc
    rw [hw,ones_replicate_S] at ha
    omega
  · have hw : seg f 0 h=List.replicate h false :=
      seg_false f 0 h (by intro i _ hih; exact hS i (by omega))
    have hc:=cntF_seg f 0 h
    rw [hw,cntF_replicate_S] at hc
    have hsadd:=cN_add (fun i=>f i=false) 0 h (k-h)
    rw [show h+(k-h)=k by omega] at hsadd
    have haadd:=cN_add (fun i=>f i=true) 0 k (B-k)
    rw [show k+(B-k)=B by omega] at haadd
    omega

/-- Prefix padding never removes a local supplier at the same final ray. -/
theorem actual_ray_retains_suffix (f : Nat → Bool) (B T h : Nat) (w : List Bool)
    (hpre : seg f 0 B=List.replicate h false++w)
    (hA : ∀ i, i<T → f (B+i)=true) :
    rayCount w T≤cN (EndN f 0) B T := by
  rw [endable_A_run_count f B T _ hpre hA]
  unfold rayCount
  apply cN_mono
  intro i hi hiT he
  exact (ray_supply_append_iff (List.replicate h false) w i).mpr (Or.inr he)

end Recaman.InitialSPaddingPositive
