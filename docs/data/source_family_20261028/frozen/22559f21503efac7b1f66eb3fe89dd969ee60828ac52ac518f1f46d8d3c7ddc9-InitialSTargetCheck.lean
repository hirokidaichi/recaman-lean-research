import Recaman.InitialSTargetBounds

namespace Recaman.InitialSTargetCheck

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.TwoRunSupply Recaman.RunSupplyBudget Recaman.BlockOldRay
open Recaman.ThreeRunSupplyBudget Recaman.InitialSTargetBounds Recaman.SourceFamilyFreeCount
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

def rayBoolCount (w : List Bool) (K : Nat) : Nat :=
  ((List.range K).filter (fun i => Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true))).length

theorem cN_bool_filter (g : Nat → Bool) : ∀ K : Nat,
    cN (fun i => g i=true) 0 K=((List.range K).filter g).length
  | 0 => rfl
  | K+1 => by
    have ih := cN_bool_filter g K
    cases hg : g K
    · rw [cN_succ_neg (fun i => g i=true) 0 K (by simpa using hg)]
      simp [List.range_succ,List.filter_append,hg,ih]
    · rw [cN_succ_pos (fun i => g i=true) 0 K (by simpa using hg)]
      simp [List.range_succ,List.filter_append,hg,ih]

theorem rayCount_eq_boolCount (w : List Bool) (K : Nat) : rayCount w K=rayBoolCount w K := by
  exact cN_bool_filter (fun i => Recaman.ThreeNonsuppliedData.localSupply (w++List.replicate i true)) K

def secondBoolCount (H M m L : Nat) : Nat :=
  rayBoolCount (List.replicate H false++List.replicate M true++List.replicate m false) L

def thirdBoolCount (H M m L s T : Nat) : Nat :=
  rayBoolCount (List.replicate H false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false) T

def firstFreeFloor (M : Nat) : Nat := M-min 2 (M-2)

def countFloor (H M m L s T : Nat) : Nat :=
  firstFreeFloor M+(L-(1+secondBoolCount H M m L))+(T-(1+thirdBoolCount H M m L s T))

def coreValid (R K M m s : Nat) : Bool :=
  let A := K+R
  let P := (K*K-R*R)/2
  let E := P-M*(m+s)
  let L := E/s
  decide (1≤M ∧ 1≤m ∧ 1≤s ∧ m+s<K ∧ M*(m+s)<P ∧ E%s=0 ∧ 1≤L ∧ M+L<A)

def checkCore (R K M m s : Nat) : Bool :=
  if coreValid R K M m s then
    let A := K+R
    let P := (K*K-R*R)/2
    let L := (P-M*(m+s))/s
    let T := A-M-L
    decide (R≤countFloor (A-2) M m L s T)
  else true

def criticalPairs : List (Nat × Nat) := [(5,7),(5,9),(6,8),(7,9)]

def checkPair (R K : Nat) : Bool :=
  (List.range (K+R)).all (fun M => (List.range K).all (fun m =>
    (List.range K).all (fun s => checkCore R K M m s)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem critical_checked : criticalPairs.all (fun p => checkPair p.1 p.2)=true := by decide

end Recaman.InitialSTargetCheck
