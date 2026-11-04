import Recaman.OldInitialKeyGap
import Recaman.UnitOneInitialSource

namespace Recaman.LowOldInitialSources

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.UnitTargetSASProfile

/-- Positive middle/third S runs and source-specific mass supply the
structural bound, so no S/area cutoff is assumed. No target is required. -/
theorem low_old_initial_excluded (u : List Bool) (h M m L s U v k : Nat)
    (hu : BlockWord u) (hD : mass u=2 ∨ mass u=3)
    (hm : 1≤m) (hs : 1≤s) (hzero : M+L+U=h+m+s)
    (hold : runKey (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false))= -2) :
    ¬sourceAt false h (List.replicate M true++List.replicate m false++List.replicate L true++
      List.replicate s false++List.replicate U true++List.replicate v false) k := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let x:=List.replicate q false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hrep : List.replicate h false=List.replicate d false++List.replicate q false := by
    rw [List.replicate_append_replicate,show d+q=h by dsimp [d]; omega]
  have hmass : mass x+(k : Int)=1 := by simpa only [x,List.append_assoc] using hbal
  have hdk : d+k=v+1 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A] at hmass
    dsimp [d]
    omega
  have hcount : cntF x=q+m+s+v := by
    simp only [x,cntF_append,cntF_replicate_S,cntF_A,Nat.add_zero,Nat.zero_add]
  have hgeo : 2*d+2≤d+cntF x := by rw [hcount]; omega
  have hlocal : runKey x= -2 := by simpa only [x,List.append_assoc] using hkey
  have hshared : runKey (u++(List.replicate d false++x))= -2 := by
    rw [hrep] at hold
    simpa only [x,List.append_assoc] using hold
  exact Recaman.OldInitialKeyGap.low_mass_initial_excluded u x d hu hD hgeo hshared hlocal

/-- The new source exclusion improves the full local last-ray budget
without using a target, a global area band, or bounded history. -/
theorem low_old_local_five (u : List Bool) (h M m L s U v K : Nat)
    (hu : BlockWord u) (hD : mass u=2 ∨ mass u=3)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hzero : M+L+U=h+m+s)
    (hold : runKey (u++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false))= -2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤5 := by
  apply Recaman.UnitOneInitialSource.fourth_local_five h M m L s U v K hv
  intro i
  exact low_old_initial_excluded u h M m L s U v i hu hD hm hs hzero hold

end Recaman.LowOldInitialSources
