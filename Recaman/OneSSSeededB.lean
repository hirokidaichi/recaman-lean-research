import Recaman.FiniteSeedPeriodicSupply
import Recaman.OneSSMultiplicity

namespace Recaman.OneSSSeededB

open LeadingRunSupply OneSSGapAlgebra FiniteSeedPeriodicSupply OneSSMultiplicity

def seed : State := ⟨100,[100,64,76,86,83,80]⟩

theorem exact_values :
    (List.range 13).map (fun k => (SeededReplay.run 10 seed k).value) =
      [100,89,77,90,104,119,103,120,102,121,101,122,144] := by decide

theorem exact_signs :
    (List.range 12).map (fun k => absoluteSign 10 seed ((10+k : Nat) : Int)) =
      [false,false,true,true,true,false,true,false,true,false,true,true] := by decide

theorem family_B_window :
    past (absoluteSign 10 seed) 21 11=gapWord 1 (familyGaps 5 3 4 2) := by decide

theorem current_A_and_minimum :
    absoluteSign 10 seed 21=true ∧ ShortPeriodicSupply.P2 (absoluteSign 10 seed) 21 11 ∧
    ∀ d : Fin 11, ¬ ShortPeriodicSupply.P2 (absoluteSign 10 seed) 21 d.val := by
  unfold ShortPeriodicSupply.P2
  decide

theorem family_B_noSAAS : SSFreeSupply.NoSAAS (past (absoluteSign 10 seed) 21 11) := by
  have hz : saasCount (past (absoluteSign 10 seed) 21 11)=0 := by decide
  intro u v heq
  have h := saas_occurrence_positive u v
  rw [← heq,hz] at h
  omega

theorem family_B_single_SS : ssCount (past (absoluteSign 10 seed) 21 11)=1 := by decide

end Recaman.OneSSSeededB
