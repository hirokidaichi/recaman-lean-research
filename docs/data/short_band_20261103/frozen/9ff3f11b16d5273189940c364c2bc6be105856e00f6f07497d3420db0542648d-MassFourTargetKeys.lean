import Recaman.BlockOldRay
namespace Recaman.MassFourTargetKeys
open Recaman.BlockSuffixPositivity Recaman.RunSupplyKeys Recaman.BlockOldRay

theorem mass_four_keys (u : List Bool) (hu : BlockWord u) (hm : mass u=4) :
    runKey u= -2 ∨ runKey u=0 ∨ runKey u=2 ∨ runKey u=4 ∨ runKey u=6 := by
  have hmem:=block_mass_four hu hm
  have hchecked : (massFourWords.all fun v=>decide (runKey v= -2 ∨ runKey v=0 ∨ runKey v=2 ∨ runKey v=4 ∨ runKey v=6))=true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hchecked u hmem)
end Recaman.MassFourTargetKeys
