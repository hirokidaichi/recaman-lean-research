import Recaman.RunClockClassifier
namespace Recaman.S14R6LocalCertificate
open Recaman.RunSupplyBudget Recaman.BlockOldRay Recaman.RunClockClassifier

theorem third_1 : rayCount (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false++List.replicate 3 true++List.replicate 2 false) 7≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_2 : rayCount (List.replicate 11 false++List.replicate 4 true++List.replicate 1 false++List.replicate 4 true++List.replicate 2 false) 6≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_3 : rayCount (List.replicate 9 false++List.replicate 3 true++List.replicate 4 false++List.replicate 4 true++List.replicate 1 false) 7≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_4 : rayCount (List.replicate 9 false++List.replicate 3 true++List.replicate 4 false++List.replicate 5 true++List.replicate 1 false) 6≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_5 : rayCount (List.replicate 9 false++List.replicate 3 true++List.replicate 4 false++List.replicate 6 true++List.replicate 1 false) 5≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_6 : rayCount (List.replicate 11 false++List.replicate 6 true++List.replicate 2 false++List.replicate 1 true++List.replicate 1 false) 7≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_7 : rayCount (List.replicate 11 false++List.replicate 6 true++List.replicate 2 false++List.replicate 2 true++List.replicate 1 false) 6≤3 := by
  rw [rayCount_eq_boolCount]
  decide

theorem third_8 : rayCount (List.replicate 11 false++List.replicate 6 true++List.replicate 2 false++List.replicate 3 true++List.replicate 1 false) 5≤3 := by
  rw [rayCount_eq_boolCount]
  decide

end Recaman.S14R6LocalCertificate
