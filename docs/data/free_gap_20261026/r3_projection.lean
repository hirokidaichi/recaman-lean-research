import Recaman.BlockOldRay
open Recaman.ThreeNonsuppliedData
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
example : (List.range rows.size).all (fun i =>
 decide ((stateAt rows i).additions≤2*(stateAt rows i).nonsupplied+1))=true := by decide
