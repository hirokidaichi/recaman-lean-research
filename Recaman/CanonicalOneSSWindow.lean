import Recaman.CanonicalSSFreeSupply

namespace Recaman.CanonicalOneSSWindow

open LeadingRunSupply CanonicalSSFreeSupply

/-! Isolated kernel computation of the canonical sign window. Keeping the
certificate here avoids replaying it when editing its symbolic consequences. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_window_certificate : past canonicalSign 1352 15 =
    [false,true,false,true,true,true,true,false,false,true,false,true,false,true,false] := by
  decide

end Recaman.CanonicalOneSSWindow
