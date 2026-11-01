import Recaman.ShortTightDonorAvoidance

open Recaman.LeadingRunSupply
open Recaman.TwoSSTightDisjoint

def prefixAuditStream (t : Int) : Bool :=
  ([false, true, true, true] : List Bool).getD ((t % 4).toNat) false

#eval past prefixAuditStream 3 3
#eval past prefixAuditStream 3 4
#eval decide (P2 (past prefixAuditStream 3 3))
#eval decide (P2 (past prefixAuditStream 3 4))
#eval neighborhood prefixAuditStream 4 [3] (fun _ => 3)
#eval neighborhood prefixAuditStream 4 [3] (fun _ => 4)
#eval neighborhood prefixAuditStream 4 [3] (fun _ => 0)
