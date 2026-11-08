import Recaman.MixedPrefixClockSquare

namespace Recaman.SevenPrefixSourceShape

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Complete 64-word certificate after the actual source has supplied
length seven, a first S, and exactly three A signs. -/
private theorem certificate : ∀ a b c d e g : Bool,
    ones [false,a,b,c,d,e,g]=3 → 0<runKey [false,a,b,c,d,e,g] →
      [false,a,b,c,d,e,g]=[false,true,true,true,false,false,false] := by decide

theorem seven_positive_key_shape (p : List Bool) (hlen : p.length=7)
    (hfirst : p.head?=some false) (hones : ones p=3) (hkey : 0<runKey p) :
    p=[false,true,true,true,false,false,false] := by
  cases p with
  | nil => simp at hlen
  | cons a0 p =>
    cases p with
    | nil => simp at hlen
    | cons a1 p =>
      cases p with
      | nil => simp at hlen
      | cons a2 p =>
        cases p with
        | nil => simp at hlen
        | cons a3 p =>
          cases p with
          | nil => simp at hlen
          | cons a4 p =>
            cases p with
            | nil => simp at hlen
            | cons a5 p =>
              cases p with
              | nil => simp at hlen
              | cons a6 p =>
                have hp : p=[] := by
                  apply List.eq_nil_of_length_eq_zero
                  simp only [List.length_cons] at hlen
                  omega
                subst p
                have ha0 : a0=false := by simpa using hfirst
                subst a0
                exact certificate a1 a2 a3 a4 a5 a6 hones hkey

end Recaman.SevenPrefixSourceShape
