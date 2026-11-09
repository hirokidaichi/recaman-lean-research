import Recaman.FreeTwoTightTail

namespace Recaman.ElevenSignRankPrefix

open Recaman.LeadingRunSupply Recaman.RunSupplyKeys

/-- A complete certificate for the eleven signs between the two sources.
The three prefix ceilings constrain the third, fourth and fifth addition ranks. -/
private theorem certificate : ∀ a b c d e g h : Bool,
    let p := [false,a,b,c,d,e,g,h,true,false,false]
    ones p=5 → runKey p=4 → ones (p.take 4)≤2 → ones (p.take 6)≤3 →
      ones (p.take 8)≤4 → p.take 5=[false,true,true,false,true] := by decide

/-- The minimum chronological area at the rank-two band fixes the first
three additions. Only the intervening sign word is bounded. -/
theorem eleven_rank_prefix (p : List Bool) (hlen : p.length=11)
    (hfirst : p.head?=some false) (htail : p.drop 8=[true,false,false])
    (ha : ones p=5) (hk : runKey p=4)
    (h4 : ones (p.take 4)≤2) (h6 : ones (p.take 6)≤3) (h8 : ones (p.take 8)≤4) :
    p.take 5=[false,true,true,false,true] := by
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
                cases p with
                | nil => simp at hlen
                | cons a7 p =>
                  cases p with
                  | nil => simp at hlen
                  | cons a8 p =>
                    cases p with
                    | nil => simp at hlen
                    | cons a9 p =>
                      cases p with
                      | nil => simp at hlen
                      | cons a10 p =>
                        have hp : p=[] := by
                          apply List.eq_nil_of_length_eq_zero
                          simp only [List.length_cons] at hlen
                          omega
                        subst p
                        have h0 : a0=false := by simpa using hfirst
                        subst a0
                        change [a8,a9,a10]=[true,false,false] at htail
                        have ht : a8=true ∧ a9=false ∧ a10=false := by simpa using htail
                        obtain ⟨ha8,ha9,ha10⟩:=ht
                        subst a8
                        subst a9
                        subst a10
                        exact certificate a1 a2 a3 a4 a5 a6 a7 ha hk h4 h6 h8

end Recaman.ElevenSignRankPrefix
