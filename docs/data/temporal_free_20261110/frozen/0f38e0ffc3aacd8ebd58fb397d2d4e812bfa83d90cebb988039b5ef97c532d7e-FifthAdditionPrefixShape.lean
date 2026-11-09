import Recaman.RankThreeFifthWindow

namespace Recaman.FifthAdditionPrefixShape

open Recaman.LeadingRunSupply Recaman.RunSupplyKeys

private theorem eight_certificate : ∀ a b c d e g : Bool,
    let p := [false,a,b,c,d,e,g,true]
    ones p=5 → 2≤runKey p → ones (p.take 4)≤2 →
      p.take 6=[false,true,true,false,true,true] ∨
      p.take 8=[false,true,false,true,true,true,false,true] ∨
      p.take 7=[false,true,true,false,true,false,true] := by decide

/-- Complete check of the early word after both endpoint signs are known. -/
theorem eight_fifth_prefix (p : List Bool) (hlen : p.length=8)
    (hfirst : p.head?=some false) (hlast : p[7]?=some true)
    (ha : ones p=5) (hk : 2≤runKey p) (h4 : ones (p.take 4)≤2) :
    p.take 6=[false,true,true,false,true,true] ∨
      p.take 8=[false,true,false,true,true,true,false,true] ∨
      p.take 7=[false,true,true,false,true,false,true] := by
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
                  have hp : p=[] := by
                    apply List.eq_nil_of_length_eq_zero
                    simp only [List.length_cons] at hlen
                    omega
                  subst p
                  have hf : a0=false := by simpa using hfirst
                  have hl : a7=true := by simpa using hlast
                  subst a0
                  subst a7
                  exact eight_certificate a1 a2 a3 a4 a5 a6 ha hk h4

private theorem nine_certificate : ∀ a b c d e g h : Bool,
    let p := [false,a,b,c,d,e,g,h,true]
    ones p=5 → 8≤runKey p → ones (p.take 4)≤2 →
      p.take 6=[false,true,true,false,true,true] ∨
      p.take 8=[false,true,false,true,true,true,false,true] ∨
      p.take 7=[false,true,true,false,true,false,true] := by decide

/-- Complete check of the early word after both endpoint signs are known. -/
theorem nine_fifth_prefix (p : List Bool) (hlen : p.length=9)
    (hfirst : p.head?=some false) (hlast : p[8]?=some true)
    (ha : ones p=5) (hk : 8≤runKey p) (h4 : ones (p.take 4)≤2) :
    p.take 6=[false,true,true,false,true,true] ∨
      p.take 8=[false,true,false,true,true,true,false,true] ∨
      p.take 7=[false,true,true,false,true,false,true] := by
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
                    have hp : p=[] := by
                      apply List.eq_nil_of_length_eq_zero
                      simp only [List.length_cons] at hlen
                      omega
                    subst p
                    have hf : a0=false := by simpa using hfirst
                    have hl : a8=true := by simpa using hlast
                    subst a0
                    subst a8
                    exact nine_certificate a1 a2 a3 a4 a5 a6 a7 ha hk h4

end Recaman.FifthAdditionPrefixShape
