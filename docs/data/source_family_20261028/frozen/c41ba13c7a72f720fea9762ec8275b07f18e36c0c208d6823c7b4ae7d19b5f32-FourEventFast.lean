import Recaman.FourEventProof

namespace Recaman.FourEventFast

open Recaman.LeadingRunSupply
open Recaman.ShortPeriodicSupply (sign)
open Recaman.BlockSuffixPositivity
open Recaman.FourNonsuppliedData

theorem localSupply_cons (c : Bool) (w : List Bool) :
    Recaman.ThreeNonsuppliedData.localSupply (c::w)=
      (Recaman.ThreeNonsuppliedData.localSupply w ||
        decide (mass (c::w)=1 ∧ Recaman.ThreeNonsuppliedData.wordArea (c::w)=0)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq,localSupply_iff]
  constructor
  · rintro ⟨t,ht,hm,ha⟩
    cases t with
    | zero => exact Or.inr ⟨hm,ha⟩
    | succ t =>
      left
      exact ⟨t,by simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ ht,hm,ha⟩
  · rintro (⟨t,ht,hm,ha⟩|⟨hm,ha⟩)
    · exact ⟨t+1,by simpa only [List.length_cons] using Nat.succ_lt_succ ht,hm,ha⟩
    · exact ⟨0,by simp,hm,ha⟩

structure Scan where
  size : Nat
  totalMass : Int
  totalArea : Int
  found : Bool

def scan : List Bool → Scan
  | [] => ⟨0,0,0,false⟩
  | c::w =>
    let q := scan w
    let m := sign c+q.totalMass
    let a := sign c*((q.size : Int)+1)+q.totalArea
    ⟨q.size+1,m,a,q.found || decide (m=1 ∧ a=0)⟩

theorem scan_values (w : List Bool) :
    (scan w).size=w.length ∧ (scan w).totalMass=mass w ∧
      (scan w).totalArea=Recaman.ThreeNonsuppliedData.wordArea w ∧
      (scan w).found=Recaman.ThreeNonsuppliedData.localSupply w := by
  induction w with
  | nil => decide
  | cons c w ih =>
    obtain ⟨hl,hm,ha,hf⟩ := ih
    simp only [scan]
    rw [hl,hm,ha,hf]
    exact ⟨rfl,rfl,rfl,(localSupply_cons c w).symm⟩

def oldFrom (q : Scan) : Bool :=
  let r := 1-q.totalMass
  let B := -q.totalArea-(q.size : Int)*r
  decide (1≤r ∧ 1≤B ∧ r*(r+1)≤2*B+2 ∧
    4*B≤5*r*r-11*r+16 ∧ (r=1 → B=1))

theorem oldFrom_scan (w : List Bool) :
    oldFrom (scan w)=Recaman.ThreeNonsuppliedData.oldSignature w := by
  obtain ⟨hl,hm,ha,_⟩ := scan_values w
  simp only [oldFrom,Recaman.ThreeNonsuppliedData.oldSignature,hl,hm,ha]

def fastStepA (s : State) (e : Bool) : Option State :=
  let q := scan s.word
  let an := s.nonsupplied+(if e then 0 else 1)
  let admitted := if e then q.found || (decide (s.subtractions<19) && oldFrom q) else !q.found
  if admitted && decide (an≤4) &&
      decide (s.subtractions=19 ∨ 1≤(s.subtractions : Int)-(s.additions+1 : Nat)+an) then
    some ⟨if s.subtractions=19 then trim (s.word++[true]) else s.word++[true],
      s.additions+1,s.subtractions,an⟩ else none

theorem fastStepA_eq (s : State) (e : Bool) : fastStepA s e=stepA s e := by
  have hf := (scan_values s.word).2.2.2
  simp only [fastStepA,stepA,oldFrom_scan,hf]

def fastMacroA (s : State) (j : Nat) (e : Bool) : Option State := fastStepA (gap s j) e

def fastSuccessors (s : State) : List State :=
  (List.range 20).flatMap fun j => [fastMacroA s j false,fastMacroA s j true].filterMap id

theorem successors_eq_fast (s : State) :
    Recaman.FourEventProof.successors s=fastSuccessors s := by
  simp only [Recaman.FourEventProof.successors,fastSuccessors,fastMacroA,fastStepA_eq,macroA]

-- Boundary controls keep the full-window suffix and the original A11 edge.
example : (scan [false,true,true]).found=true := by decide
example : (scan [true,true]).found=false := by decide
example : (fastMacroA ⟨[],10,0,3⟩ 20 false).map (fun s => s.additions)=some 11 := by decide

end Recaman.FourEventFast
