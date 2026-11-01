namespace Recaman.LagElevenSupply

/-! # Lag-11 residual injection: finite kernel

Seventeen min-lag-11 windows, a U7-incompatible charge for each, and a
sign clash at distance `j-i` for every distinct pair. The periodic glue
from an arbitrary sign stream onto these windows is not claimed here.
-/

def isS (m : Nat) (i : Nat) : Bool := m.testBit (i - 1)

def maskOf (offs : List Nat) : Nat :=
  offs.foldl (fun acc i => acc ||| (1 <<< (i - 1))) 0

def p2At (m : Nat) (d : Nat) : Bool :=
  decide (
    ((List.range d).map fun i =>
      (if isS m (i + 1) then (-1 : Int) else 1)).sum = 1 ∧
    ((List.range d).map fun i =>
      ((i + 1 : Nat) : Int) * (if isS m (i + 1) then (-1 : Int) else 1)).sum = 0)

def minLag11 (m : Nat) : Bool :=
  p2At m 11 && !p2At m 3 && !p2At m 7

def types : List (List Nat) :=
  [[1,2,9,10,11],[1,3,8,10,11],[1,4,7,10,11],[1,4,8,9,11],[1,5,6,10,11],
   [1,5,7,9,11],[1,5,8,9,10],[2,3,7,10,11],[2,3,8,9,11],[2,4,6,10,11],
   [2,4,7,9,11],[2,4,8,9,10],[2,5,6,9,11],[2,6,7,8,10],[4,5,6,7,11],
   [4,5,6,8,10],[4,5,7,8,9]]

def charge : List Nat → Nat
  | [1,2,9,10,11] => 10
  | [1,3,8,10,11] => 3
  | [1,4,7,10,11] => 4
  | [1,4,8,9,11] => 4
  | [1,5,6,10,11] => 6
  | [1,5,7,9,11] => 7
  | [1,5,8,9,10] => 8
  | [2,3,7,10,11] => 10
  | [2,3,8,9,11] => 9
  | [2,4,6,10,11] => 4
  | [2,4,7,9,11] => 4
  | [2,4,8,9,10] => 4
  | [2,5,6,9,11] => 6
  | [2,6,7,8,10] => 7
  | [4,5,6,7,11] => 6
  | [4,5,6,8,10] => 6
  | [4,5,7,8,9] => 7
  | _ => 0

/-- Sign at offset `k` from t: 0 is the A at t; 1..11 the backward window. -/
def signOff (offs : List Nat) : Nat → Int
  | 0 => 1
  | k + 1 => if k + 1 ≤ 11 then (if offs.contains (k + 1) then -1 else 1) else 99

def contradicts (offs : List Nat) (off : Nat) (val : Int) : Bool :=
  decide (off ≤ 11 ∧ signOff offs off ≠ val)

def lag3Contradicts (offs : List Nat) (i : Nat) : Bool :=
  (decide (3 ≤ i) && contradicts offs (i - 3) 1) ||
  (decide (2 ≤ i) && contradicts offs (i - 2) 1) ||
  (decide (1 ≤ i) && contradicts offs (i - 1) 1) ||
  contradicts offs i (-1)

def lag7h1Contradicts (offs : List Nat) (i : Nat) : Bool :=
  (List.range 8).any fun k =>
    let off := (i : Int) - 7 + k
    let val : Int := if k == 0 then 1 else if k == 1 || k == 6 || k == 7 then -1 else 1
    decide (0 ≤ off ∧ off ≤ 11) && contradicts offs off.toNat val

def lag7h2Contradicts (offs : List Nat) (i : Nat) : Bool :=
  (List.range 8).any fun k =>
    let off := (i : Int) - 5 + k
    let val : Int := if k == 0 then 1 else if k == 2 || k == 5 || k == 7 then -1 else 1
    decide (0 ≤ off ∧ off ≤ 11) && contradicts offs off.toNat val

def u7Blocked (offs : List Nat) (i : Nat) : Bool :=
  lag3Contradicts offs i && lag7h1Contradicts offs i && lag7h2Contradicts offs i

def clash (tau sig : List Nat) (i j : Nat) : Bool :=
  (List.range 12).any fun k =>
    let a := signOff tau k
    let bOff := (k : Int) - ((j : Int) - i)
    decide (0 ≤ bOff ∧ bOff ≤ 11 ∧ a ≠ signOff sig bOff.toNat)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem seventeen_types : types.length = 17 := by decide

theorem types_are_minLag11 :
    types.all (fun offs => minLag11 (maskOf offs)) = true := by
  decide

theorem charge_is_S :
    types.all (fun offs => offs.contains (charge offs)) = true := by
  decide

theorem charge_u7_blocked :
    types.all (fun offs => u7Blocked offs (charge offs)) = true := by
  decide

theorem pairwise_clash :
    (types.flatMap fun tau => types.map fun sig => (tau, sig)).all
      (fun p => (p.1 == p.2) || clash p.1 p.2 (charge p.1) (charge p.2)) = true := by
  decide

/-- Same-time overlap of the two length-11 windows at distance `j-i`.
This is the injectivity obstruction; `clash` is an offset-index slide that
happens to hold on this assignment but is not the geometric claim. -/
def timeClash (tau sig : List Nat) (i j : Nat) : Bool :=
  (List.range 12).any fun k =>
    let sOff := (j : Int) - i + k
    decide (0 ≤ sOff ∧ sOff ≤ 11 ∧ signOff tau k ≠ signOff sig sOff.toNat)

theorem pairwise_timeClash :
    (types.flatMap fun tau => types.map fun sig => (tau, sig)).all
      (fun p => (p.1 == p.2) || timeClash p.1 p.2 (charge p.1) (charge p.2)) = true := by
  decide

theorem types_complete :
    (List.range 2048).all (fun m =>
      !minLag11 m || types.any (fun offs => maskOf offs == m)) = true := by
  decide

theorem charge_bounds :
    types.all (fun offs => decide (3 ≤ charge offs ∧ charge offs ≤ 11)) = true := by
  decide

theorem types_distinct_masks :
    (types.flatMap fun tau => types.map fun sig => (tau, sig)).all
      (fun p => (p.1 == p.2) || decide (maskOf p.1 ≠ maskOf p.2)) = true := by
  decide

def typeOf (m : Nat) : List Nat :=
  match types.find? (fun offs => maskOf offs == m) with
  | some offs => offs
  | none => []

theorem types_contains_isS :
    types.all (fun offs =>
      (List.range 11).all (fun i => offs.contains (i + 1) == isS (maskOf offs) (i + 1))) = true := by
  decide

theorem pairwise_timeClash_mem (tau sig : List Nat)
    (ht : tau ∈ types) (hs : sig ∈ types)
    (hne : tau ≠ sig) :
    timeClash tau sig (charge tau) (charge sig) = true := by
  have hall := List.all_eq_true.mp pairwise_timeClash
  have hmem : (tau, sig) ∈ types.flatMap (fun a => types.map fun b => (a, b)) := by
    rw [List.mem_flatMap]
    refine ⟨tau, ht, ?_⟩
    rw [List.mem_map]
    exact ⟨sig, hs, rfl⟩
  have hp := hall (tau, sig) hmem
  cases hbeq : tau == sig
  · simpa [hbeq] using hp
  · have : tau = sig := eq_of_beq hbeq
    exact (hne this).elim

end Recaman.LagElevenSupply
