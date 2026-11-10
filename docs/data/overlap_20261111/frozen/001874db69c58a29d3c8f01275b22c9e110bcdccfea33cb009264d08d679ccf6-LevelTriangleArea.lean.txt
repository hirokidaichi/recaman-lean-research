import Recaman.BlockSuffixPositivity

namespace Recaman.LevelTriangleArea

open Recaman.SingleWindowEquality

def aboveTriangle (r h : Int) : Int :=
  max 0 (h-r) * (max 0 (h-r)+1)

def belowTriangle (r h : Int) : Int :=
  max 0 (r-h) * (max 0 (r-h)+1)

def lowAdditionWeight (f : Nat → Bool) (r : Int) (t : Nat) : Int :=
  if f t=true ∧ Fw f t<r then 2*(r-Fw f t)-1 else 0

def lowAdditionWeights (f : Nat → Bool) (s : Nat) (r : Int) : Nat → Int
  | 0 => 0
  | k+1 => lowAdditionWeights f s r k+lowAdditionWeight f r (s+k)

def areaFromLevel (f : Nat → Bool) (s : Nat) (r : Int) (k : Nat) : Int :=
  Ar f s k+(k : Int)*(Fw f s-r)

theorem area_from_level_succ (f : Nat → Bool) (s : Nat) (r : Int) (k : Nat) :
    areaFromLevel f s r (k+1)=areaFromLevel f s r k+Fw f (s+k+1)-r := by
  unfold areaFromLevel
  rw [Ar_succ,Int.natCast_add,Int.add_mul]
  have ho : ((1 : Nat) : Int)=1 := rfl
  rw [ho,Int.one_mul]
  omega

theorem low_weight_nonnegative (f : Nat → Bool) (r : Int) (t : Nat) :
    0≤lowAdditionWeight f r t := by
  unfold lowAdditionWeight
  by_cases h : f t=true ∧ Fw f t<r
  · rw [if_pos h]
    have := h.2
    omega
  · rw [if_neg h]
    omega

theorem low_weights_nonnegative (f : Nat → Bool) (s : Nat) (r : Int) :
    ∀ K, 0≤lowAdditionWeights f s r K
  | 0 => by simp [lowAdditionWeights]
  | K+1 => by
    have h0 := low_weights_nonnegative f s r K
    have h1 := low_weight_nonnegative f r (s+K)
    rw [lowAdditionWeights]
    omega

theorem low_weights_append (f : Nat → Bool) (s : Nat) (r : Int) (a : Nat) :
    ∀ b, lowAdditionWeights f s r (a+b)=
      lowAdditionWeights f s r a+lowAdditionWeights f (s+a) r b
  | 0 => by simp [lowAdditionWeights]
  | b+1 => by
    have hi := low_weights_append f s r a b
    rw [show a+(b+1)=a+b+1 by omega,lowAdditionWeights,lowAdditionWeights,hi,
      show s+(a+b)=s+a+b by omega]
    omega

private theorem one_step (f : Nat → Bool) (r : Int) (t : Nat) :
    let E := 2*(Fw f (t+1)-r)+belowTriangle r (Fw f (t+1))-
      belowTriangle r (Fw f t)+2*lowAdditionWeight f r t
    0≤E ∧ aboveTriangle r (Fw f (t+1))-aboveTriangle r (Fw f t)≤E := by
  dsimp only
  rcases fw_cases f t with ⟨hstep,hA⟩ | ⟨hstep,hS⟩
  · by_cases h : r≤Fw f t
    · have w0 : lowAdditionWeight f r t=0 := by
        simp [lowAdditionWeight,hA,show ¬Fw f t<r by omega]
      rw [w0,hstep]
      unfold aboveTriangle belowTriangle
      rw [Int.max_eq_left (show r-(Fw f t+1)≤0 by omega),
        Int.max_eq_left (show r-Fw f t≤0 by omega),
        Int.max_eq_right (show 0≤Fw f t+1-r by omega),
        Int.max_eq_right (show 0≤Fw f t-r by omega)]
      constructor <;> grind
    · have hw : lowAdditionWeight f r t=2*(r-Fw f t)-1 := by
        simp [lowAdditionWeight,hA,show Fw f t<r by omega]
      rw [hw,hstep]
      unfold aboveTriangle belowTriangle
      rw [Int.max_eq_right (show 0≤r-(Fw f t+1) by omega),
        Int.max_eq_right (show 0≤r-Fw f t by omega),
        Int.max_eq_left (show Fw f t+1-r≤0 by omega),
        Int.max_eq_left (show Fw f t-r≤0 by omega)]
      constructor <;> grind
  · have w0 : lowAdditionWeight f r t=0 := by simp [lowAdditionWeight,hS]
    rw [w0,hstep]
    unfold aboveTriangle belowTriangle
    by_cases h : Fw f t≤r
    · rw [Int.max_eq_right (show 0≤r-(Fw f t-1) by omega),
        Int.max_eq_right (show 0≤r-Fw f t by omega),
        Int.max_eq_left (show Fw f t-1-r≤0 by omega),
        Int.max_eq_left (show Fw f t-r≤0 by omega)]
      constructor <;> grind
    · rw [Int.max_eq_left (show r-(Fw f t-1)≤0 by omega),
        Int.max_eq_left (show r-Fw f t≤0 by omega),
        Int.max_eq_right (show 0≤Fw f t-1-r by omega),
        Int.max_eq_right (show 0≤Fw f t-r by omega)]
      constructor <;> grind

/-- Low additions with their exact weights pay the negative area.
After that correction, the positive area dominates the upper triangle
gained by the original walk on the same interval. -/
theorem signed_area_with_low_weights (f : Nat → Bool) (s : Nat) (r : Int) :
    ∀ K,
    let E := 2*areaFromLevel f s r K+belowTriangle r (Fw f (s+K))-
      belowTriangle r (Fw f s)+2*lowAdditionWeights f s r K
    0≤E ∧ aboveTriangle r (Fw f (s+K))-aboveTriangle r (Fw f s)≤E
  | 0 => by simp [areaFromLevel,Ar,lowAdditionWeights]
  | k+1 => by
    have hi := signed_area_with_low_weights f s r k
    have hs := one_step f r (s+k)
    dsimp only at hi hs ⊢
    rw [area_from_level_succ,lowAdditionWeights,show s+(k+1)=s+k+1 by omega]
    exact ⟨by omega,by omega⟩

end Recaman.LevelTriangleArea
