import Recaman.SignedSupplyGap

namespace Recaman.BoundedExcessSupply

open LeadingRunSupply SignedSupplyGap

/-! Multiplicity of P2 supplies in a fixed-width band above the leading-run bound. -/

/-- The signed quadratic gap forces a sharp quadratic bound on the earlier
run index. No minimum-lag or nesting assumption is used. -/
theorem band_arithmetic (R m k d d₂ : Int) (hR : 0 ≤ R) (hk : 1 ≤ k)
    (hlo : 4*m-1 ≤ d) (hhi : d ≤ 4*m-1+4*R)
    (hlo₂ : 4*(m+k)-1 ≤ d₂) (hhi₂ : d₂ ≤ 4*(m+k)-1+4*R)
    (hgap : 4*k*(d-1) ≤ (d₂-d)*(d₂-d-4*k)) : m ≤ R*(R+1) := by
  let x := d₂-d-4*k
  have hxlo : -4*R ≤ x := by dsimp [x]; omega
  have hxhi : x ≤ 4*R := by dsimp [x]; omega
  have hsq := Int.mul_nonneg (show 0 ≤ 4*R-x by omega)
    (show 0 ≤ 4*R+x by omega)
  have hlin := Int.mul_nonneg (show 0 ≤ 4*k by omega)
    (show 0 ≤ 4*R-x by omega)
  have hlow := Int.mul_nonneg (show 0 ≤ 4*k by omega)
    (show 0 ≤ d-(4*m-1) by omega)
  have hRsq := Int.mul_nonneg hR hR
  have hscale := Int.mul_nonneg (show 0 ≤ k-1 by omega) hRsq
  have hbound : 4*k*(4*m-2) ≤ 16*k*(R*R+R) := by
    have eq₁ : (4*R-x)*(4*R+x) = 16*(R*R)-x*x := by grind
    have eq₂ : 4*k*(4*R-x) = 16*(k*R)-4*k*x := by grind
    have eq₃ : 4*k*(d-(4*m-1)) = 4*k*(d-1)-4*k*(4*m-2) := by grind
    have eq₄ : (k-1)*(R*R) = k*(R*R)-R*R := by grind
    have eq₅ : (d₂-d)*(d₂-d-4*k) = x*x+4*k*x := by dsimp [x]; grind
    have eq₆ : 16*k*(R*R+R) = 16*(k*(R*R))+16*(k*R) := by grind
    omega
  by_cases hm : m ≤ R*(R+1)
  · exact hm
  · have hcontra := Int.mul_nonneg (show 0 ≤ 16*k by omega)
      (show 0 ≤ m-(R*R+R+1) by grind)
    have heq : 16*k*(m-(R*R+R+1)) =
        4*k*(4*m-2)-16*k*(R*R+R)-8*k := by grind
    omega

theorem stream_bounded_excess_multiplicity (e : Int → Bool) (t : Int)
    (R m k d d₂ : Nat) (hk : 1 ≤ k)
    (ha : ∀ i, i < k → e (t+i) = true)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+k) d₂)
    (hlo : 4*(m : Int)-1 ≤ d) (hhi : (d : Int) ≤ 4*m-1+4*R)
    (hlo₂ : 4*((m : Int)+k)-1 ≤ d₂) (hhi₂ : (d₂ : Int) ≤ 4*(m+k)-1+4*R) :
    m ≤ R*(R+1) := by
  have hg := stream_signed_supply_gap e t d d₂ k ha hold hnew
  have hb := band_arithmetic R m k d d₂ (by omega) (by omega) hlo hhi hlo₂ hhi₂ hg
  exact_mod_cast hb


def boundaryTail (R : Nat) : List Bool :=
  List.replicate (2*R+1) false ++ [true,false] ++ List.replicate (2*R) true

def boundaryNew (R : Nat) : List Bool :=
  [true] ++ sharpFamily (R*(R+1)) ++ boundaryTail R

theorem boundaryTail_data (R : Nat) :
    (boundaryTail R).length = 4*R+3 ∧
    mass (boundaryTail R) = -1 ∧ moment (boundaryTail R) = 4*(R : Int)*(R+1)-2 := by
  have hc := mass_eq (boundaryTail R)
  have ht := twice_moment (boundaryTail R)
  have ha := positions_replicate_A (2*R)
  have ho : ones (boundaryTail R) = 2*(R : Int)+1 := by
    simp [boundaryTail, ones_append, ones]
    omega
  have hp : 2*positions (boundaryTail R) = 12*(R : Int)*R+18*R+4 := by
    simp only [boundaryTail, positions_append, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil, Int.natCast_add,
      Int.natCast_mul, positions_replicate_S,
      ones_replicate_A, positions, ones]
    simp only [Int.natCast_mul] at ha
    grind
  have hl : (boundaryTail R).length = 4*R+3 := by simp [boundaryTail]; omega
  refine ⟨hl, ?_, ?_⟩
  · rw [ho, hl] at hc
    omega
  · rw [hl] at ht
    simp only [Int.natCast_add, Int.natCast_mul] at ht
    grind

theorem boundaryNew_data (R : Nat) (hR : 2 ≤ R) :
    (boundaryNew R).length = 4*(R*(R+1))+4*R+3 ∧ P2 (boundaryNew R) := by
  have hm : 1 ≤ R*(R+1) := Nat.mul_pos (by omega) (by omega)
  have hb := boundaryTail_data R
  have hs := sharpFamily_p2 (R*(R+1)) hm
  have hl := sharpFamily_length (R*(R+1)) hm
  have heq : ((4*(R*(R+1))-1 : Nat) : Int) = 4*(R : Int)*(R+1)-1 := by
    have hh : 1 ≤ 4*(R*(R+1)) := by omega
    rw [Int.natCast_sub hh]
    simp [Int.natCast_mul, Int.natCast_add]
    grind
  constructor
  · simp only [boundaryNew, List.length_append, List.length_cons, List.length_nil,
      hl, hb.1]
    omega
  · unfold boundaryNew
    constructor
    · simp only [mass_append, hs.1, hb.2.1, mass_cons, mass_nil, ShortPeriodicSupply.sign]
      decide
    · simp only [moment_append, List.length_append, List.length_cons, List.length_nil,
        hs.1, hs.2, hb.2.1, hb.2.2, hl, Int.natCast_add,
        moment, mass_nil, ShortPeriodicSupply.sign, heq]
      grind


theorem boundaryNew_take_leading (R : Nat) (hR : 2 ≤ R) :
    (boundaryNew R).take (R*(R+1)+1) = List.replicate (R*(R+1)+1) true := by
  have hm : 1 ≤ R*(R+1) := Nat.mul_pos (by omega) (by omega)
  have hl := sharpFamily_length (R*(R+1)) hm
  change true :: (sharpFamily (R*(R+1)) ++ boundaryTail R).take (R*(R+1)) = _
  rw [List.take_append_of_le_length (by omega), sharpFamily_take_leading _ _ (by omega)]
  rfl

/-- The optimality witnesses really use minimum supply lags. -/
theorem boundaryNew_minimal (R d : Nat) (hR : 2 ≤ R)
    (hd : d < (boundaryNew R).length) : ¬ P2 ((boundaryNew R).take d) := by
  intro hp
  let m := R*(R+1)
  have hm : 3 ≤ m := by
    have h := Nat.mul_le_mul (show 2 ≤ R from hR) (show 3 ≤ R+1 by omega)
    dsimp [m]
    omega
  have hl := (boundaryNew_data R hR).1
  have hlead := boundaryNew_take_leading R hR
  change (boundaryNew R).take (m+1) = List.replicate (m+1) true at hlead
  by_cases hsmall : d ≤ m+1
  · have hh := congrArg (List.take d) hlead
    rw [List.take_take, Nat.min_eq_left hsmall] at hh
    rw [List.take_replicate, Nat.min_eq_left hsmall] at hh
    rw [hh] at hp
    exact not_p2_all_A d hp
  · have ht : ((boundaryNew R).take d).take (m+1) = List.replicate (m+1) true := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
      exact hlead
    have hb := leading_run_bound_of_take _ (m+1) (by omega) ht hp
    simp only [List.length_take] at hb
    have hdlow : 4*m+3 ≤ d := by omega
    have holdlen := sharpFamily_length m (by omega)
    have hsplit : (boundaryNew R).take d =
        List.replicate 1 true ++ sharpFamily m ++
          (boundaryTail R).take (d-1-(sharpFamily m).length) := by
      change (true :: (sharpFamily m ++ boundaryTail R)).take d = _
      have hdpos : d = (d-1)+1 := by omega
      rw [hdpos, List.take_succ_cons]
      simp only [List.take_append]
      rw [List.take_of_length_le (by omega)]
      have heq : d-1+1-1-(sharpFamily m).length = d-1-(sharpFamily m).length := by omega
      rw [heq]
      rfl
    rw [hsplit] at hp
    have hg := nested_supply_gap (sharpFamily m)
      ((boundaryTail R).take (d-1-(sharpFamily m).length)) 1
      (sharpFamily_p2 m (by omega)) hp
    have htail := (boundaryTail_data R).1
    have htake : ((boundaryTail R).take (d-1-(sharpFamily m).length)).length = d-4*m := by
      simp only [List.length_take]
      dsimp [m] at holdlen ⊢
      omega
    rw [htake, holdlen] at hg
    have holdcast : ((4*m-1 : Nat) : Int) = 4*(m : Int)-1 := by omega
    have htailcast : ((d-4*m : Nat) : Int) = (d : Int)-4*m := by omega
    rw [holdcast, htailcast] at hg
    simp only [Int.cast_ofNat_Int, Int.mul_one] at hg
    have hdhigh : (d : Int)-4*m ≤ 4*(R : Int)+2 := by
      change (boundaryNew R).length = 4*m+4*R+3 at hl
      omega
    have hprod := Int.mul_nonneg (show 0 ≤ 4*(R : Int)+2-((d : Int)-4*m) by omega)
      (show 0 ≤ 4*(R : Int)+((d : Int)-4*m) by omega)
    have hmcast : (m : Int) = (R : Int)*(R+1) := by simp [m]
    have heq :
        (4*(R : Int)+2-((d : Int)-4*m))*(4*R+((d : Int)-4*m)) =
        (4*R+3)*(4*R-1)-(1+((d : Int)-4*m))*(((d : Int)-4*m)-3) := by grind
    have hright : (4*(R : Int)+3)*(4*R-1) = 16*(m : Int)-8*R-3 := by grind
    have hleft : 4*(1 : Int)*(4*(m : Int)-1-1) = 16*(m : Int)-8 := by grind
    omega


/-- Two minimum supplies attain the boundary m=R(R+1), for every R≥2. -/
theorem bounded_excess_optimality_certificate (R : Nat) (hR : 2 ≤ R) :
    (sharpFamily (R*(R+1))).length = 4*(R*(R+1))-1 ∧
    (boundaryNew R).length = 4*(R*(R+1))+4*R+3 ∧
    P2 (sharpFamily (R*(R+1))) ∧ P2 (boundaryNew R) ∧
    (boundaryNew R).take (R*(R+1)+1) = List.replicate (R*(R+1)+1) true ∧
    (∀ d, d < (sharpFamily (R*(R+1))).length →
      ¬ P2 ((sharpFamily (R*(R+1))).take d)) ∧
    (∀ d, d < (boundaryNew R).length → ¬ P2 ((boundaryNew R).take d)) := by
  have hm : 3 ≤ R*(R+1) := by
    have h := Nat.mul_le_mul (show 2 ≤ R from hR) (show 3 ≤ R+1 by omega)
    omega
  have ho := sharpFamily_certificate (R*(R+1)) hm
  have hn := boundaryNew_data R hR
  exact ⟨ho.1, hn.1, ho.2.2.1, hn.2, boundaryNew_take_leading R hR,
    ho.2.2.2, fun d hd => boundaryNew_minimal R d hR hd⟩

end Recaman.BoundedExcessSupply
