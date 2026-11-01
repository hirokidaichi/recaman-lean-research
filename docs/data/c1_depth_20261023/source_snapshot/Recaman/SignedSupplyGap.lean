import Recaman.LeadingRunSupply

namespace Recaman.SignedSupplyGap

open LeadingRunSupply

/-! Signed separation of P2 lags across consecutive A steps.
Both increasing and decreasing lags are allowed; no nesting is assumed.
-/

/-- A-position sums are smallest when all A signs come first. -/
theorem positions_lower (w : List Bool) :
    ones w * (ones w + 1) ≤ 2 * positions w := by
  induction w with
  | nil => simp [ones, positions]
  | cons b w ih =>
    have hb := ones_bounds w
    cases b <;> simp [ones, positions] <;> grind

theorem moment_lower_of_mass (w : List Bool) (k : Int) (hm : mass w = k) :
    -((w.length : Int)*w.length) + 2*w.length*k + k*k + 2*k ≤ 4*moment w := by
  have hp := positions_lower w
  have hc := mass_eq w
  have ht := twice_moment w
  have heq :
      4*moment w + (w.length : Int)*w.length - 2*w.length*k - k*k - 2*k =
      4*(2*positions w-ones w*(ones w+1)) := by grind
  omega

/-- Removing an old tail after inserting k A signs gives the same signed
quadratic bound as adding an older tail. -/
theorem removed_tail_gap (u v : List Bool) (k : Nat)
    (hold : P2 (u ++ v)) (hnew : P2 (List.replicate k true ++ u)) :
    4*(k : Int)*((u++v).length-1) ≤
      ((v.length : Int)-k)*(v.length+3*k) := by
  have hn := hnew.1
  simp only [mass_append, mass_replicate_A] at hn
  have ho := hold.1
  rw [mass_append] at ho
  have hv : mass v = k := by omega
  have ht := hnew.2
  simp only [moment_append, List.length_replicate] at ht
  have hk := twice_moment_replicate_A k
  have hu : 2*moment u = (k : Int)*(k-3) := by grind
  have hvo := hold.2
  rw [moment_append, hv] at hvo
  have hvm : 4*moment v = -4*(k : Int)*u.length-2*k*k+6*k := by grind
  have hl := moment_lower_of_mass v k hv
  have heq :
      4*moment v + (v.length : Int)*v.length - 2*v.length*k - (k : Int)*k - 2*k =
      ((v.length : Int)-k)*(v.length+3*k)-4*(k : Int)*((u++v).length-1) := by
    simp only [List.length_append, Int.natCast_add]
    grind
  omega

theorem past_in_A_run (e : Int → Bool) (t : Int) (k d : Nat) (hd : d ≤ k)
    (ha : ∀ i, i < k → e (t+i) = true) :
    past e (t+k) d = List.replicate d true := by
  apply List.ext_getElem
  · simp [past]
  · intro i hi hj
    have hid : i < d := by simpa using hj
    have he := ha (k-1-i) (by omega)
    have hpos : t+(k : Int)-((i : Int)+1) = t+(k-1-i : Nat) := by omega
    simpa [past, hpos] using he

/-- The universal quadratic gap. Delta is an integer, so it can be negative. -/
theorem stream_signed_supply_gap (e : Int → Bool) (t : Int) (d d₂ k : Nat)
    (ha : ∀ i, i < k → e (t+i) = true)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+k) d₂) :
    4*(k : Int)*((d : Int)-1) ≤
      ((d₂ : Int)-d)*((d₂ : Int)-d-4*k) := by
  have hklt : k < d₂ := by
    by_cases hle : d₂ ≤ k
    · have hn := (past_p2_iff e (t+k) d₂).mpr hnew
      rw [past_in_A_run e t k d₂ hle ha] at hn
      exact False.elim (not_p2_all_A d₂ hn)
    · omega
  by_cases hcontain : d+k ≤ d₂
  · let ell := d₂-d-k
    have hell : d₂ = k+(d+ell) := by dsimp [ell]; omega
    have hn := (past_p2_iff e (t+k) d₂).mpr hnew
    rw [hell, past_append, past_A_run e t k ha] at hn
    have htime : t+(k : Int)-k = t := by omega
    rw [htime, past_append, ← List.append_assoc] at hn
    have hg := nested_supply_gap (past e t d) (past e (t-d) ell) k
      ((past_p2_iff e t d).mpr hold) hn
    simp only [past, List.length_map, List.length_range] at hg
    have hd₂ : (d₂ : Int) = k+d+ell := by omega
    have heq : ((d₂ : Int)-d)*((d₂ : Int)-d-4*k) =
        ((k : Int)+ell)*((ell : Int)-3*k) := by grind
    rw [heq]
    exact hg
  · let ell := d₂-k
    let b := d-ell
    have hnewlen : d₂ = k+ell := by dsimp [ell]; omega
    have holdlen : d = ell+b := by dsimp [ell,b]; omega
    have hn := (past_p2_iff e (t+k) d₂).mpr hnew
    rw [hnewlen, past_append, past_A_run e t k ha] at hn
    have htime : t+(k : Int)-k = t := by omega
    rw [htime] at hn
    have ho := (past_p2_iff e t d).mpr hold
    rw [holdlen, past_append] at ho
    have hg := removed_tail_gap (past e t ell) (past e (t-ell) b) k ho hn
    simp only [List.length_append, past, List.length_map, List.length_range,
      Int.natCast_add] at hg
    have hd₂ : (d₂ : Int) = k+ell := by omega
    have hd : (d : Int) = ell+b := by omega
    have heq : ((d₂ : Int)-d)*((d₂ : Int)-d-4*k) =
        ((b : Int)-k)*(b+3*k) := by grind
    rw [heq, hd]
    exact hg

/-- A symmetric-looking square form, with the later lag on the right. -/
theorem stream_supply_square_gap (e : Int → Bool) (t : Int) (d d₂ k : Nat)
    (ha : ∀ i, i < k → e (t+i) = true)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+k) d₂) :
    4*(k : Int)*((d₂ : Int)-1) ≤ ((d₂ : Int)-d)*((d₂ : Int)-d) := by
  have h := stream_signed_supply_gap e t d d₂ k ha hold hnew
  have heq :
      ((d₂ : Int)-d)*((d₂ : Int)-d-4*k)-4*(k : Int)*((d : Int)-1) =
      ((d₂ : Int)-d)*((d₂ : Int)-d)-4*(k : Int)*((d₂ : Int)-1) := by grind
  omega

/-- No intermediate or equal lag is possible, but genuine lag drops remain allowed. -/
theorem stream_lag_dichotomy (e : Int → Bool) (t : Int) (d d₂ k : Nat) (hk : 1 ≤ k)
    (ha : ∀ i, i < k → e (t+i) = true)
    (hold : ShortPeriodicSupply.P2 e t d)
    (hnew : ShortPeriodicSupply.P2 e (t+k) d₂) : d₂ < d ∨ d+4*k < d₂ := by
  have hg := stream_signed_supply_gap e t d d₂ k ha hold hnew
  have hd := p2_length_ge_three (past e t d) ((past_p2_iff e t d).mpr hold)
  simp only [past, List.length_map, List.length_range] at hd
  have hpositive : 0 < 4*(k : Int)*((d : Int)-1) :=
    Int.mul_pos (by omega) (by omega)
  by_cases hlt : d₂ < d
  · exact Or.inl hlt
  · right
    by_cases hgt : d+4*k < d₂
    · exact hgt
    · have hn := Int.mul_nonneg
        (show 0 ≤ (d₂ : Int)-d by omega)
        (show 0 ≤ 4*(k : Int)-((d₂ : Int)-d) by omega)
      have heq : ((d₂ : Int)-d)*(4*(k : Int)-((d₂ : Int)-d)) =
          -(((d₂ : Int)-d)*((d₂ : Int)-d-4*k)) := by grind
      omega

def equalityOld : List Bool := [true,false,true,true,false,true,false]
def equalityNew : List Bool :=
  [true,true] ++ equalityOld ++ List.replicate 6 false ++ List.replicate 4 true

/-- The factor 4 in the square gap cannot be increased, even for minimal supplies. -/
theorem square_gap_equality_certificate :
    equalityOld.length = 7 ∧ equalityNew.length = 19 ∧
    P2 equalityOld ∧ P2 equalityNew ∧
    (∀ d : Fin 7, ¬ P2 (equalityOld.take d.val)) ∧
    (∀ d : Fin 19, ¬ P2 (equalityNew.take d.val)) ∧
    (19-7 : Int)*(19-7) = 4*2*(19-1) := by
  unfold P2 mass
  decide

end Recaman.SignedSupplyGap
