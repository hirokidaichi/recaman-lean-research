import Recaman.LeadingRunSupply

namespace Recaman.BoundedExcessReservoir

open LeadingRunSupply

/-! A middle block with few A signs for supplies of bounded excess.
The conclusion is a count, not a fixed S position or a contiguous S block. -/

theorem split_position_deficit (u v : List Bool) :
    2*ones u*((v.length : Int)-ones v) ≤
      ones (u++v)*(2*((u++v).length : Int)-ones (u++v)+1)-2*positions (u++v) := by
  have hu := positions_upper u
  have hv := positions_upper v
  rw [ones_append, positions_append]
  simp only [List.length_append, Int.natCast_add]
  have heq :
      (ones u+ones v)*(2*((u.length : Int)+v.length)-(ones u+ones v)+1) -
        2*(positions u+positions v+(u.length : Int)*ones v) -
        2*ones u*((v.length : Int)-ones v) =
      (ones u*(2*(u.length : Int)-ones u+1)-2*positions u)+
      (ones v*(2*(v.length : Int)-ones v+1)-2*positions v) := by grind
  omega

theorem reservoir_arithmetic (m s b : Int) (hm : 0 ≤ m) (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hdef : 2*b*(m+2*s+b) ≤ 2*m*(2*s+1)+4*s*s) : b ≤ 2*s := by
  by_cases hle : b ≤ 2*s
  · exact hle
  · have hgap : 0 ≤ b-(2*s+1) := by omega
    have h₁ := Int.mul_nonneg hgap (show 0 ≤ m+4*s+1 by omega)
    have h₂ := Int.mul_nonneg hb hgap
    have h₃ := Int.mul_nonneg hs (show 0 ≤ s+1 by omega)
    have heq : 2*b*(m+2*s+b) - (2*m*(2*s+1)+4*s*s) =
        2*((b-(2*s+1))*(m+4*s+1)) + 2*(b*(b-(2*s+1))) +
        12*(s*(s+1))+2 := by grind
    omega

/-- An exact-excess word split isolates the middle block of length m-1. -/
theorem middle_block_bound (m : Nat) (s : Int) (u v : List Bool)
    (hm : 3 ≤ m) (hs : 0 ≤ s)
    (hu : u.length = m-1) (hv : (v.length : Int) = 2*m+4*s)
    (hp : P2 (List.replicate m true ++ (u++v))) : ones u ≤ 2*s := by
  have hc := mass_eq (List.replicate m true ++ (u++v))
  have ht := twice_moment (List.replicate m true ++ (u++v))
  have ha := positions_replicate_A m
  have hlen : ((List.replicate m true ++ (u++v)).length : Int) = 4*m-1+4*s := by
    simp only [List.length_append, List.length_replicate, Int.natCast_add]
    omega
  have hmcast : ((m-1 : Nat) : Int) = (m : Int)-1 := by omega
  have hones : ones (u++v) = (m : Int)+2*s := by
    rw [ones_append, ones_replicate_A, hlen, hp.1] at hc
    omega
  have htailLen : ((u++v).length : Int) = 3*m-1+4*s := by
    simp only [List.length_append, Int.natCast_add]
    omega
  have hdef : ones (u++v)*(2*((u++v).length : Int)-ones (u++v)+1)-
      2*positions (u++v) = 2*(m : Int)*(2*s+1)+4*s*s := by
    rw [hp.2, hlen, positions_append, List.length_replicate, hones] at ht
    rw [htailLen, hones]
    grind
  have hd := split_position_deficit u v
  have honesV : ones v = (m : Int)+2*s-ones u := by rw [ones_append] at hones; omega
  rw [hdef, hv, honesV] at hd
  have heq : 2*ones u*(2*(m : Int)+4*s-((m : Int)+2*s-ones u)) =
      2*ones u*((m : Int)+2*s+ones u) := by grind
  rw [heq] at hd
  exact reservoir_arithmetic m s (ones u) (by omega) hs (ones_bounds u).1 hd


/-- At most 2R A signs in offsets m+1 through 2m-1, for any P2 lag
within 4R of the sharp leading-run lower bound. -/
theorem bounded_excess_middle_As (w : List Bool) (m R : Nat) (hm : 3 ≤ m)
    (hlead : w.take m = List.replicate m true) (hp : P2 w)
    (hupper : (w.length : Int) ≤ 4*m-1+4*R) :
    ones ((w.drop m).take (m-1)) ≤ 2*(R : Int) := by
  have hlow := leading_run_bound_of_take w m hm hlead hp
  have hc := p2_count_identities w hp
  let s : Int := ones w / 2 - m
  have ha : ones w = 2*(ones w/2) := by omega
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hsR : s ≤ R := by dsimp [s]; omega
  have hlen : (w.length : Int) = 4*m-1+4*s := by dsimp [s]; omega
  let u := (w.drop m).take (m-1)
  let v := (w.drop m).drop (m-1)
  have hu : u.length = m-1 := by
    simp only [u, List.length_take, List.length_drop]
    omega
  have hv : (v.length : Int) = 2*m+4*s := by
    simp only [v, List.length_drop]
    omega
  have hsplit : w = List.replicate m true ++ (u++v) := by
    dsimp [u,v]
    rw [List.take_append_drop, ← hlead, List.take_append_drop]
  have hbound := middle_block_bound m s u v hm hs hu hv (by rw [← hsplit]; exact hp)
  dsimp [u] at hbound
  omega


/-- Stream form of the reservoir bound; no upper bound on the lag itself. -/
theorem stream_middle_As (e : Int → Bool) (t : Int) (d m R : Nat) (hm : 3 ≤ m)
    (ha : ∀ i, i < m → e (t-((i+1 : Nat) : Int)) = true)
    (hp : ShortPeriodicSupply.P2 e t d) (hupper : (d : Int) ≤ 4*m-1+4*R) :
    ones (past e (t-m) (m-1)) ≤ 2*(R : Int) := by
  have hpw := (past_p2_iff e t d).mpr hp
  have hmd : m ≤ d := by
    by_cases hh : m ≤ d
    · exact hh
    · have hall : past e t d = List.replicate d true := by
        apply List.ext_getElem
        · simp [past]
        · intro i hi hj
          have hid : i < d := by simpa using hj
          simpa [past] using ha i (by omega)
      rw [hall] at hpw
      exact False.elim (not_p2_all_A d hpw)
  have hlead : (past e t d).take m = List.replicate m true := by
    apply take_leading _ _ (by simp [past]; omega)
    intro i hi
    simpa [past] using ha i hi
  have hlow := leading_run_bound_of_take (past e t d) m hm hlead hpw
  simp only [past, List.length_map, List.length_range] at hlow
  have hbound := bounded_excess_middle_As (past e t d) m R hm hlead hpw
    (by simpa [past] using hupper)
  have hd : d = m+((m-1)+(d-m-(m-1))) := by omega
  rw [hd, past_append, past_append] at hbound
  rw [List.drop_left' (by simp [past])] at hbound
  rw [List.take_append_of_le_length (by simp [past])] at hbound
  have htake : (past e (t-m) (m-1)).take (m-1) = past e (t-m) (m-1) :=
    List.take_of_length_le (by simp [past])
  rwa [htake] at hbound


def failedFixedChargeFamily (m : Nat) : List Bool :=
  List.replicate m true ++ [false,true] ++ List.replicate (m-2) false ++
    [true] ++ List.replicate (m+2) false ++ List.replicate m true

/-- Even excess four permits A at the old fixed charge offset, at arbitrarily
long leading runs. A density bound cannot be replaced by that fixed sign. -/
theorem fixed_charge_failure (m : Nat) (hm : 3 ≤ m) :
    (failedFixedChargeFamily m).length = 4*m+3 ∧
    (failedFixedChargeFamily m).take m = List.replicate m true ∧
    P2 (failedFixedChargeFamily m) ∧
    (failedFixedChargeFamily m)[m+1]? = some true := by
  have hmcast : ((m-2 : Nat) : Int) = (m : Int)-2 := by omega
  have ha := positions_replicate_A m
  have hc : ones (failedFixedChargeFamily m) = 2*(m : Int)+2 := by
    simp [failedFixedChargeFamily, ones_append, ones]
    omega
  have hl : (failedFixedChargeFamily m).length = 4*m+3 := by
    simp [failedFixedChargeFamily]
    omega
  have hpos : positions (failedFixedChargeFamily m) = (4*(m : Int)+3)*(m+1) := by
    simp only [failedFixedChargeFamily, positions_append,
      positions_replicate_S, ones_replicate_S, ones_replicate_A, positions, ones,
      List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      Int.natCast_add, hmcast]
    grind
  refine ⟨hl, ?_, ?_, ?_⟩
  · simp only [failedFixedChargeFamily, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    simp
  · have hmass := mass_eq (failedFixedChargeFamily m)
    have hmoment := twice_moment (failedFixedChargeFamily m)
    rw [hc, hl] at hmass
    rw [hpos, hl] at hmoment
    simp only [Int.natCast_add, Int.natCast_mul, Int.cast_ofNat_Int] at hmoment
    exact ⟨by omega, by grind⟩
  · simp [failedFixedChargeFamily, List.append_assoc]


/-- The bound is attained already at R=1, m=6. -/
theorem middle_As_bound_attained_certificate :
    let w := List.replicate 6 true ++ List.replicate 3 false ++
      List.replicate 2 true ++ List.replicate 10 false ++ List.replicate 6 true
    w.length = 27 ∧ P2 w ∧ w.take 6 = List.replicate 6 true ∧
      ones ((w.drop 6).take 5) = 2 := by
  unfold P2 mass
  decide

end Recaman.BoundedExcessReservoir
