import Recaman.CanonicalLowSSBoundary

namespace Recaman.TwoSSLeadingSibling

open LeadingRunSupply CanonicalSSFreeSupply CanonicalLowSSBoundary
open OneSSMultiplicity

/-! A minimum P2 window longer than AAS cannot start AAS. If a backward
word begins with at least three A's then S, dropping the newest a-2
letters leaves AAS. On a stream that is a strictly earlier current-A
source in the same run. Canonical sign 114 is an instance, not an
exception: leading run 3, sibling 113. This is why newest-S collides
with the E-128 charge of that sibling. -/

theorem p2_AAS : P2 [true,true,false] := by
  unfold P2
  decide

theorem past_length (e : Int → Bool) (t : Int) (d : Nat) :
    (past e t d).length = d := by
  simp [past]

theorem take_left_past (e : Int → Bool) (t : Int) (d : Nat) (hd : 3 ≤ d) :
    (past e t d).take 3 = past e t 3 := by
  have hsplit := past_append e t 3 (d-3)
  have hd' : 3+(d-3)=d := by omega
  have hw : past e t d = past e t 3 ++ past e (t-3) (d-3) := by
    simpa [hd'] using hsplit
  have hlen : (past e t 3).length = 3 := past_length e t 3
  rw [hw,← hlen]
  exact List.take_left

/-- A proper prefix AAS would already be P2, so a longer minimum window
cannot start that way. Minimum SS=2 windows have length at least 11. -/
theorem min_P2_not_prefix_AAS (w : List Bool)
    (hmin : ∀ f : Nat, f < w.length → ¬ P2 (w.take f))
    (hlen : 3 < w.length) :
    w.take 3 ≠ [true,true,false] := by
  intro h
  have hP3 : P2 (w.take 3) := by
    rw [h]
    exact p2_AAS
  exact hmin 3 (by omega) hP3

theorem stream_min_not_prefix_AAS (e : Int → Bool) (t : Int) (d : Nat)
    (hmin : ∀ f : Nat, f < d → ¬ ShortPeriodicSupply.P2 e t f)
    (hlen : 3 < d) :
    past e t 3 ≠ [true,true,false] := by
  have hlenw := past_length e t d
  have htake := take_left_past e t d (by omega)
  intro h
  apply min_P2_not_prefix_AAS (past e t d)
  · intro f hf
    have hf' : f < d := by simpa [hlenw] using hf
    intro hPf
    have htake_f : (past e t d).take f = past e t f :=
      LowSSEndpoint.take_past e t d f (by omega)
    have hPs : ShortPeriodicSupply.P2 e t f :=
      (past_p2_iff e t f).mp (by simpa [htake_f] using hPf)
    exact hmin f hf' hPs
  · simpa [hlenw] using hlen
  · simpa [htake] using h

theorem take3_of_head (l : List Bool) (h : 3 ≤ l.length)
    (h0 : l[0]? = some true) (h1 : l[1]? = some true)
    (h2 : l[2]? = some false) :
    l.take 3 = [true,true,false] := by
  match l with
  | [] => simp at h
  | _ :: [] => simp at h
  | _ :: _ :: [] => simp at h
  | b0 :: b1 :: b2 :: rest =>
    simp at h0 h1 h2
    simp [h0,h1,h2]

theorem drop_take_three (w : List Bool) (a : Nat)
    (ha : 3 ≤ a) (had : a < w.length)
    (hA : ∀ i : Nat, i < a → w[i]? = some true)
    (hS : w[a]? = some false) :
    (w.drop (a-2)).take 3 = [true,true,false] := by
  have hlen : 3 ≤ (w.drop (a-2)).length := by
    simp [List.length_drop]; omega
  have h0 : (w.drop (a-2))[0]? = some true := by
    have := hA (a-2) (by omega)
    simpa [List.getElem?_drop] using this
  have h1 : (w.drop (a-2))[1]? = some true := by
    have := hA (a-1) (by omega)
    have hidx : a-2+1 = a-1 := by omega
    simpa [List.getElem?_drop,hidx] using this
  have h2 : (w.drop (a-2))[2]? = some false := by
    have hidx : a-2+2 = a := by omega
    simpa [List.getElem?_drop,hidx] using hS
  exact take3_of_head _ hlen h0 h1 h2

theorem drop_past (e : Int → Bool) (t : Int) (d k : Nat) (hk : k ≤ d) :
    (past e t d).drop k = past e (t - (k : Int)) (d-k) := by
  have hsplit := past_append e t k (d-k)
  have hd : k+(d-k)=d := by omega
  have hw : past e t d = past e t k ++ past e (t - (k : Int)) (d-k) := by
    simpa [hd] using hsplit
  rw [hw]
  have : (past e t k ++ past e (t-(k : Int)) (d-k)).drop k =
      (past e t k ++ past e (t-(k : Int)) (d-k)).drop (past e t k).length := by
    simp [past_length]
  rw [this]
  exact List.drop_left

/-- The source `t-(a-2)` sits inside the leading A run and its length-3
past is AAS. -/
theorem leading_run_clean_sibling (e : Int → Bool) (t : Int) (d a : Nat)
    (ha : 3 ≤ a) (had : a < d)
    (hA : ∀ i : Nat, i < a → (past e t d)[i]? = some true)
    (hS : (past e t d)[a]? = some false) :
    let u := t - ((a-2 : Nat) : Int)
    past e u 3 = [true,true,false] ∧
      ShortPeriodicSupply.P2 e u 3 ∧ u < t := by
  intro u
  have hdrop := drop_past e t d (a-2) (by omega)
  have hlen : 3 ≤ d - (a-2) := by omega
  have htake := take_left_past e u (d-(a-2)) hlen
  have hword := drop_take_three (past e t d) a ha
    (by simpa [past_length] using had) hA hS
  have hp : past e u 3 = [true,true,false] := by
    have h1 : (past e t d).drop (a-2) = past e u (d-(a-2)) := hdrop
    calc
      past e u 3 = (past e u (d-(a-2))).take 3 := htake.symm
      _ = ((past e t d).drop (a-2)).take 3 := by rw [h1]
      _ = [true,true,false] := hword
  refine ⟨hp,(past_p2_iff e u 3).mp ?_,?_⟩
  · simpa [hp] using p2_AAS
  · dsimp [u]; omega

theorem canonical_window_get? :
    (past canonicalSign 114 11)[0]? = some true ∧
    (past canonicalSign 114 11)[1]? = some true ∧
    (past canonicalSign 114 11)[2]? = some true ∧
    (past canonicalSign 114 11)[3]? = some false := by
  have hw := canonical_window
  simp [hw,boundaryWord]

theorem canonical_clean_sibling :
    past canonicalSign 113 3 = [true,true,false] ∧
    ShortPeriodicSupply.P2 canonicalSign 113 3 ∧
    (113 : Int) < 114 := by
  have hlead := canonical_window_get?
  have hA : ∀ i : Nat, i < 3 → (past canonicalSign 114 11)[i]? = some true := by
    intro i hi
    match i with
    | 0 => exact hlead.1
    | 1 => exact hlead.2.1
    | 2 => exact hlead.2.2.1
    | n+3 => omega
  have h := leading_run_clean_sibling canonicalSign 114 11 3
    (by omega) (by omega) hA hlead.2.2.2
  simpa using h

theorem canonical_newest_S :
    (past canonicalSign 114 11)[3]? = some false :=
  canonical_window_get?.2.2.2

theorem range_three : List.range 3 = [0,1,2] := by decide

theorem past_three_eq (e : Int → Bool) (u : Int) :
    past e u 3 = [e (u-1), e (u-2), e (u-3)] := by
  simp [past,range_three,Int.natCast_add]

/-- Dual of `leading_run_clean_sibling` at a=3. An isolated a=0 source
at t that begins an A-run of length at least 3 has a later clean lag-3
source at t+2 whose E-128 endpoint is t-1. This is why unrestricted
previous-S joint with low-SS fails. -/
theorem isolated_start_clean_sibling (e : Int → Bool) (t : Int)
    (hS : e (t-1) = false) (hA : e t = true)
    (hA1 : e (t+1) = true) (hA2 : e (t+2) = true) :
    e (t+2) = true ∧ past e (t+2) 3 = [true,true,false] ∧
      ShortPeriodicSupply.P2 e (t+2) 3 := by
  have hp : past e (t+2) 3 = [true,true,false] := by
    have h1 : (t+2)-1 = t+1 := by omega
    have h2 : (t+2)-2 = t := by omega
    have h3 : (t+2)-3 = t-1 := by omega
    rw [past_three_eq,h1,h2,h3,hA1,hA,hS]
  refine ⟨hA2,hp,(past_p2_iff e (t+2) 3).mp ?_⟩
  simpa [hp] using p2_AAS

theorem ssCount_AAS : ssCount [true, true, false] = 0 := by decide

/-- An isolated start of an A-run of length ≥3 always produces a later
clean lag-3 source. If the isolated time itself is a clean min P2, the
run therefore contains two clean sources. This is the 41 canonical
pairs of E-150, not a new charge. -/
theorem isolated_start_later_is_clean (e : Int → Bool) (t : Int)
    (hS : e (t - 1) = false) (hA : e t = true)
    (hA1 : e (t + 1) = true) (hA2 : e (t + 2) = true) :
    ShortPeriodicSupply.P2 e (t + 2) 3 ∧ ssCount (past e (t + 2) 3) = 0 := by
  have h := isolated_start_clean_sibling e t hS hA hA1 hA2
  refine ⟨h.2.2, ?_⟩
  simpa [h.2.1] using ssCount_AAS

end Recaman.TwoSSLeadingSibling
