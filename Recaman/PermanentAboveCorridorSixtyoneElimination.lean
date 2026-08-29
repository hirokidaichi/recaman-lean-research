import Recaman.PermanentAboveCorridorNineteenElimination

namespace Recaman

noncomputable section

/-! # Elimination of the sixty-one replay

A sixty-one replay pins its stored history below clock fifty-nine
while its permanent tail must begin after time 222, where the orbit
still visits forty-seven.  The tail minimum then exceeds sixty-two and
its predecessor value first occurs at some clock at most fifty-eight.
A finite sweep over these clocks leaves only predecessor values whose
successors are all seen by time 222 — but a seen value can never recur
at the minimum clock beyond the tail start.  The sixty-one replay is
therefore impossible.

This removes the last exceptional target: the replay crossing clock is
at least thirty-two and the replay target is at least thirty-four,
both unconditionally.
-/

namespace TerminalExactDischargeReplayCertificate

variable {target start : Nat} {parent : PhaseSearchNode}
variable {source : PermanentTailDischargeReturnCertificate target start parent}

/-- The sixty-one tail starts after time 222: the orbit still visits
forty-seven there. -/
theorem sixtyone_tailStart_bound
    (_r : TerminalExactDischargeReplayCertificate source)
    (h61 : target = 61) :
    222 < source.tailStart := by
  by_cases hbound : 222 < source.tailStart
  · exact hbound
  · have hle : source.tailStart ≤ 222 := by omega
    have habove := source.historical_tail.strictly_above 222 hle
    have hval : a 222 = 47 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- The sixty-one replay is impossible.  Its minimum predecessor first
occurs by clock fifty-eight, yet every orbit value there is either at
most sixty-one, a revisit, or has its successor seen by time 222 —
each contradicting the pinned minimum beyond the tail start. -/
theorem target_ne_sixtyone
    (r : TerminalExactDischargeReplayCertificate source) :
    target ≠ 61 := by
  intro h61
  have hfd := source.downcross.horizon_le_time
  have helig := r.eligible
  have htime := r.time_eq
  have hlt := r.crossingTime_lt_target
  have hfbound : source.historicalFirstTime ≤ 58 := by omega
  have hpred := source.historical_minimum.predecessor_first
  have htgt := source.historical_minimum.target_lt_predecessor
  have htail := r.sixtyone_tailStart_bound h61
  have hstart := source.historical_minimum.minimum.start_le_time
  have hmin222 : 222 < source.historicalMinimumTime := by omega
  have hcases : source.historicalFirstTime = 0 ∨
      source.historicalFirstTime = 1 ∨
      source.historicalFirstTime = 2 ∨
      source.historicalFirstTime = 3 ∨
      source.historicalFirstTime = 4 ∨
      source.historicalFirstTime = 5 ∨
      source.historicalFirstTime = 6 ∨
      source.historicalFirstTime = 7 ∨
      source.historicalFirstTime = 8 ∨
      source.historicalFirstTime = 9 ∨
      source.historicalFirstTime = 10 ∨
      source.historicalFirstTime = 11 ∨
      source.historicalFirstTime = 12 ∨
      source.historicalFirstTime = 13 ∨
      source.historicalFirstTime = 14 ∨
      source.historicalFirstTime = 15 ∨
      source.historicalFirstTime = 16 ∨
      source.historicalFirstTime = 17 ∨
      source.historicalFirstTime = 18 ∨
      source.historicalFirstTime = 19 ∨
      source.historicalFirstTime = 20 ∨
      source.historicalFirstTime = 21 ∨
      source.historicalFirstTime = 22 ∨
      source.historicalFirstTime = 23 ∨
      source.historicalFirstTime = 24 ∨
      source.historicalFirstTime = 25 ∨
      source.historicalFirstTime = 26 ∨
      source.historicalFirstTime = 27 ∨
      source.historicalFirstTime = 28 ∨
      source.historicalFirstTime = 29 ∨
      source.historicalFirstTime = 30 ∨
      source.historicalFirstTime = 31 ∨
      source.historicalFirstTime = 32 ∨
      source.historicalFirstTime = 33 ∨
      source.historicalFirstTime = 34 ∨
      source.historicalFirstTime = 35 ∨
      source.historicalFirstTime = 36 ∨
      source.historicalFirstTime = 37 ∨
      source.historicalFirstTime = 38 ∨
      source.historicalFirstTime = 39 ∨
      source.historicalFirstTime = 40 ∨
      source.historicalFirstTime = 41 ∨
      source.historicalFirstTime = 42 ∨
      source.historicalFirstTime = 43 ∨
      source.historicalFirstTime = 44 ∨
      source.historicalFirstTime = 45 ∨
      source.historicalFirstTime = 46 ∨
      source.historicalFirstTime = 47 ∨
      source.historicalFirstTime = 48 ∨
      source.historicalFirstTime = 49 ∨
      source.historicalFirstTime = 50 ∨
      source.historicalFirstTime = 51 ∨
      source.historicalFirstTime = 52 ∨
      source.historicalFirstTime = 53 ∨
      source.historicalFirstTime = 54 ∨
      source.historicalFirstTime = 55 ∨
      source.historicalFirstTime = 56 ∨
      source.historicalFirstTime = 57 ∨
      source.historicalFirstTime = 58 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq |
    heq | heq
  · -- historicalFirstTime = 0, a 0 = 0
    rw [heq] at hpred
    have hp1 : a 0 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 0 = 0 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 1, a 1 = 1
    rw [heq] at hpred
    have hp1 : a 1 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 1 = 1 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 2, a 2 = 3
    rw [heq] at hpred
    have hp1 : a 2 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 2 = 3 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 3, a 3 = 6
    rw [heq] at hpred
    have hp1 : a 3 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 3 = 6 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 4, a 4 = 2
    rw [heq] at hpred
    have hp1 : a 4 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 4 = 2 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 5, a 5 = 7
    rw [heq] at hpred
    have hp1 : a 5 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 5 = 7 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 6, a 6 = 13
    rw [heq] at hpred
    have hp1 : a 6 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 6 = 13 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 7, a 7 = 20
    rw [heq] at hpred
    have hp1 : a 7 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 7 = 20 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 8, a 8 = 12
    rw [heq] at hpred
    have hp1 : a 8 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 8 = 12 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 9, a 9 = 21
    rw [heq] at hpred
    have hp1 : a 9 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 9 = 21 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 10, a 10 = 11
    rw [heq] at hpred
    have hp1 : a 10 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 10 = 11 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 11, a 11 = 22
    rw [heq] at hpred
    have hp1 : a 11 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 11 = 22 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 12, a 12 = 10
    rw [heq] at hpred
    have hp1 : a 12 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 12 = 10 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 13, a 13 = 23
    rw [heq] at hpred
    have hp1 : a 13 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 13 = 23 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 14, a 14 = 9
    rw [heq] at hpred
    have hp1 : a 14 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 14 = 9 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 15, a 15 = 24
    rw [heq] at hpred
    have hp1 : a 15 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 15 = 24 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 16, a 16 = 8
    rw [heq] at hpred
    have hp1 : a 16 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 16 = 8 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 17, a 17 = 25
    rw [heq] at hpred
    have hp1 : a 17 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 17 = 25 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 18, a 18 = 43
    rw [heq] at hpred
    have hp1 : a 18 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 18 = 43 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 19, a 19 = 62
    rw [heq] at hpred
    have hp1 : a 19 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 19 = 62 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 63 := by
      omega
    have hwit : a 21 = 63 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (63 : Nat) ∈ valuesThrough 21 :=
      mem_valuesThrough_iff.mpr ⟨21, Nat.le_refl _, hwit⟩
    have hseen : (63 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        63 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 20, a 20 = 42
    rw [heq] at hpred
    have hp1 : a 20 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 20 = 42 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 21, a 21 = 63
    rw [heq] at hpred
    have hp1 : a 21 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 21 = 63 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 64 := by
      omega
    have hwit : a 99 = 64 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (64 : Nat) ∈ valuesThrough 99 :=
      mem_valuesThrough_iff.mpr ⟨99, Nat.le_refl _, hwit⟩
    have hseen : (64 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        64 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 22, a 22 = 41
    rw [heq] at hpred
    have hp1 : a 22 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 22 = 41 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 23, a 23 = 18
    rw [heq] at hpred
    have hp1 : a 23 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 23 = 18 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 24, a 24 = 42
    rw [heq] at hpred
    have hp1 : a 24 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 24 = 42 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 25, a 25 = 17
    rw [heq] at hpred
    have hp1 : a 25 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 25 = 17 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 26, a 26 = 43
    rw [heq] at hpred
    have hp1 : a 26 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 26 = 43 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 27, a 27 = 16
    rw [heq] at hpred
    have hp1 : a 27 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 27 = 16 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 28, a 28 = 44
    rw [heq] at hpred
    have hp1 : a 28 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 28 = 44 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 29, a 29 = 15
    rw [heq] at hpred
    have hp1 : a 29 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 29 = 15 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 30, a 30 = 45
    rw [heq] at hpred
    have hp1 : a 30 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 30 = 45 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 31, a 31 = 14
    rw [heq] at hpred
    have hp1 : a 31 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 31 = 14 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 32, a 32 = 46
    rw [heq] at hpred
    have hp1 : a 32 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 32 = 46 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 33, a 33 = 79
    rw [heq] at hpred
    have hp1 : a 33 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 33 = 79 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 80 := by
      omega
    have hwit : a 43 = 80 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (80 : Nat) ∈ valuesThrough 43 :=
      mem_valuesThrough_iff.mpr ⟨43, Nat.le_refl _, hwit⟩
    have hseen : (80 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        80 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 34, a 34 = 113
    rw [heq] at hpred
    have hp1 : a 34 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 34 = 113 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 114 := by
      omega
    have hwit : a 36 = 114 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (114 : Nat) ∈ valuesThrough 36 :=
      mem_valuesThrough_iff.mpr ⟨36, Nat.le_refl _, hwit⟩
    have hseen : (114 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        114 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 35, a 35 = 78
    rw [heq] at hpred
    have hp1 : a 35 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 35 = 78 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 79 := by
      omega
    have hwit : a 33 = 79 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (79 : Nat) ∈ valuesThrough 33 :=
      mem_valuesThrough_iff.mpr ⟨33, Nat.le_refl _, hwit⟩
    have hseen : (79 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        79 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 36, a 36 = 114
    rw [heq] at hpred
    have hp1 : a 36 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 36 = 114 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 115 := by
      omega
    have hwit : a 170 = 115 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (115 : Nat) ∈ valuesThrough 170 :=
      mem_valuesThrough_iff.mpr ⟨170, Nat.le_refl _, hwit⟩
    have hseen : (115 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        115 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 37, a 37 = 77
    rw [heq] at hpred
    have hp1 : a 37 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 37 = 77 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 78 := by
      omega
    have hwit : a 35 = 78 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (78 : Nat) ∈ valuesThrough 35 :=
      mem_valuesThrough_iff.mpr ⟨35, Nat.le_refl _, hwit⟩
    have hseen : (78 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        78 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 38, a 38 = 39
    rw [heq] at hpred
    have hp1 : a 38 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 38 = 39 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 39, a 39 = 78
    rw [heq] at hpred
    have hp1 : a 39 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 39 = 78 := by
      set_option maxRecDepth 100000 in decide
    have hearlier : a 35 = 78 := by
      set_option maxRecDepth 100000 in decide
    exact (hpred.2 35 (by omega)) (by omega)
  · -- historicalFirstTime = 40, a 40 = 38
    rw [heq] at hpred
    have hp1 : a 40 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 40 = 38 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 41, a 41 = 79
    rw [heq] at hpred
    have hp1 : a 41 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 41 = 79 := by
      set_option maxRecDepth 100000 in decide
    have hearlier : a 33 = 79 := by
      set_option maxRecDepth 100000 in decide
    exact (hpred.2 33 (by omega)) (by omega)
  · -- historicalFirstTime = 42, a 42 = 37
    rw [heq] at hpred
    have hp1 : a 42 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 42 = 37 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 43, a 43 = 80
    rw [heq] at hpred
    have hp1 : a 43 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 43 = 80 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 81 := by
      omega
    have hwit : a 45 = 81 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (81 : Nat) ∈ valuesThrough 45 :=
      mem_valuesThrough_iff.mpr ⟨45, Nat.le_refl _, hwit⟩
    have hseen : (81 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        81 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 44, a 44 = 36
    rw [heq] at hpred
    have hp1 : a 44 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 44 = 36 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 45, a 45 = 81
    rw [heq] at hpred
    have hp1 : a 45 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 45 = 81 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 82 := by
      omega
    have hwit : a 47 = 82 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (82 : Nat) ∈ valuesThrough 47 :=
      mem_valuesThrough_iff.mpr ⟨47, Nat.le_refl _, hwit⟩
    have hseen : (82 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        82 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 46, a 46 = 35
    rw [heq] at hpred
    have hp1 : a 46 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 46 = 35 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 47, a 47 = 82
    rw [heq] at hpred
    have hp1 : a 47 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 47 = 82 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 83 := by
      omega
    have hwit : a 49 = 83 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (83 : Nat) ∈ valuesThrough 49 :=
      mem_valuesThrough_iff.mpr ⟨49, Nat.le_refl _, hwit⟩
    have hseen : (83 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        83 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 48, a 48 = 34
    rw [heq] at hpred
    have hp1 : a 48 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 48 = 34 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 49, a 49 = 83
    rw [heq] at hpred
    have hp1 : a 49 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 49 = 83 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 84 := by
      omega
    have hwit : a 51 = 84 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (84 : Nat) ∈ valuesThrough 51 :=
      mem_valuesThrough_iff.mpr ⟨51, Nat.le_refl _, hwit⟩
    have hseen : (84 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        84 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 50, a 50 = 33
    rw [heq] at hpred
    have hp1 : a 50 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 50 = 33 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 51, a 51 = 84
    rw [heq] at hpred
    have hp1 : a 51 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 51 = 84 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 85 := by
      omega
    have hwit : a 53 = 85 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (85 : Nat) ∈ valuesThrough 53 :=
      mem_valuesThrough_iff.mpr ⟨53, Nat.le_refl _, hwit⟩
    have hseen : (85 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        85 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 52, a 52 = 32
    rw [heq] at hpred
    have hp1 : a 52 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 52 = 32 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 53, a 53 = 85
    rw [heq] at hpred
    have hp1 : a 53 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 53 = 85 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 86 := by
      omega
    have hwit : a 55 = 86 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (86 : Nat) ∈ valuesThrough 55 :=
      mem_valuesThrough_iff.mpr ⟨55, Nat.le_refl _, hwit⟩
    have hseen : (86 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        86 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 54, a 54 = 31
    rw [heq] at hpred
    have hp1 : a 54 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 54 = 31 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 55, a 55 = 86
    rw [heq] at hpred
    have hp1 : a 55 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 55 = 86 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 87 := by
      omega
    have hwit : a 57 = 87 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (87 : Nat) ∈ valuesThrough 57 :=
      mem_valuesThrough_iff.mpr ⟨57, Nat.le_refl _, hwit⟩
    have hseen : (87 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        87 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 56, a 56 = 30
    rw [heq] at hpred
    have hp1 : a 56 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 56 = 30 := by
      set_option maxRecDepth 100000 in decide
    omega
  · -- historicalFirstTime = 57, a 57 = 87
    rw [heq] at hpred
    have hp1 : a 57 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 57 = 87 := by
      set_option maxRecDepth 100000 in decide
    have hmin : a source.historicalMinimumTime = 88 := by
      omega
    have hwit : a 59 = 88 := by
      set_option maxRecDepth 100000 in decide
    have hmem : (88 : Nat) ∈ valuesThrough 59 :=
      mem_valuesThrough_iff.mpr ⟨59, Nat.le_refl _, hwit⟩
    have hseen : (88 : Nat) ∈
        valuesThrough (source.historicalMinimumTime - 1) :=
      valuesThrough_mono (by omega) hmem
    have hsucc : source.historicalMinimumTime - 1 + 1 =
        source.historicalMinimumTime := by omega
    have hgoal : a (source.historicalMinimumTime - 1 + 1) =
        88 := by
      rw [hsucc]
      exact hmin
    exact (a_succ_ne_of_seen hseen (by omega)) hgoal
  · -- historicalFirstTime = 58, a 58 = 29
    rw [heq] at hpred
    have hp1 : a 58 = a source.historicalMinimumTime - 1 :=
      hpred.1
    have hv : a 58 = 29 := by
      set_option maxRecDepth 100000 in decide
    omega

/-- Unconditional third floor: the replay crossing clock is at least
thirty-two. -/
theorem thirtytwo_le_crossingTime
    (r : TerminalExactDischargeReplayCertificate source) :
    32 ≤ r.crossingTime := by
  rcases r.thirtytwo_le_crossingTime_or_sixtyone with hbig | h61
  · exact hbig
  · exact absurd h61 r.target_ne_sixtyone

/-- The replay target is at least thirty-four. -/
theorem thirtyfour_le_target
    (r : TerminalExactDischargeReplayCertificate source) :
    34 ≤ target := by
  rcases r.target_split with h19 | h61 | hbig
  · exact absurd h19 r.target_ne_nineteen
  · exact absurd h61 r.target_ne_sixtyone
  · exact hbig

end TerminalExactDischargeReplayCertificate

end

end Recaman
