import Recaman.LowCrossLocalClocks

namespace Recaman.LowCrossOldClocks

open Recaman.LowCrossLocalClocks Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction

private theorem gate_constraints (x : List Bool) (i : Nat)
    (h : Recaman.OldMassEndpointGate.oldPossible x i=true) :
    let c:=1-mass x-(i : Int)
    let k:=runKey x+4*c*(cntF x : Int)
    1≤c ∧ k≤0 ∧ (c=1 → k= -2) ∧ (c=2 → k= -2 ∨ k=0) := by
  let c:=1-mass x-(i : Int)
  let k:=runKey x+4*c*(cntF x : Int)
  change 1≤c ∧ k≤0 ∧ (c=1 → k= -2) ∧ (c=2 → k= -2 ∨ k=0)
  change (if c=1 then decide (k= -2) else if c=2 then decide (k= -2 ∨ k=0)
    else decide (3≤c ∧ k≤0))=true at h
  by_cases h1 : c=1
  · rw [if_pos h1] at h
    have hk:=of_decide_eq_true h
    exact ⟨by omega,by omega,fun _=>hk,by omega⟩
  · rw [if_neg h1] at h
    by_cases h2 : c=2
    · rw [if_pos h2] at h
      have hk:=of_decide_eq_true h
      exact ⟨by omega,by omega,by omega,fun _=>hk⟩
    · rw [if_neg h2] at h
      obtain ⟨hc,hk⟩:=of_decide_eq_true h
      exact ⟨by omega,hk,by omega,by omega⟩

private theorem old_before_last_S_arith (a s z qx qz c k : Int)
    (hs : 0≤s) (hz : 0≤z) (hqx : 0≤qx) (hqz : 0≤qz) (ha : 0≤a)
    (hS : s+z=6) (hc : c=1-(a-s))
    (hQ : qx+qz+4*(a+1)*z≤20) (hkey : k=qx-2*s^2+4*c*s)
    (hc1 : 1≤c) (hk : k≤0) (h1 : c=1 → k= -2) (h2 : c=2 → k= -2 ∨ k=0)
    (hzero : s=0 → qx=0) : z=0 := by
  by_cases hz0 : z=0
  · exact hz0
  · have hs0 : 0<s := by
      by_cases h : s=0
      · have hq0:=hzero h
        have hc' := h1 (by omega)
        rw [h,hq0] at hkey
        omega
      · omega
    have hC : 2*c≤s := by
      by_cases h : 2*c≤s
      · exact h
      · have hp:=Int.mul_pos (show 0<2*c-s by omega) hs0
        grind only
    have ha2 : 2≤a := by omega
    have hz1 : z=1 := by
      by_cases he : z=1
      · exact he
      · have hp:=Int.mul_nonneg (show 0≤a-2 by omega) hz
        grind only
    rw [hz1] at hQ
    have hs5 : s=5 := by omega
    have hqa : qx=0 := by omega
    have hct : c=2 := by omega
    have hcon:=h2 hct
    rw [hct,hs5,hqa] at hkey
    omega

/-- With six subtractions and at most five AS pairs, any original
BlockWord source is confined to additions after the last subtraction. -/
theorem low_cross_old_after_last_S (w x z : List Bool) (hw : BlockWord w)
    (hS : cntF x+cntF z=6) (hQ : cross (x++[true]++z)≤20)
    (he : tailOldRay w x 0) : cntF z=0 := by
  have hGate:=Recaman.OldMassEndpointGate.old_source_passes_mass_gate w x 0 hw he
  obtain ⟨hC,hk,h1,h2⟩:=gate_constraints x 0 hGate
  let c:=1-mass x
  let k:=runKey x+4*c*(cntF x : Int)
  change 1≤1-mass x-(0 : Int) at hC
  have hc1 : 1≤c := by dsimp [c]; omega
  have hk' : k≤0 := by dsimp [k,c]; simpa using hk
  have h1' : c=1 → k= -2 := by dsimp [k,c]; simpa using h1
  have h2' : c=2 → k= -2 ∨ k=0 := by dsimp [k,c]; simpa using h2
  have hm:=mass_eq x
  have hf:=cntF_int x
  have hce : c=1-(ones x-(cntF x : Int)) := by dsimp [c]; omega
  rw [cross_at_addition] at hQ
  have hKey : k=cross x-2*(cntF x : Int)^2+4*c*(cntF x : Int) := by
    unfold cross
    dsimp [k]
    omega
  have hz:=old_before_last_S_arith (ones x) (cntF x : Int) (cntF z : Int)
    (cross x) (cross z) c k (by omega) (by omega) (cross_nonnegative x)
    (cross_nonnegative z) (ones_bounds x).1 (by omega) hce hQ hKey hc1 hk' h1' h2'
    (fun hs=>cross_zero_of_no_S x (by omega))
  omega

private theorem cross28_old_arith (a s z qx qz c k : Int)
    (hs : 0≤s) (hz : 0≤z) (hqx : 0≤qx) (hqz : 0≤qz) (ha : 0≤a)
    (hS : s+z=6) (hc : c=1-(a-s))
    (hQ : qx+qz+4*(a+1)*z=28) (hkey : k=qx-2*s^2+4*c*s)
    (hc1 : 1≤c) (hk : k≤0) (h1 : c=1 → k= -2)
    (hzero : s=0 → qx=0) (hz0 : z=0 → qz=0) :
    s=5 ∧ a=4 := by
  have hs0 : 0<s := by
    by_cases h : s=0
    · have hq0:=hzero h
      have hc' := h1 (by omega)
      rw [h,hq0] at hkey
      omega
    · omega
  have hC : 2*c≤s := by
    by_cases h : 2*c≤s
    · exact h
    · have hp:=Int.mul_pos (show 0<2*c-s by omega) hs0
      grind only
  have ha2 : 2≤a := by omega
  have hzle : z≤2 := by
    have hp:=Int.mul_nonneg (show 0≤a-2 by omega) hz
    grind only
  have hzn2 : z≠2 := by
    intro h
    rw [h] at hQ
    omega
  have hzn0 : z≠0 := by
    intro h
    have h6 : s=6 := by omega
    rw [h,hz0 h] at hQ
    rw [h6] at hkey
    by_cases hC1 : c=1
    · have hK:=h1 hC1
      omega
    · omega
  have hz1 : z=1 := by omega
  have hs5 : s=5 := by omega
  have hn5 : a≠5 := by
    intro h
    have hK:=h1 (by omega)
    rw [hz1,h] at hQ
    rw [hs5,show c=1 by omega] at hkey
    omega
  omega

/-- At seven AS pairs an old source can supply only the fifth addition,
with exactly five S signs before it. -/
theorem cross28_old_cut (w x z : List Bool) (hw : BlockWord w)
    (hS : cntF x+cntF z=6) (hQ : cross (x++[true]++z)=28)
    (he : tailOldRay w x 0) : cntF x=5 ∧ ones x=4 := by
  have hGate:=Recaman.OldMassEndpointGate.old_source_passes_mass_gate w x 0 hw he
  obtain ⟨hC,hk,h1,_⟩:=gate_constraints x 0 hGate
  let c:=1-mass x
  let k:=runKey x+4*c*(cntF x : Int)
  change 1≤1-mass x-(0 : Int) at hC
  have hc1 : 1≤c := by dsimp [c]; omega
  have hk' : k≤0 := by dsimp [k,c]; simpa using hk
  have h1' : c=1 → k= -2 := by dsimp [k,c]; simpa using h1
  have hm:=mass_eq x
  have hf:=cntF_int x
  have hce : c=1-(ones x-(cntF x : Int)) := by dsimp [c]; omega
  rw [cross_at_addition] at hQ
  have hKey : k=cross x-2*(cntF x : Int)^2+4*c*(cntF x : Int) := by
    unfold cross
    dsimp [k]
    omega
  obtain ⟨hs,ha⟩:=cross28_old_arith (ones x) (cntF x : Int) (cntF z : Int)
    (cross x) (cross z) c k (by omega) (by omega) (cross_nonnegative x)
    (cross_nonnegative z) (ones_bounds x).1 (by omega) hce hQ hKey hc1 hk' h1'
    (fun hs=>cross_zero_of_no_S x (by omega)) (fun hz=>cross_zero_of_no_S z (by omega))
  exact ⟨by omega,ha⟩

/-- With at most four total S signs and positive cross in the four-S
case, an old endpoint must have exactly three S signs before it. -/
theorem old_source_small_S (w x z : List Bool) (hw : BlockWord w)
    (hS : cntF x+cntF z≤4)
    (hCross : cross (x++[true]++z)=0 → cntF x+cntF z≤2)
    (ho : tailOldRay w x 0) : cntF x=3 := by
  have hbase:=runKey_count_lower x
  have h0 : 1≤cntF x := by
    by_cases h : 1≤cntF x
    · exact h
    · have hf : cntF x=0 := by omega
      rw [hf] at hbase
      exact (Recaman.NonnegativeFutureOldSource.no_old_source w x hw (by omega) 0 ho).elim
  obtain ⟨hn,he⟩:=Recaman.OldSourceNegativeThreshold.old_source_key_threshold w x 0 hw h0 ho
  have hc : cntF x=1 ∨ cntF x=2 ∨ cntF x=3 ∨ cntF x=4 := by omega
  rcases hc with h1|h2|h3|h4
  · rw [h1] at hbase hn
    omega
  · have hu:=he (by rw [h2] <;> decide)
    rw [h2] at hbase hu
    omega
  · exact h3
  · have hu:=he (by rw [h4] <;> decide)
    have hx : cross x=0 := by unfold cross; rw [h4] at hbase hu ⊢; omega
    have hz : cntF z=0 := by omega
    have hq : cross (x++[true]++z)=0 := by
      rw [cross_at_addition,hx,cross_zero_of_no_S z hz,hz]
      omega
    have hsmall:=hCross hq
    omega

/-- A clock-zero old source after three subtractions is the mass-one
old suffix. Its original mixed prefix has cross exactly four. -/
theorem old_at_three_S_data (w x : List Bool) (hw : BlockWord w)
    (hS : cntF x=3) (ho : tailOldRay w x 0) : ones x=3 ∧ cross x=4 := by
  obtain ⟨hC,hk,h1,_⟩:=gate_constraints x 0
    (Recaman.OldMassEndpointGate.old_source_passes_mass_gate w x 0 hw ho)
  let c:=1-mass x
  let k:=runKey x+4*c*(cntF x : Int)
  change 1≤1-mass x-(0 : Int) at hC
  have hc : 1≤c := by dsimp [c]; omega
  have hk' : k≤0 := by dsimp [k,c]; simpa using hk
  have h1' : c=1 → k= -2 := by dsimp [k,c]; simpa using h1
  have hlo:=runKey_count_lower x
  rw [hS] at hlo
  have he : c=1 := by
    dsimp only [k] at hk'
    rw [hS] at hk'
    omega
  have hKey:=h1' he
  dsimp only [k] at hKey
  rw [hS,he] at hKey
  have hm:=mass_eq x
  have hf:=cntF_int x
  rw [hS] at hf
  dsimp [c] at he
  unfold cross
  rw [hS]
  exact ⟨by omega,by omega⟩

end Recaman.LowCrossOldClocks
