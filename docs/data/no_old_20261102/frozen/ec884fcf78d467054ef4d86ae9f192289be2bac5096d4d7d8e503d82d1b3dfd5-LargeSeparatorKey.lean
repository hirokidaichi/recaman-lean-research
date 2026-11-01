import Recaman.FourthActualSeven

namespace Recaman.LargeSeparatorKey

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem small_budget_key (S R v r : Nat) (ku kz : Int)
    (hS : 3≤S) (hv : 6≤v) (hcost : r+v≤9) (hsmall : S≤2*r+1)
    (hR : r+1≤R) (hlo : -2≤ku) (hkz : -2*(S : Int)^2≤kz)
    (hthree : S=3 → kz= -6)
    (hid : ku= -kz-12*((S : Int)+(v : Int))+2*(v : Int)^2-2*(R : Int)^2) : False := by
  have hr : r=1 ∨ r=2 ∨ r=3 := by omega
  have hv' : v=6 ∨ v=7 ∨ v=8 := by omega
  rcases hr with rfl|rfl|rfl <;> rcases hv' with rfl|rfl|rfl
  all_goals try omega
  all_goals have hRR:=Int.mul_nonneg (show 0≤(R : Int)-((r : Int)+1) by omega)
    (show 0≤(R : Int)+((r : Int)+1) by omega)
  all_goals have hSS:=Int.mul_nonneg (show 0≤(2*(r : Int)+1)-(S : Int) by omega)
    (show 0≤(S : Int)+(2*(r : Int)+1)-6 by omega)
  all_goals try have ht : S=3 := by omega
  all_goals try have htkey:=hthree ht
  all_goals grind only

/-- A zero-mass genuine three-run head cannot support the small free
budget required by a counter with separator at least six. The S=3
boundary retains the actual run word rather than its coarse key bound. -/
theorem large_separator_key_excluded (u z : List Bool) (hu : BlockWord u)
    (h M m L s U R v r : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hz : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)
    (hmz : M+L+U=h+m+s) (hv : 6≤v) (hcost : r+v≤9)
    (hsmall : h+m+s≤2*r+1) (hR : r+1≤R)
    (hid : runKey u= -runKey z-12*((h : Int)+(m : Int)+(s : Int)+(v : Int))+
      2*(v : Int)^2-2*(R : Int)^2) : False := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hcnt : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hm0 : mass z=0 := by rw [hz]; simp only [mass_append,mass_rep_false,mass_replicate_A]; omega
    have hlen : z.length=h+M+m+L+s+U := by simp [hz]
    rw [hm0,hlen] at hc
    omega
  have hkz:=runKey_count_lower z
  rw [hcnt] at hkz
  have hthree : h+m+s=3 → runKey z= -6 := by
    intro hsum
    have hh1 : h=1 := by omega
    have hm1 : m=1 := by omega
    have hs1 : s=1 := by omega
    have hM1 : M=1 := by omega
    have hL1 : L=1 := by omega
    have hU1 : U=1 := by omega
    rw [hz,hh1,hm1,hs1,hM1,hL1,hU1]
    decide
  exact small_budget_key (h+m+s) R v r (runKey u) (runKey z) (by omega) hv hcost hsmall hR hlo
    (by simpa only [Int.natCast_add] using hkz) hthree
    (by simpa only [Int.natCast_add] using hid)

end Recaman.LargeSeparatorKey
