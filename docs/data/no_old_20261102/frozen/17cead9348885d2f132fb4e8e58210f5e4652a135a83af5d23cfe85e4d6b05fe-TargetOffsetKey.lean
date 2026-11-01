import Recaman.FourthActualSeven

namespace Recaman.TargetOffsetKey

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem small_budget_key (S R v r : Nat) (ku kz : Int)
    (hS : 3≤S) (hv : 3≤v) (hcost : r+v≤6) (hsmall : S≤2*r+1)
    (hR : r+1≤R) (hlo : -2≤ku) (hkz : -2*(S : Int)^2≤kz)
    (hthree : S=3 → kz= -6)
    (hid : ku≤ -kz-12*(S : Int)-18+2*(v : Int)^2-2*(R : Int)^2) : False := by
  have hr : r=1 ∨ r=2 ∨ r=3 := by omega
  have hv' : v=3 ∨ v=4 ∨ v=5 := by omega
  have hRR:=Int.mul_nonneg (show 0≤(R : Int)-((r : Int)+1) by omega)
    (show 0≤(R : Int)+((r : Int)+1) by omega)
  have hSS:=Int.mul_nonneg (show 0≤(2*(r : Int)+1)-(S : Int) by omega)
    (show 0≤(S : Int)+(2*(r : Int)+1)-6 by omega)
  have hthree' : S=3 → kz= -6 := hthree
  rcases hr with rfl|rfl|rfl <;> rcases hv' with rfl|rfl|rfl
  all_goals try omega
  all_goals try have ht : S=3 := by omega
  all_goals try have htkey:=hthree' ht
  all_goals grind only

/-- For target mass at least four, the stated offset-key bound excludes the small head budget at separator difference at least three. The S3 boundary retains the actual run word. -/
theorem target_offset_key_excluded (u z : List Bool) (hu : BlockWord u)
    (h M m L s U R v r : Nat)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hz : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)
    (hmz : M+L+U=h+m+s) (hv : 3≤v) (hcost : r+v≤6)
    (hsmall : h+m+s≤2*r+1) (hR : r+1≤R)
    (hid : runKey u≤ -runKey z-12*((h : Int)+(m : Int)+(s : Int))-18+
      2*(v : Int)^2-2*(R : Int)^2) : False := by
  have hlo : -2≤runKey u := by
    have hb:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hcnt : cntF z=h+m+s := by
    have hc:=mass_cntF z
    have hm0 : mass z=0 := by rw [hz]; simp only [mass_append,mass_rep_false,mass_replicate_A]; omega
    have hlen : z.length=h+M+m+L+s+U := by simp [hz,Nat.add_assoc]
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

end Recaman.TargetOffsetKey
