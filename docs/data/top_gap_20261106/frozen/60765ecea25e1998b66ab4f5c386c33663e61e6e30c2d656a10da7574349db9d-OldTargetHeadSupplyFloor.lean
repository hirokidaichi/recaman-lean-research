import Recaman.DelayedOldTargetBudget
import Recaman.PrimitiveOldTargetCut

namespace Recaman.OldTargetHeadSupplyFloor

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem empty_prefix_ray_count (T : Nat) : rayCount [] T=0 := by
  apply cN_zero_of
  intro i _ _ hi
  have hh:=(localSupply_A_S_iff [] i 0).mp (by simpa only [List.replicate_zero,List.append_nil] using hi)
  obtain ⟨r,hr,_,_⟩:=hh
  simp only [List.length_nil] at hr
  omega

/-- An original same-old-target free counter needs at least j+1
actual suppliers before the final A ray. The prefix may be any mixed
word with at least two A signs and original relative positivity. -/
theorem old_target_head_supply_floor (f : Nat → Bool) (n t B T j : Nat)
    (hw : BlockWord (seg f 0 n)) (ht : t<n) (hj : 2≤j)
    (hC : 2≤mass (seg f t (n-t)))
    (hN : 2≤cN (fun x=>f x=true) n B)
    (hpos : ∀ k, 0<k → k≤B → cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hA : ∀ i, i<T → f (n+B+i)=true)
    (hgap : ∀ x, n+B+T≤x → x<n+B+T+j → f x=false)
    (htarget : Win f t (n+B+T+j-t))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (B+T)<j+1) :
    j+1≤cN (EndN f 0) n B := by
  let N:=cN (fun x=>f x=true) n B
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let r:=cN P n B
  let E:=cN (EndN f 0) (n+B) T
  have hr : 1≤r := by
    by_cases hz : r=0
    · have hb:=positive_r3_additions_free_bound f n 0 B hw (by simp) hpos
        (show r≤3 by omega)
      change N≤2*r+1 at hb
      change 2≤N at hN
      omega
    · omega
  have hAlower:=Recaman.PrimitiveOldTargetCut.actual_old_target_A_cut
    f n t (B+T) j (seg f 0 n) hw rfl ht hC
    (by simpa only [Nat.add_assoc] using hgap) (by simpa only [Nat.add_assoc] using htarget)
  have htA := count_A_run f (n+B) T hA
  have hAeq := cN_add (fun x=>f x=true) n B T
  rw [htA] at hAeq
  change cN (fun x=>f x=true) n (B+T)=N+T at hAeq
  rw [hAeq] at hAlower
  have hcut:=Recaman.DelayedOldTargetBudget.delayed_word_budget f n t B T j N (seg f n B) []
    hw ht hj hC (by rw [List.append_nil]) (by rw [ones_seg_eq_count]; exact Int.le_refl _) hA hgap htarget
  rw [empty_prefix_ray_count,Nat.add_zero] at hcut
  change E≤max (T-j) (N+T-(2*j+1)) at hcut
  have hpT:=addition_endable_partition f (n+B) T
  rw [htA] at hpT
  change T=E+cN P (n+B) T at hpT
  rw [cN_add P n B T] at hbad
  change r+cN P (n+B) T<j+1 at hbad
  have hfree : T+r≤j+E := by omega
  have hsplit:=addition_endable_partition f n B
  change N=cN (EndN f 0) n B+r at hsplit
  by_cases he : T-j≤N+T-(2*j+1)
  · rw [Nat.max_eq_right he] at hcut
    omega
  · rw [Nat.max_eq_left (by omega)] at hcut
    omega

end Recaman.OldTargetHeadSupplyFloor
