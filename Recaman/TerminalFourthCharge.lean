import Recaman.TerminalOldClock
import Recaman.ThreeRunSupplyBudget

namespace Recaman.TerminalFourthCharge

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.TerminalLocalProfile Recaman.TerminalOldClock Recaman.ThreeRunSupplyBudget

/-- The unrestricted old prefix contributes at most one clock, all at
clock4 or later. Together with the exact local profile this limits the
last-ray charge to1, without erasing any original supply. -/
theorem terminal_ray_count_charge (w : List Bool) (hw : BlockWord w) (v T : Nat)
    (hv : 1≤v) : 2*rayCount (w++(seed++List.replicate v false)) T≤T+1 := by
  have hc : 3≤cntF (seed++List.replicate v false) := by
    rw [cntF_append,cntF_replicate_S]
    have hseed : cntF seed=10 := by decide
    rw [hseed]
    omega
  have hb:=block_rayCount_append hw (seed++List.replicate v false) hc T
  have hl:=terminal_local_count_le_two v T hv
  by_cases hT : 5≤T
  · omega
  · have heq : rayCount (w++(seed++List.replicate v false)) T=
        rayCount (seed++List.replicate v false) T := by
      apply cN_congr
      intro i hi hiT
      rw [ray_supply_append_iff]
      have hn : ¬tailOldRay w (seed++List.replicate v false) i := by
        intro he
        have hh:=terminal_old_clock_ge_four w hw v i hv he
        omega
      exact or_iff_right hn
    rw [heq]
    have hh:=terminal_local_count_half v T hv
    omega

/-- Same actual f0, with a fixed seed but arbitrary old BlockWord,
positive separator length and final A-run length. -/
theorem terminal_last_run_charge (f : Nat → Bool) (n v T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hseed : seg f n 20=seed) (hv : 1≤v)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ i, i<T → f (n+20+v+i)=true) :
    T≤2*cN (fun x=>f x=true ∧ ¬EndN f 0 x) (n+20+v) T+1 := by
  have hshape : seg f 0 (n+20+v)=w++(seed++List.replicate v false) := by
    rw [show n+20+v=n+(20+v) by omega,seg_add,Nat.zero_add,hpre,seg_add,
      hseed,seg_false f (n+20) v hS]
  have hE:=endable_A_run_count f (n+20+v) T _ hshape hA
  have hc:=terminal_ray_count_charge w hw v T hv
  have hpart:=addition_endable_partition f (n+20+v) T
  rw [count_A_run f (n+20+v) T hA] at hpart
  omega

/-- Fixed-seed four-run charge<=3 for every v/T and unchanged actual old
history. It does not prove this charge bound for arbitrary four runs. -/
theorem terminal_four_run_charge (f : Nat → Bool) (n v T : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (hseed : seg f n 20=seed) (hv : 1≤v)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ i, i<T → f (n+20+v+i)=true)
    (hpos : ∀ k, 0<k → k≤20+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    10+T≤2*cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T)+3 := by
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hA10 : cN (fun x=>f x=true) n 20=10 := by
    have hc:=ones_seg_eq_count f n 20
    rw [hseed] at hc
    have hs : ones seed=10 := by decide
    rw [hs] at hc
    omega
  have hF4 : 4≤cN P n 20 := by
    by_cases hh : cN P n 20≤3
    · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
      have hb:=positive_r3_additions_free_bound f n 0 20 hw hpre0
        (fun k hk hk20=>hpos k hk (by omega)) hh
      rw [hA10] at hb
      change 10≤2*cN P n 20+1 at hb
      omega
    · omega
  have hlast:=terminal_last_run_charge f n v T w hw hpre hseed hv hS hA
  have hz : cN P (n+20) v=0 := by
    apply cN_zero_of
    intro x hx hxv he
    have hh:=hS x hx hxv
    change f x=true ∧ ¬EndN f 0 x at he
    rw [hh] at he
    simp at he
  have h1:=cN_add P n 20 v
  have h2:=cN_add P n (20+v) T
  change 10+T≤2*cN P n (20+v+T)+3
  change T≤2*cN P (n+20+v) T+1 at hlast
  rw [hz] at h1
  simp only [Nat.add_assoc] at *
  omega


/-- A genuine four-run subfamily: the fixed seed followed by arbitrary
Sv AT. A final-S local source in the target band and the same old target
force full-tail free-gap. This is not all four-run C1. -/
theorem terminal_final_S_free_gap (f : Nat → Bool) (n t v T j q i : Nat) (w : List Bool)
    (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hseed : seg f n 20=seed)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ k, k<T → f (n+20+v+k)=true)
    (hgap : ∀ x, n+20+v+T≤x → x<n+20+v+T+j → f x=false)
    (htarget : Win f t (n+20+v+T+j-t))
    (hlocal : Win f (n+20+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤20+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T) := by
  have hcharge:=terminal_four_run_charge f n v T w hw hpre hseed hv hS hA hpos
  have hword : seg f n (20+v+T)=seed++List.replicate v false++List.replicate T true := by
    rw [seg_add,seg_add,hseed,seg_false f (n+20) v hS]
    have hh : seg f (n+(20+v)) T=List.replicate T true := by
      apply seg_A
      intro x hx hxt
      have hh:=hA (x-(n+20+v)) (by omega)
      rw [show n+20+v+(x-(n+20+v))=x by omega] at hh
      exact hh
    rw [hh]
  have hraw : seg f n (5+3+4+4+1+3+v+T)=
      List.replicate 5 false++List.replicate 3 true++List.replicate 4 false++
      List.replicate 4 true++List.replicate 1 false++List.replicate 3 true++
      List.replicate v false++List.replicate T true := by
    simpa only [seed,List.replicate_one,List.append_assoc] using hword
  have hsrc:=Recaman.FourRunTargetArea.actual_final_S_source_A_budget
    f n t 5 3 4 4 1 3 v T j q i w hw hpre ht
    (by decide) (by decide) (by decide) (by decide) (by decide) hv hq hqv hi hband hraw
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hS)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hA)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hgap)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using htarget)
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hlocal)
  have hcnt : cN (fun x=>f x=true) n (20+v+T)=10+T := by
    have hh:=ones_seg_eq_count f n (20+v+T)
    rw [hword,ones_append,ones_append,ones_replicate_S,ones_replicate_A] at hh
    have hseedA : ones seed=10 := by decide
    rw [hseedA] at hh
    omega
  have hsrc' : 2*(j+1)+2≤cN (fun x=>f x=true) n (20+v+T) := by simpa only [Nat.reduceAdd] using hsrc.2.2
  rw [hcnt] at hsrc'
  omega

end Recaman.TerminalFourthCharge
