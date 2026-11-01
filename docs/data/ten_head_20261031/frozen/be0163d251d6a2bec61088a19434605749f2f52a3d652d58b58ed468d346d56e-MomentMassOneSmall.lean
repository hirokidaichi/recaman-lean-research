import Recaman.MomentMassOneGap
import Recaman.MomentSmallHeadPruning
import Recaman.MomentTargetProfile

namespace Recaman.MomentMassOneSmall

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.MomentActualTarget Recaman.MomentNoOld Recaman.MomentRunResidual
open Recaman.MomentTargetProfile Recaman.MomentSmallHeadPruning Recaman.ShortGapLocalBudget

private theorem actual_count_payment (f : Nat → Bool) (n H v T j F E : Nat)
    (hhead : F≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H)
    (hlast : cN (EndN f 0) (n+H+v) T≤E) (hpay : j+1+E≤F+T)
    (hS : ∀ x, n+H≤x → x<n+H+v → f x=false)
    (hA : ∀ k, k<T → f (n+H+v+k)=true) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (H+v+T) := by
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  have hzero : cN P (n+H) v=0 := by
    apply cN_zero_of
    intro x hx hxv hp
    have hf:=hS x hx hxv
    change f x=true ∧ ¬EndN f 0 x at hp
    rw [hf] at hp
    simp at hp
  have h1:=cN_add P n H v
  have h2:=cN_add P n (H+v) T
  have hpart:=addition_endable_partition f (n+H+v) T
  rw [count_A_run f (n+H+v) T hA] at hpart
  change F≤cN P n H at hhead
  change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hpart
  change j+1≤cN P n (H+v+T)
  simp only [Nat.add_assoc] at *
  omega

/-- The remaining small heads in the mass-one target branch reduce
internally to S7 and a tall initial S block. No finite head table is used.
Actual headfree3 plus lastfree2 pay the whole required gap. -/
theorem moment_mass_one_small_head_gap (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hzeroMass : M+L+U=h+m+s)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (B : Int) (haz : areaW (seg f n (h+M+m+L+s+U))= -B)
    (hlo : 4*((h+m+s : Nat) : Int)+6≤B) (hhi : B≤6*((h+m+s : Nat) : Int)+4)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
    (hS7 : h+m+s≤7) (htmass : mass (w.drop t)=1) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  · have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
    let H:=h+M+m+L+s+U
    let S:=h+m+s
    let z:=seg f n H
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hr:=moment_run_counter_residual f n t h M m L s U v T j q i w hw hpre ht hh hM hm hL hs hU hzeroMass
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 B haz hlo hhi hv hq hqv hi hband hgap htarget hlocal hpos hbad
    have hR : 5≤j+1 := by omega
    have hhead:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
    have hmz : mass z=0 := by
      simp only [z,H,hhead,mass_append,mass_rep_false,mass_replicate_A]
      omega
    have hSz : cntF z=S := by
      have hc:=mass_cntF z
      have hl : z.length=H := seg_length f n H
      rw [hmz,hl] at hc
      dsimp [H,S] at *
      omega
    have hc:=actual_moment_target_low_mass f n t H v T j q i w z hw hpre ht rfl hmz B haz
      (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv hq hqv hi hband
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [H,Nat.add_assoc] using htarget)
      (by simpa only [H,Nat.add_assoc] using hlocal) hR
    have hbalance:=hc.2.2.2.2.2
    rw [htmass] at hbalance
    have hv12 : v=1 ∨ v=2 := by omega
    have hkey:=actual_zero_mass_target_key f n t H v T j w z hpre ht rfl hmz B haz
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [H,Nat.add_assoc] using htarget)
    have hu : BlockWord (w.drop t) := block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
    have huA:=block_mass_one hu htmass
    have hkey0 : runKey (w.drop t)=0 := by rw [huA]; decide
    rw [hkey0,htmass,hSz] at hkey
    let I : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
    have hIpos : 0≤I := by
      have h1:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int) by omega)
      have h2:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int) by omega)
      dsimp [I]
      omega
    have hmom : B=(S : Int)^2-2*I := by
      have hmom:=three_head_moment h M m L s U hzeroMass B (by rw [←hhead]; exact haz)
      simpa only [I,S,Int.natCast_add] using hmom
    have hcases:=small_mass_one_numbers S v T j B I hS7 hv12 hR (by omega)
      (by grind only) (by have he:=hc.2.2.2.2.1; rw [hSz] at he; exact he) hmom hIpos
    obtain ⟨hSeven,hv2,hT6,hj4,hB39,hI5⟩:=hcases
    have hno:=actual_moment_no_old f n H t v T j w z hw hpre ht rfl hmz B haz
      (by rw [hSz]; exact hlo) (by rw [hSz]; exact hhi) hv hc.2.2.1 (by omega)
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [H,Nat.add_assoc] using htarget)
    have heq:=last_count_eq_local f n H v T z rfl
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4) hno
    have hheight:=seven_head_initial_height h M m L s U hh hM hm hL hs hU hSeven
      (by dsimp [S] at hSeven; omega) hI5
    have hlc:=two_gap_tall_initial_local_four h M m L s U 6 hzeroMass hheight.2 B
      (by rw [←hhead]; exact haz)
      (by rw [←hhead]; change 3≤cntF z; rw [hSz]; dsimp [S]; omega)
      (by rw [←hhead]; change 4*(cntF z : Int)+6≤B; rw [hSz]; exact hlo)
      (by rw [←hhead]; change B≤6*(cntF z : Int)+4; rw [hSz]; exact hhi)
    have hlocal4 : rayCount (z++List.replicate v false) T≤4 := by
      rw [hv2,hT6]
      simpa only [z,H,hhead,List.append_assoc] using hlc
    have hlast : cN (EndN f 0) (n+H+v) T≤4 := by rw [heq]; exact hlocal4
    have hAcount : cN (fun x=>f x=true) n H=7 := by
      have ha:=ones_seg_eq_count f n H
      change ones (seg f n (h+M+m+L+s+U))=_ at ha
      rw [hhead] at ha
      simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
      dsimp [S] at hSeven
      omega
    have hF3 : 3≤cN P n H := by
      by_cases hf : cN P n H≤2
      · have hpre0 : seg f 0 n=w++List.replicate 0 true := by simpa using hpre
        have hb:=positive_r3_additions_free_bound f n 0 H hw hpre0
          (fun k hk hkH=>hpos k hk (by dsimp [H] at *; omega)) (by change cN P n H≤3; omega)
        change cN (fun x=>f x=true) n H≤2*cN P n H+1 at hb
        rw [hAcount] at hb
        omega
      · omega
    exact actual_count_payment f n H v T j 3 4 hF3 hlast (by omega)
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4)

end Recaman.MomentMassOneSmall
