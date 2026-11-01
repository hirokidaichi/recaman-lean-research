import Recaman.OldTargetMassCircle
import Recaman.FinalSSourceResidual

namespace Recaman.FinalSTargetWidth

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.RunSupplyBudget Recaman.FourRunSupplySeventeen Recaman.OldTargetMassCircle
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

private theorem small_circle_bounds (C R : Int) (hC : 0≤C) (hR : 5≤R)
    (h : C^2+R^2≤117) : C≤9 ∧ C+R≤15 := by
  have hrp:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hr2 : 25≤R^2 := by grind only
  have hc : C≤9 := by
    by_cases hh : C≤9
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-10 by omega) (show 0≤C+10 by omega)
      grind only
  have hs : C+R≤15 := by
    by_cases hh : C+R≤15
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C+R-16 by omega) (show 0≤C+R+16 by omega)
      have hd:=Int.sq_nonneg (C-R)
      grind only
  exact ⟨hc,hs⟩

private theorem large_circle_bounds (C R : Int) (hC : 0≤C) (hR : 5≤R)
    (h : C^2+(R+1)^2≤226) : C≤13 ∧ C+R≤20 := by
  have hrp:=Int.mul_nonneg (show 0≤R+1-6 by omega) (show 0≤R+1+6 by omega)
  have hr2 : 36≤(R+1)^2 := by grind only
  have hc : C≤13 := by
    by_cases hh : C≤13
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-14 by omega) (show 0≤C+14 by omega)
      grind only
  have hs : C+R≤20 := by
    by_cases hh : C+R≤20
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C+R+1-22 by omega) (show 0≤C+R+1+22 by omega)
      have hd:=Int.sq_nonneg (C-(R+1))
      grind only
  exact ⟨hc,hs⟩

/-- Bounds concern the SAME target old suffix/window only. Other old
sources and the original EndN base are retained in all actual counts. -/
theorem final_S_target_mass_width (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x => f x=false) n k)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (he : EndN f 0 (n+h+M+m+L+s+U+v+T+j))
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hlocal : Win f (n+h+M+m+L+s+U+v-q) (q+i))
    (hbad : cN (fun x => f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    1≤Fw f n-Fw f t ∧ Fw f n-Fw f t≤13 ∧
    n-t≤32 ∧ h+M+m+L+s+U+v+T+j≤64 ∧
    n+h+M+m+L+s+U+v+T+j-t≤96 := by
  let B:=h+M+m+L+s+U+v+T
  let C:=Fw f n-Fw f t
  let R:=(j : Int)+1
  let A:=M+L+U+T
  have hword:=four_run_word f n h M m L s U v T hS hA hS2 hA2 hS3 hA3 hS4 hA4
  have hnew:=Recaman.FourRunTargetArea.actual_final_S_source_A_budget
    f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hword hS4 hA4 hgap htarget hlocal
  have hold:=Recaman.FinalSSourceResidual.final_S_counterexample_band_twelve
    f n t h M m L s U v T j q i w hw hpre ht
    hM hm hL hs hU hv hq hqv hi hband hS hA hS2 hA2 hS3 hA3 hS4 hA4
    hpos hgap he htarget hlocal hbad
  have hp:=addition_endable_partition f n B
  have hE:=four_run_supply_le_seventeen f n h M m L s U v T
    w hw hpre hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  have hcount : cN (fun x=>f x=true) n B=A := by
    have ha:=ones_seg_eq_count f n B
    change ones (seg f n (h+M+m+L+s+U+v+T))=_ at ha
    rw [hword] at ha
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
    dsimp [A]
    omega
  have hbudget : A≤j+1+16 := by dsimp [B] at hp hcount; omega
  have hlen:=block_prefix_suffix_length_bound f n 0 t hw (by simpa only [List.replicate_zero,List.append_nil] using hpre) (by omega)
  have hC : 1≤C := by dsimp [C]; omega
  have hR : 5≤R := by dsimp [R]; omega
  have hcr : C≤13 ∧ C+R≤20 := by
    by_cases hML : j+1≤M+L
    · have hcir:=actual_large_prefix_mass_circle f n t h M m L s U v T j 16 w hw hpre ht
        hM hm hL hs hU hv (by omega) hML (by simpa only [A] using hbudget) hword hgap htarget
      have hcir' : C^2+(R+1)^2≤226 := by dsimp [C,R]; grind only
      exact large_circle_bounds C R (by omega) hR hcir'
    · have hEs:=Recaman.SmallPrefixSupplyThirteen.four_run_small_prefix_supply_le_thirteen
        f n t h M m L s U v T j w hw hpre ht (by omega) (by omega) (by omega)
        htarget hgap hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
      have hsbudget : A≤j+1+12 := by dsimp [B] at hp hcount; omega
      have hcir:=actual_target_mass_circle f n t h M m L s U v T j 12 w hw hpre ht
        hM hm hL hs hU hv (by omega) (by simpa only [A] using hsbudget) hword hgap htarget
      have hcir' : C^2+R^2≤117 := by dsimp [C,R]; grind only
      have hs:=small_circle_bounds C R (by omega) hR hcir'
      omega
  have hfull : seg f n (B+j)=seg f n B++List.replicate j false := by
    rw [seg_add]
    have hh : seg f (n+B) j=List.replicate j false := by
      apply seg_false
      intro x hx hxb
      exact hgap x (by dsimp [B] at *; omega) (by dsimp [B] at *; omega)
    rw [hh]
  have hones : ones (seg f n (B+j))=(A : Int) := by
    rw [hfull,ones_append,ones_replicate_S]
    have hc:=ones_seg_eq_count f n B
    rw [hcount] at hc
    omega
  have hmfull:=mass_eq (seg f n (B+j))
  rw [seg_mass,seg_length,hones] at hmfull
  have hwm:=htarget.2.1
  have hlength : (B+j : Int)=2*(A : Int)+C-1 := by
    rw [show t+(n+h+M+m+L+s+U+v+T+j-t)=n+B+j by dsimp [B]; omega] at hwm
    dsimp [C]
    omega
  have htlen : B+j≤64 := by dsimp [R] at hcr; omega
  have hsource : n-t≤32 := by dsimp [C] at hcr; omega
  refine ⟨hC,hcr.1,hsource,?_,?_⟩ <;> dsimp [B] at * <;> omega

end Recaman.FinalSTargetWidth
