import Recaman.SecondSTargetProfile
import Recaman.FourMeasuredCounts
import Recaman.FourRunSupplySeventeen

namespace Recaman.SecondSActualCounterBand

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Same-target source/count saturation excludes M9 and strictly reduces
all second-S actual counters without bounding the old history. -/
theorem second_S_actual_counter_band (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
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
    (hta : n+h+M≤t) (htb : t<n+h+M+m)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    let q:=n+h+M+m-t
    M≤8 ∧ M+q+s+v≤15 ∧ 5≤j+1 ∧ j+1≤12 ∧ q+s+v≤14 := by
  dsimp only
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hbal,hstrict,hsq⟩:=Recaman.SecondSTargetProfile.actual_second_S_target_profile
    f (n+h+M) m L s U v T j t hta htb hL hs hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget
  generalize hqDef : n+h+M+m-t=q at hbal hstrict hsq
  have hq : 1≤q := by omega
  clear hqDef
  obtain ⟨hEH,hE,hcount,hfree,hrsmall,hword⟩:=
    Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
      hM hm hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
  change EH≤10 at hEH
  change E≤7 at hE
  change A=EH+E+F at hcount
  change T+r≤F+E at hfree
  change r≤3 → EH≤r+1 at hrsmall
  change F<j+1 at hbad
  have hET : E≤T := Recaman.ClockCountSaturation.count_le_length (EndN f 0) (n+B) T
  have hAeq : A=M+L+U+T := by
    have he:=ones_seg_eq_count f n (B+T)
    have hw' := Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v T
      hS hA hS2 hA2 hS3 hA3 hS4 hA4
    change seg f n (B+T)=_ at hw'
    rw [hw'] at he
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at he
    dsimp [A]
    omega
  have hF4 : 4≤F := by
    by_cases he : F≤3
    · have hb:=positive_r3_additions_free_bound f n 0 (B+T) hw
        (by simpa only [List.replicate_zero,List.append_nil] using hpre)
        (fun k hk hkB=>hpos k hk (by dsimp [B,H] at hkB; omega)) he
      change A≤2*F+1 at hb
      omega
    · omega
  have h16 : M+q+s+v≤16 := by omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by
    simpa only [B,H,Nat.add_assoc] using hA4
  have hword' : seg f n B=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false := by
    simpa only [List.append_assoc] using hword
  obtain ⟨hfirst,hsecond⟩:=Recaman.FourShortPrefixBounds.actual_one_short_bound
    f n B T h M m L s U v w hw hpre hword' hm hs hv hA4'
  change M≤8 → E≤6 at hfirst
  change L≤3 → E≤5 at hsecond
  have hM8 : M≤8 := by
    by_cases hh : M≤8
    · exact hh
    · have hM9 : M=9 := by omega
      have hp7 : q+s+v=7 := by omega
      have hR5 : j+1=5 := by omega
      have hE7 : E=7 := by omega
      have hF4' : F=4 := by omega
      have hEH10 : EH=10 := by omega
      have hr4 : 4≤r := by
        by_cases hr : r≤3
        · have he:=hrsmall hr
          omega
        · omega
      have hT7 : T=7 := by omega
      have hL4 : 4≤L := by
        by_cases he : L≤3
        · have hh:=hsecond he
          omega
        · omega
      have hL4' : L=4 := by omega
      have hU1 : U=1 := by omega
      have hpi : (q : Int)+(s : Int)+(v : Int)=7 := by omega
      have hri : (j : Int)+1=5 := by omega
      rw [hpi,hri,hL4',hU1] at hsq
      have he : 4*(s : Int)+5*(v : Int)=12 := by grind only
      omega
  have hE6:=hfirst hM8
  change M≤8 ∧ M+q+s+v≤15 ∧ 5≤j+1 ∧ j+1≤12 ∧ q+s+v≤14
  exact ⟨hM8,by omega,by omega,by omega,by omega⟩

end Recaman.SecondSActualCounterBand
