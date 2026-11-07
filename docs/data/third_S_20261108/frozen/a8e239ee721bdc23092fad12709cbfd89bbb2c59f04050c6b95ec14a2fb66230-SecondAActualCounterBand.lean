import Recaman.SecondATargetProfile
import Recaman.FourMeasuredCounts
import Recaman.FourRunSupplySeventeen

namespace Recaman.SecondAActualCounterBand

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A second-A actual counter stays in a strict scalar band while the
whole original old prefix and the source before the target are retained. -/
theorem second_A_actual_counter_band (f : Nat → Bool) (n t h M m L s U v T j : Nat)
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
    (hta : n+h+M+m≤t) (htb : t<n+h+M+m+L)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    let a:=n+h+M+m+L-t
    let D:=s+v-a
    1≤a ∧ a≤L ∧ 6≤D ∧ D≤11 ∧ 5≤j+1 ∧ j+1≤10 ∧ s+v≤13 ∧ M≤7 ∧ L≤7 ∧
      T+U≤21 ∧ M+L+U+T≤24 ∧ M+L+D≤14 ∧ (L≤3 → M+L+D≤13) := by
  dsimp only
  let a:=n+h+M+m+L-t
  let D:=s+v-a
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨ha1,haL,hp,hbal,hRD,haD,hsq⟩:=Recaman.SecondATargetProfile.actual_second_A_profile
    f (n+h+M+m) L s U v T j t hta htb hs hU hv hA2 hS3 hA3 hS4 hA4 hgap htarget
  change 1≤a at ha1
  change a≤L at haL
  change s+v=a+D at hp
  change T+U=j+1+D at hbal
  change j+1<D at hRD
  change a<D at haD
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
  have hD6 : 6≤D := by omega
  have h16 : M+L+D≤16 := by omega
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
    by_cases he : M≤8
    · exact he
    · have hb:=hsecond (by omega)
      omega
  have hL8 : L≤8 := by
    by_cases he : L≤8
    · exact he
    · have hb:=hfirst (by omega)
      omega
  obtain ⟨hE5,hE4⟩:=Recaman.MixedShortAPairBudget.actual_fourth_bounds
    f n B T h M m L s U v w hw hpre hword' hm hs hv hM8 hL8 hA4'
  change E≤5 at hE5
  change L≤3 → E≤4 at hE4
  have h14 : M+L+D≤14 := by omega
  have h13 : L≤3 → M+L+D≤13 := by intro hL3; have he:=hE4 hL3; omega
  have hr4 : 4≤r := by
    by_cases he : r≤3
    · have hh:=hrsmall he
      by_cases hL3 : L≤3
      · have he4:=hE4 hL3
        omega
      · omega
    · omega
  have hD11 : D≤11 := by
    by_cases hL3 : L≤3
    · have hh:=h13 hL3
      omega
    · omega
  change 1≤a ∧ a≤L ∧ 6≤D ∧ D≤11 ∧ 5≤j+1 ∧ j+1≤10 ∧ s+v≤13 ∧ M≤7 ∧ L≤7 ∧
      T+U≤21 ∧ M+L+U+T≤24 ∧ M+L+D≤14 ∧ (L≤3 → M+L+D≤13)
  exact ⟨ha1,haL,hD6,hD11,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,h14,h13⟩

end Recaman.SecondAActualCounterBand
