import Recaman.SecondAStartRayBudget
import Recaman.FourMeasuredCounts

namespace Recaman.SecondAStartCounterBand

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- A new whole-A target source exclusion supplies the strict counter
band before any short-prefix bootstrap. Earlier history is unchanged. -/
theorem second_A_start_counter_band (f : Nat → Bool) (n h M m L s U v T j : Nat)
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
    (htarget : Win f (n+h+M+m) (L+s+U+v+T+j))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    let D:=s+v-L
    6≤D ∧ D≤11 ∧ 5≤j+1 ∧ j+1≤10 ∧ s+v≤13 ∧ M≤7 ∧ L≤6 ∧
      T+U≤21 ∧ M+L+U+T≤24 ∧ M+L+D≤14 ∧ (L≤3 → M+L+D≤13) := by
  dsimp only
  let D:=s+v-L
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨ha1,haL,hp,hbal,hRD,hLD,hsq⟩:=Recaman.SecondATargetProfile.actual_second_A_profile
    f (n+h+M+m) L s U v T j (n+h+M+m) (by omega) (by omega) hs hU hv
      hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m)=L+s+U+v+T+j by omega]; exact htarget)
  have haeq : n+h+M+m+L-(n+h+M+m)=L := by omega
  rw [haeq] at hp hbal hRD hLD
  change s+v=L+D at hp
  change T+U=j+1+D at hbal
  change j+1<D at hRD
  change L<D at hLD
  clear ha1 haL hsq
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
  have hE6 : E≤6 := by
    have he:=Recaman.SecondAStartRayBudget.actual_start_six f n h M m L s U v T j w hw hpre
      hL hU hm hs hv (by omega) hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget
    simpa only [E,B,H,Nat.add_assoc] using he
  have h15 : M+L+D≤15 := by omega
  have hM8 : M≤8 := by omega
  have hL8 : L≤8 := by omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by
    simpa only [B,H,Nat.add_assoc] using hA4
  have hword' : seg f n B=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false := by
    simpa only [List.append_assoc] using hword
  obtain ⟨hE5,hE4⟩:=Recaman.MixedShortAPairBudget.actual_fourth_bounds
    f n B T h M m L s U v w hw hpre hword' hm hs hv hM8 hL8 hA4'
  change E≤5 at hE5
  change L≤3 → E≤4 at hE4
  have h14 : M+L+D≤14 := by omega
  have h13 : L≤3 → M+L+D≤13 := by intro hL3; have he:=hE4 hL3; omega
  have hD11 : D≤11 := by
    by_cases hL3 : L≤3
    · have hh:=h13 hL3
      omega
    · omega
  change 6≤D ∧ D≤11 ∧ 5≤j+1 ∧ j+1≤10 ∧ s+v≤13 ∧ M≤7 ∧ L≤6 ∧
      T+U≤21 ∧ M+L+U+T≤24 ∧ M+L+D≤14 ∧ (L≤3 → M+L+D≤13)
  exact ⟨hD6,hD11,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,h14,h13⟩

end Recaman.SecondAStartCounterBand
