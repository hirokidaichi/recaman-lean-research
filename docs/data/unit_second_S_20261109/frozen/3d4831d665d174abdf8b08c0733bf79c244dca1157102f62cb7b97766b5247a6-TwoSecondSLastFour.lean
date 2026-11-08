import Recaman.TwoSActualSourceClock

namespace Recaman.TwoSecondSLastFour

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

theorem two_second_S_counter_last_four (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 2≤m) (hs : 1≤s) (hv : 1≤v)
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
    (htarget : Win f (n+h+M+m-2) (2+L+s+U+v+T+j))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤4
 := by
  obtain ⟨hM7,hL7,hz11,hR5,_,_⟩:=Recaman.TwoSecondSCounterCut.two_second_S_counter_cut
    f n h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
  let B:=h+M+m+L+s+U+v
  let x:=List.replicate s false++(List.replicate U true++List.replicate v false)
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hk:=Recaman.UnitSActualLastBudget.actual_second_S_target_key
    f (n+h+M) m L s U v T j (n+h+M+m-2) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-2)=1+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-2)=2 by omega] at hk
  have hFx : cntF x≤13 := by
    simp only [x,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.zero_add]
    omega
  have hSsave:=Recaman.TwoSSelectedSource.same_S_prefix_saving
    (List.replicate L true++x) m (j+1) T hR5 (by
      simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,Nat.zero_add]
      exact hFx)
    (by simpa only [x,List.append_assoc,Int.natCast_add,Int.natCast_one] using hk)
  have hAsave : rayCount (List.replicate L true++x) T≤rayCount x T := by
    unfold rayCount
    apply cN_mono
    intro i hi hiT he
    rcases (Recaman.FourthSourceFamilies.local_const_split true L x i).mp he with ha|hx
    · exact False.elim (Recaman.TwoSActualSourceClock.counter_next_A_source_excluded
        f n h M m L s U v T j i w hw hpre hM hL hU hT hm hs hv
          hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad ha)
    · exact hx
  have hmid : rayCount (List.replicate m false++(List.replicate L true++x)) T≤rayCount x T := by omega
  have hp:=Recaman.MixedShortAPairBudget.pair_prefix_saving
    (List.replicate m false++(List.replicate L true++x)) h M T (by omega)
  have hxS:=rayCount_const_append false s (List.replicate U true++List.replicate v false) T
  have hxA:=rayCount_A_S_le_one U v T hv
  have hy : rayCount y T≤3 := by
    simp only [x,y,List.append_assoc] at hmid hp hxS ⊢
    omega
  have hword:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v 0
    hS hA hS2 hA2 hS3 hA3 hS4 (by intro i hi; omega)
  simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hword
  have hw' : seg f n B=y := by simpa only [B,y] using hword
  have hcnt : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,Nat.add_assoc] using hA4
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hw' hcnt hA4').1
  have he : cN (EndN f 0) (n+B) T≤4 := by omega
  simpa only [B,Nat.add_assoc] using he

end Recaman.TwoSecondSLastFour
