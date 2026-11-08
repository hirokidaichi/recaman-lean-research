import Recaman.TargetSSourceSquareOrder

namespace Recaman.TwoSecondSLastThree

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.AdjacentRunSupply

theorem two_second_S_counter_last_three (f : Nat → Bool) (n h M m L s U v T j : Nat)
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
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤3
 := by
  obtain ⟨hM7,hL7,hz11,hR5,hR11,h14⟩:=Recaman.TwoSecondSCounterCut.two_second_S_counter_cut
    f n h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hbal,hstrict,hsq⟩:=Recaman.SecondSTargetProfile.actual_second_S_target_profile
    f (n+h+M) m L s U v T j (n+h+M+m-2) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-2)=2+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-2)=2 by omega] at hbal hstrict hsq
  obtain ⟨hEH,hE,hcount,hfree,hrsmall,hword⟩:=
    Recaman.FourMeasuredCounts.measured_counts f n h M m L s U v T w hw hpre
      hM (by omega) hs hv hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos
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
  have hE4raw:=Recaman.TwoSecondSLastFour.two_second_S_counter_last_four
    f n h M m L s U v T j w hw hpre hM hL hU hT hm hs hv
      hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
  have hE4 : E≤4 := by simpa only [E,B,H,Nat.add_assoc] using hE4raw
  let D:=2+s+v-L
  have hDL : D+L=2+s+v := by dsimp [D]; omega
  have hbalance : T+U=j+1+D := by omega
  have hr4 : 4≤r := by
    by_cases hh : r≤3
    · have hb:=hrsmall hh
      omega
    · omega
  have hUfloor : D+1≤U := by omega
  have hDsq : (D : Int)^2=((j : Int)+1)^2+((L : Int)-2)^2-4+2*(U : Int)*(v : Int) := by
    have he : (D : Int)+(L : Int)=2+(s : Int)+(v : Int) := by omega
    grind only
  have hnoS (i : Nat) : ¬Recaman.FourthSourceFamilies.sourceAt false s
      (List.replicate U true++List.replicate v false) i :=
    Recaman.TargetSSourceSquareOrder.last_S_source_excluded 2 (L : Int) ((j : Int)+1) (D : Int)
      s U v i (by decide) (by omega) (by omega) (by omega) hDsq
  let x:=List.replicate s false++(List.replicate U true++List.replicate v false)
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hk:=Recaman.UnitSActualLastBudget.actual_second_S_target_key
    f (n+h+M) m L s U v T j (n+h+M+m-2) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-2)=2+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-2)=2 by omega] at hk
  have hFx : cntF x≤13 := by
    simp only [x,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have hSsave:=Recaman.TwoSSelectedSource.same_S_prefix_saving
    (List.replicate L true++x) m (j+1) T hR5 (by
      simp only [cntF_append,Recaman.UnitTargetSASProfile.cntF_A,Nat.zero_add]; exact hFx)
    (by simpa only [x,List.append_assoc,Int.natCast_add,Int.natCast_one] using hk)
  have hAsave : rayCount (List.replicate L true++x) T≤rayCount x T := by
    unfold rayCount
    apply cN_mono
    intro i hi hiT he
    rcases (Recaman.FourthSourceFamilies.local_const_split true L x i).mp he with ha|hx
    · exact False.elim (Recaman.TwoSActualSourceClock.counter_next_A_source_excluded
        f n h M m L s U v T j i w hw hpre hM hL hU hT hm hs hv
          hS hA hS2 hA2 hS3 hA3 hS4 hA4 hpos hgap htarget hbad
            (by simpa only [x,List.append_assoc] using ha))
    · exact hx
  have hlastS : rayCount x T≤rayCount (List.replicate U true++List.replicate v false) T := by
    unfold rayCount
    apply cN_mono
    intro i hi hiT he
    rcases (Recaman.FourthSourceFamilies.local_const_split false s _ i).mp he with hs'|hx
    · exact False.elim (hnoS i hs')
    · exact hx
  have hp:=Recaman.MixedShortAPairBudget.pair_prefix_saving
    (List.replicate m false++(List.replicate L true++x)) h M T (by omega)
  have htail:=rayCount_A_S_le_one U v T hv
  have hy : rayCount y T≤2 := by
    simp only [x,y,List.append_assoc] at hp hSsave hAsave hlastS ⊢
    omega
  have hwB : seg f n B=y := by simpa only [B,H,y,List.append_assoc] using hword
  have hcnt : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have hA4B : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hwB hcnt hA4B).1
  have he : E≤3 := by omega
  simpa only [E,B,H,Nat.add_assoc] using he

end Recaman.TwoSecondSLastThree
