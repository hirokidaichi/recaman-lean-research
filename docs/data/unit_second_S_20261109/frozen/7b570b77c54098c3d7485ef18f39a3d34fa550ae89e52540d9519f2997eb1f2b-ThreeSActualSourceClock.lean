import Recaman.ThreeSSelectedSource

namespace Recaman.ThreeSActualSourceClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.AdjacentRunSupply

theorem counter_same_S_source_excluded (f : Nat → Bool) (n h M m L s U v T j i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hM : 1≤M) (hL : 1≤L) (hU : 1≤U) (hT : 1≤T) (hm : 3≤m) (hs : 1≤s) (hv : 1≤v)
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
    (htarget : Win f (n+h+M+m-3) (3+L+s+U+v+T+j))
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1)
    (hsource : Recaman.FourthSourceFamilies.sourceAt false m
      (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) i) : False
 := by
  let H:=h+M+m+L+s+U
  let B:=H+v
  let A:=cN (fun x=>f x=true) n (B+T)
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let F:=cN P n (B+T)
  let r:=cN P n H
  let EH:=cN (EndN f 0) n H
  let E:=cN (EndN f 0) (n+B) T
  obtain ⟨hbal,hstrict,hsq⟩:=Recaman.SecondSTargetProfile.actual_second_S_target_profile
    f (n+h+M) m L s U v T j (n+h+M+m-3) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-3)=3+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-3)=3 by omega] at hbal hstrict hsq
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
  have hF4 : 4≤F := by
    by_cases he : F≤3
    · have hb:=positive_r3_additions_free_bound f n 0 (B+T) hw
        (by simpa only [List.replicate_zero,List.append_nil] using hpre)
        (fun k hk hkB=>hpos k hk (by dsimp [B,H] at hkB; omega)) he
      change A≤2*F+1 at hb
      omega
    · omega


  have h16 : M+3+s+v≤16 := by omega
  have hz12 : s+v≤12 := by omega
  have hR5 : 5≤j+1 := by omega
  have hk:=Recaman.UnitSActualLastBudget.actual_second_S_target_key
    f (n+h+M) m L s U v T j (n+h+M+m-3) (by omega) (by omega) hL hs
      hS2 hA2 hS3 hA3 hS4 hA4 hgap
        (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-3)=3+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-3)=3 by omega] at hk
  let x:=List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hFx : cntF x=s+v := by
    simp only [x,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A,Nat.add_zero,Nat.zero_add]
  obtain ⟨k,hk1,hkm,hmass,hkey⟩:=hsource
  obtain ⟨hkone,hbands⟩:=Recaman.ThreeSSelectedSource.same_S_depth_spectrum x (j+1) k hk1 hR5
    (by omega) (by simpa only [x,List.append_assoc,Int.natCast_add,Int.natCast_one] using hk) hkey
  rw [hkone] at hmass
  simp only [mass_append,mass_replicate_A,mass_rep_false] at hmass
  have hclock : T=i+(j+1)+1 := by omega
  have hwB:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v 0
    hS hA hS2 hA2 hS3 hA3 hS4 (by intro t ht; omega)
  simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hwB
  change seg f n B=_ at hwB
  have hA4B : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,H,Nat.add_assoc] using hA4
  have hUv:=Int.mul_pos (show 0<(U : Int) by omega) (show 0<(v : Int) by omega)
  rcases hbands with h5|h7
  · have hz : (s : Int)+(v : Int)=4 := by omega
    rw [show (3 : Int)+(s : Int)+(v : Int)=7 by omega,
      show (j : Int)+1=5 by omega,hz] at hsq
    have hL2 : L≤2 := by omega
    let y:=List.replicate U true++List.replicate v false
    have htail : rayCount y T≤1 := rayCount_A_S_le_one U v T hv
    have htr:=Recaman.MixedThreeFamilyBudget.actual_prefix_two_saving f n B T m L s
      [(false,h),(true,M)] y w hw hpre
      (by simpa only [y,runWord,List.append_nil,List.append_assoc] using hwB)
      (by omega) hs (by simp only [y,cntF_append,Recaman.UnitTargetSASProfile.cntF_A,cntF_replicate_S]; omega)
      (by omega) hA4B
    have hE5 : E≤5 := by
      simp only [List.length_cons,List.length_nil] at htr
      change E≤2+2+rayCount y T at htr
      omega
    have hr3 : r≤3 := by omega
    have hsmall:=hrsmall hr3
    have hM1 : M≤1 := by omega
    obtain ⟨_,h4⟩:=Recaman.MixedShortAPairBudget.actual_fourth_bounds f n B T h M m L s U v w hw hpre
      hwB (by omega) hs hv (by omega) (by omega) hA4B
    have hE4 : E≤4 := h4 (by omega)
    omega
  · have hz : (s : Int)+(v : Int)=10 := by omega
    rw [show (3 : Int)+(s : Int)+(v : Int)=13 by omega,
      show (j : Int)+1=7 by omega,hz] at hsq
    have hL5 : L≤5 := by omega
    obtain ⟨h5',_⟩:=Recaman.MixedShortAPairBudget.actual_fourth_bounds f n B T h M m L s U v w hw hpre
      hwB (by omega) hs hv (by omega) (by omega) hA4B
    have hE5 : E≤5 := h5'
    have hr3 : r≤3 := by omega
    have hsmall:=hrsmall hr3
    omega

end Recaman.ThreeSActualSourceClock
