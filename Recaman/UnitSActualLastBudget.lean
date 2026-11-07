import Recaman.UnitSSelectedSource

namespace Recaman.UnitSActualLastBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

theorem actual_second_S_target_key (f : Nat → Bool) (b m L s U v T j t : Nat)
    (hta : b≤t) (htb : t<b+m) (hL : 1≤L) (hs : 1≤s)
    (hS0 : ∀ x, b≤x → x<b+m → f x=false)
    (hA0 : ∀ i, i<L → f (b+m+i)=true)
    (hS : ∀ x, b+m+L≤x → x<b+m+L+s → f x=false)
    (hAU : ∀ i, i<U → f (b+m+L+s+i)=true)
    (hS4 : ∀ x, b+m+L+s+U≤x → x<b+m+L+s+U+v → f x=false)
    (hAT : ∀ i, i<T → f (b+m+L+s+U+v+i)=true)
    (hgap : ∀ x, b+m+L+s+U+v+T≤x → x<b+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (b+m+L+s+U+v+T+j-t)) :
    runKey (List.replicate (b+m-t) false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false)= -2*((j : Int)+1)^2 := by
  let q:=b+m-t
  have hqe : t+q=b+m := by dsimp [q]; omega
  have hword : seg f t (b+m+L+s+U+v+T+j-t)=
      List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false := by
    have hh:=Recaman.SeparatorSupplyReset.three_run_word f t q L s U v T
      (by intro x hx hxq; exact hS0 x (by omega) (by omega))
      (by simpa only [hqe] using hA0)
      (by simpa only [hqe,Nat.add_assoc] using hS)
      (by simpa only [hqe,Nat.add_assoc] using hAU)
      (by simpa only [hqe,Nat.add_assoc] using hS4)
      (by simpa only [hqe,Nat.add_assoc] using hAT)
    rw [show b+m+L+s+U+v+T+j-t=(q+L+s+U+v+T)+j by omega,seg_add,hh,
      show t+(q+L+s+U+v+T)=b+m+L+s+U+v+T by omega,
      seg_false f (b+m+L+s+U+v+T) j hgap]
  have hm : mass (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have he:=htarget.2.1
    rw [show t+(b+m+L+s+U+v+T+j-t)=b+m+L+s+U+v+T+j by omega] at he ⊢
    omega
  have ha : areaW (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  exact Recaman.ASourceReuse.source_key_before_gap
    (List.replicate q false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false) T j hm ha

theorem actual_second_S_unit_six (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hL : 1≤L) (hU : 1≤U) (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hj : 1≤j)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f (n+h+M+m-1) (1+L+s+U+v+T+j)) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤6 := by
  let B:=h+M+m+L+s+U+v
  let x:=List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hk:=actual_second_S_target_key f (n+h+M) m L s U v T j (n+h+M+m-1)
    (by omega) (by omega) hL hs hS2 hA2 hS3 hA3 hS4 hA4 hgap
      (by rw [show n+h+M+m+L+s+U+v+T+j-(n+h+M+m-1)=1+L+s+U+v+T+j by omega]; exact htarget)
  rw [show n+h+M+m-(n+h+M+m-1)=1 by omega] at hk
  change runKey (List.replicate 1 false++x)= -2*((j : Int)+1)^2 at hk
  have hmid:=Recaman.UnitSSelectedSource.unit_S_prefix_saving x m (j+1) T (by omega)
    (by simpa only [Int.natCast_add,Int.natCast_one] using hk)
  have hxs:=rayCount_const_append false s (List.replicate U true++List.replicate v false) T
  have hxa:=rayCount_A_S_le_one U v T hv
  have hxl:=rayCount_const_append true L
    (List.replicate s false++(List.replicate U true++List.replicate v false)) T
  have hx : rayCount x T≤3 := by
    simp only [x,List.append_assoc] at hxs hxl ⊢
    omega
  have hp:=run_prefix_ray_budget [(false,h),(true,M)] (List.replicate m false++x) T
  have hy : rayCount y T≤5 := by
    simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd] at hp
    simp only [y,x,List.append_assoc] at hp hmid hx ⊢
    omega
  have hword:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m L s U v 0
    hS hA hS2 hA2 hS3 hA3 hS4 (by intro i hi; omega)
  simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hword
  have hword' : seg f n B=y := by simpa only [B,y] using hword
  have hcnt : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have hA4' : ∀ i, i<T → f (n+B+i)=true := by simpa only [B,Nat.add_assoc] using hA4
  have ho:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y hw hpre hword' hcnt hA4').1
  have he : cN (EndN f 0) (n+B) T≤6 := by omega
  simpa only [B,Nat.add_assoc] using he

end Recaman.UnitSActualLastBudget
