import Recaman.WholeATargetSourceCut
import Recaman.FourRunSupplySeventeen

namespace Recaman.SecondAStartRayBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies

/-- The actual target at the second A start internally removes that
source family; every old supplier is retained in the six-clock count. -/
theorem actual_start_six (f : Nat → Bool) (n h M m L s U v T j : Nat)
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
    (htarget : Win f (n+h+M+m) (L+s+U+v+T+j)) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤6 := by
  let B:=h+M+m+L+s+U+v
  let x:=List.replicate s false++(List.replicate U true++List.replicate v false)
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
    List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
  have hno:=Recaman.WholeATargetSourceCut.actual_start_excludes_source f (n+h+M+m) L s U v T j
    hL hs hU hv hj hA2 hS3 hA3 hS4 hA4 hgap htarget
  have hmid : rayCount (List.replicate L true++x) T≤rayCount x T := by
    unfold rayCount
    apply cN_mono
    intro i hi hiT he
    rcases (local_const_split true L x i).mp he with ha|hx
    · exact False.elim (hno i ha)
    · exact hx
  have hxS:=rayCount_const_append false s (List.replicate U true++List.replicate v false) T
  have hxA:=rayCount_A_S_le_one U v T hv
  have hx : rayCount x T≤2 := by change rayCount x T≤1+_ at hxS; omega
  have hp:=run_prefix_ray_budget [(false,h),(true,M),(false,m)] (List.replicate L true++x) T
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

end Recaman.SecondAStartRayBudget
