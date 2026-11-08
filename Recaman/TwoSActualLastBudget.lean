import Recaman.TwoSSelectedSource

namespace Recaman.TwoSActualLastBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply

theorem actual_second_S_two_budgets (f : Nat → Bool) (n h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hL : 1≤L) (hU : 1≤U) (hm : 2≤m) (hs : 1≤s) (hv : 1≤v) (hR : 5≤j+1) (hF : s+v≤13)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<L → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+L+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+L+s+U+v+i)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f (n+h+M+m-2) (2+L+s+U+v+T+j)) :
    cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤6 ∧
      (M≤8 → cN (EndN f 0) (n+h+M+m+L+s+U+v) T≤5) := by
  let B:=h+M+m+L+s+U+v
  let x:=List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false
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
  have hmid:=Recaman.TwoSSelectedSource.same_S_prefix_saving x m (j+1) T hR hFx
    (by simpa only [x,List.append_assoc,Int.natCast_add,Int.natCast_one] using hk)
  have hxt:=rayCount_A_S_le_one U v T hv
  have hxp:=run_prefix_ray_budget [(true,L),(false,s)] (List.replicate U true++List.replicate v false) T
  have hx : rayCount x T≤3 := by
    simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,List.append_assoc,x] at hxp ⊢
    omega
  have hp:=run_prefix_ray_budget [(false,h),(true,M)] (List.replicate m false++x) T
  have hy : rayCount y T≤5 := by
    simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,List.append_assoc,x,y] at hp hmid hx ⊢
    omega
  have hyshort (hM : M≤8) : rayCount y T≤4 := by
    have hp:=Recaman.MixedShortAPairBudget.pair_prefix_saving (List.replicate m false++x) h M T hM
    simp only [x,y,List.append_assoc] at hp hmid hx ⊢
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
  constructor
  · have he : cN (EndN f 0) (n+B) T≤6 := by omega
    simpa only [B,Nat.add_assoc] using he
  · intro hM
    have hs:=hyshort hM
    have he : cN (EndN f 0) (n+B) T≤5 := by omega
    simpa only [B,Nat.add_assoc] using he

end Recaman.TwoSActualLastBudget
