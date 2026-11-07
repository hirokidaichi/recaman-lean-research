import Recaman.ThirdSTargetParity
import Recaman.FourRunSupplySeventeen

namespace Recaman.ThirdSUnitLastBudget

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ThirdSeparatorClock

/-- The same target removes the unit A family; the two remaining S
families have one common clock and the terminal pair has clock two. -/
theorem suffix_two (m s U v K q R : Nat) (hv : 1≤v)
    (htarget : ((q : Int)+(v : Int))^2=(R : Int)^2+2*(U : Int)*(v : Int)) :
    rayCount (List.replicate m false++List.replicate 1 true++List.replicate s false++
      List.replicate U true++List.replicate v false) K≤2 := by
  let PS:=fun i=>sourceAt false m (List.replicate 1 true++List.replicate s false++
      List.replicate U true++List.replicate v false) i ∨
      sourceAt false s (List.replicate U true++List.replicate v false) i
  have hPS : cN PS 0 K≤1 := Recaman.SeparatedSActualBudget.paired_S_count_four m 1 s U v K (by decide) hv
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho:=cN_or_le PS (fun i=>i=2) K
  have hle : rayCount (List.replicate m false++List.replicate 1 true++List.replicate s false++
      List.replicate U true++List.replicate v false) K≤cN (fun i=>PS i ∨ i=2) 0 K := by
    unfold rayCount
    apply cN_mono
    intro i hi hik he
    have he' : Recaman.ThreeNonsuppliedData.localSupply
        ((List.replicate m false++(List.replicate 1 true++List.replicate s false++
          List.replicate U true++List.replicate v false))++List.replicate i true)=true := by
      simpa only [List.append_assoc] using he
    rcases (local_const_split false m _ i).mp he' with hm|hl
    · exact Or.inl (Or.inl hm)
    · have hl' : Recaman.ThreeNonsuppliedData.localSupply
          ((List.replicate 1 true++(List.replicate s false++
            (List.replicate U true++List.replicate v false)))++List.replicate i true)=true := by
        simpa only [List.append_assoc] using hl
      rcases second_A_or_third_separator_or_pair 1 s U v i hv hl' with ha|hs|hc
      · exact False.elim (Recaman.ThirdSTargetParity.unit_A_source_excluded q R s U v i htarget ha)
      · exact Or.inl (Or.inr hs)
      · exact Or.inr hc
  omega

theorem actual_five_from_profile (f : Nat → Bool) (n B T h M m s U v q R : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hword : seg f n B=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate 1 true++List.replicate s false++List.replicate U true++List.replicate v false)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (htarget : ((q : Int)+(v : Int))^2=(R : Int)^2+2*(U : Int)*(v : Int))
    (hA : ∀ i, i<T → f (n+B+i)=true) : cN (EndN f 0) (n+B) T≤5 := by
  let y:=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate 1 true++List.replicate s false++List.replicate U true++List.replicate v false
  have hy : 3≤cntF y := by
    simp only [y,cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    omega
  have he:=(Recaman.MixedFinalRayOldBudget.actual_mixed_ray_old_budget f n B T w y
    hw hpre hword hy hA).1
  have hp:=run_prefix_ray_budget [(false,h),(true,M)]
    (List.replicate m false++List.replicate 1 true++List.replicate s false++
      List.replicate U true++List.replicate v false) T
  have hb:=suffix_two m s U v T q R hv htarget
  simp only [runWord,List.length_cons,List.length_nil,List.append_nil,Nat.reduceAdd,
    List.append_assoc] at hp
  simp only [List.append_assoc] at hb he
  dsimp [y] at he
  simp only [List.append_assoc] at he
  simp only [show List.replicate 1 true=[true] from rfl] at hp hb
  omega

/-- The original actual third-S target internally supplies its profile;
no scalar target conclusion or source family is an extra assumption. -/
theorem actual_third_S_five (f : Nat → Bool) (n t h M m s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ i, i<M → f (n+h+i)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ i, i<1 → f (n+h+M+m+i)=true)
    (hS3 : ∀ x, n+h+M+m+1≤x → x<n+h+M+m+1+s → f x=false)
    (hA3 : ∀ i, i<U → f (n+h+M+m+1+s+i)=true)
    (hS4 : ∀ x, n+h+M+m+1+s+U≤x → x<n+h+M+m+1+s+U+v → f x=false)
    (hA4 : ∀ i, i<T → f (n+h+M+m+1+s+U+v+i)=true)
    (hgap : ∀ x, n+h+M+m+1+s+U+v+T≤x → x<n+h+M+m+1+s+U+v+T+j → f x=false)
    (hta : n+h+M+m+1≤t) (htb : t<n+h+M+m+1+s)
    (htarget : Win f t (n+h+M+m+1+s+U+v+T+j-t)) :
    cN (EndN f 0) (n+h+M+m+1+s+U+v) T≤5 := by
  obtain ⟨_,hsq⟩:=Recaman.ThirdSTargetProfile.actual_third_S_target_profile
    f (n+h+M+m+1) s U v T j t hta htb hS3 hA3 hS4 hA4 hgap htarget
  have hword:=Recaman.FourRunSupplySeventeen.four_run_word f n h M m 1 s U v 0
    hS hA hS2 hA2 hS3 hA3 hS4 (by intro i hi; omega)
  simp only [Nat.add_zero,List.replicate_zero,List.append_nil] at hword
  have hA4' : ∀ i, i<T → f (n+(h+M+m+1+s+U+v)+i)=true := by
    simpa only [Nat.add_assoc] using hA4
  have he:=actual_five_from_profile f n (h+M+m+1+s+U+v) T h M m s U v
    (n+h+M+m+1+s-t) (j+1) w hw hpre hword hm hs hv
      (by simpa only [Int.natCast_add,Int.natCast_one] using hsq) hA4'
  simpa only [Nat.add_assoc] using he

end Recaman.ThirdSUnitLastBudget
