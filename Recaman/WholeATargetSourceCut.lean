import Recaman.SecondATargetProfile

namespace Recaman.WholeATargetSourceCut

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.AdjacentRunSupply Recaman.FourthSourceFamilies Recaman.ShortCounterFactorBounds

/-- A target using the entire A interval has a more negative square key
than every primitive supplier starting inside that same interval. -/
theorem whole_A_target_excludes_source (x : List Bool) (L R i : Nat) (hR : 2≤R)
    (htarget : runKey (List.replicate L true++x)= -2*(R : Int)^2) :
    ¬sourceAt true L x i := by
  rintro ⟨a,ha,haL,_,hk⟩
  rw [runKey_prepend_A] at hk htarget
  have hp:=Int.mul_nonneg (show 0≤(L : Int)-(a : Int) by omega) (show 0≤(cntF x : Int) by omega)
  have hr:=square_lower (R : Int) 2 (by decide) (by omega)
  grind only

/-- This source exclusion is supplied from the same actual whole-second-A
window, without assuming its key or changing its starting position. -/
theorem actual_start_excludes_source (f : Nat → Bool) (b L s U v T j : Nat)
    (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hj : 1≤j)
    (hA0 : ∀ i, i<L → f (b+i)=true)
    (hS0 : ∀ x, b+L≤x → x<b+L+s → f x=false)
    (hAU : ∀ i, i<U → f (b+L+s+i)=true)
    (hS : ∀ x, b+L+s+U≤x → x<b+L+s+U+v → f x=false)
    (hAT : ∀ i, i<T → f (b+L+s+U+v+i)=true)
    (hgap : ∀ x, b+L+s+U+v+T≤x → x<b+L+s+U+v+T+j → f x=false)
    (htarget : Win f b (L+s+U+v+T+j)) :
    ∀ i, ¬sourceAt true L (List.replicate s false++
      (List.replicate U true++List.replicate v false)) i := by
  obtain ⟨ha1,haL,hp,hbal,hRD,haD,hsq⟩:=Recaman.SecondATargetProfile.actual_second_A_profile
    f b L s U v T j b (by omega) (by omega) hs hU hv hA0 hS0 hAU hS hAT hgap
      (by simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using htarget)
  have haeq : b+L-b=L := by omega
  rw [haeq] at hp hsq
  have hpi : (s : Int)+(v : Int)=(L : Int)+((s+v-L : Nat) : Int) := by omega
  have hk : runKey (List.replicate L true++(List.replicate s false++
      (List.replicate U true++List.replicate v false)))= -2*((j : Int)+1)^2 := by
    rw [runKey_prepend_A,←List.append_assoc,runKey_S_A_S]
    simp only [cntF_append,cntF_replicate_S,Recaman.UnitTargetSASProfile.cntF_A]
    grind only
  intro i
  exact whole_A_target_excludes_source _ L (j+1) i (by omega)
    (by simpa only [Int.natCast_add,Int.natCast_one] using hk)

/-- R1 can share the whole A source at its endpoint; it is outside the
strict-past count when the appended A length equals that source clock. -/
theorem unit_R_control :
    runKey (List.replicate 1 true++(List.replicate 2 false++
      (List.replicate 1 true++List.replicate 1 false)))= -2 ∧
    sourceAt true 1 (List.replicate 2 false++
      (List.replicate 1 true++List.replicate 1 false)) 2 := by
  exact ⟨by decide,⟨1,by decide,by decide,by decide,by decide⟩⟩

end Recaman.WholeATargetSourceCut
