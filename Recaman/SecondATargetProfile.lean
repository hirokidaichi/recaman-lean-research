import Recaman.FourShortPrefixBounds
import Recaman.ThreeRunSourceShape

namespace Recaman.SecondATargetProfile

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- The existing three-run first-A identity at the same actual target.
No earlier prefix is reset into a BlockWord. -/
theorem actual_second_A_profile (f : Nat → Bool) (b L s U v T j t : Nat)
    (hta : b≤t) (htb : t<b+L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hA0 : ∀ i, i<L → f (b+i)=true)
    (hS0 : ∀ x, b+L≤x → x<b+L+s → f x=false)
    (hAU : ∀ i, i<U → f (b+L+s+i)=true)
    (hS : ∀ x, b+L+s+U≤x → x<b+L+s+U+v → f x=false)
    (hAT : ∀ i, i<T → f (b+L+s+U+v+i)=true)
    (hgap : ∀ x, b+L+s+U+v+T≤x → x<b+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (b+L+s+U+v+T+j-t)) :
    let a:=b+L-t
    let D:=s+v-a
    1≤a ∧ a≤L ∧ s+v=a+D ∧ T+U=j+1+D ∧ j+1<D ∧ a<D ∧
      (D : Int)^2=((j : Int)+1)^2+(a : Int)^2+2*(U : Int)*(v : Int) := by
  dsimp only
  let a:=b+L-t
  let D:=s+v-a
  have ha1 : 1≤a := by dsimp [a]; omega
  have haend : t+a=b+L := by dsimp [a]; omega
  have hAa : seg f t a=List.replicate a true := by
    apply seg_A
    intro x hx hxa
    have he:=hA0 (x-b) (by omega)
    rwa [Nat.add_sub_cancel' (show b≤x by omega)] at he
  have hAU' : seg f (b+L+s) U=List.replicate U true := by
    apply seg_A
    intro x hx hxU
    have he:=hAU (x-(b+L+s)) (by omega)
    rwa [Nat.add_sub_cancel' hx] at he
  have hAT' : seg f (b+L+s+U+v) T=List.replicate T true := by
    apply seg_A
    intro x hx hxT
    have he:=hAT (x-(b+L+s+U+v)) (by omega)
    rwa [Nat.add_sub_cancel' hx] at he
  have hword : seg f t (b+L+s+U+v+T+j-t)=List.replicate a true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false := by
    rw [show b+L+s+U+v+T+j-t=a+s+U+v+T+j by omega,
      seg_add,seg_add,seg_add,seg_add,seg_add,haend,
      show t+(a+s)=b+L+s by omega,show t+(a+s+U)=b+L+s+U by omega,
      show t+(a+s+U+v)=b+L+s+U+v by omega,
      show t+(a+s+U+v+T)=b+L+s+U+v+T by omega,hAa,
      seg_false f (b+L) s hS0,hAU',seg_false f (b+L+s+U) v hS,hAT',
      seg_false f (b+L+s+U+v+T) j hgap]
  have hm : mass (List.replicate a true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hword,seg_mass]
    have he:=htarget.2.1
    rw [show t+(b+L+s+U+v+T+j-t)=b+L+s+U+v+T+j by omega] at he ⊢
    omega
  have ha : areaW (List.replicate a true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hword,←Ar_areaW]
    exact htarget.2.2
  obtain ⟨hbal,hkey,_⟩:=Recaman.ThreeRunSourceShape.first_A_target_equations a s U v T j ha1 hs hm ha
  have hlater:=Recaman.ThreeRunSourceShape.first_A_target_later_A a s U v T j ha1 hs hm ha
  have hp : s+v=a+D := by dsimp [D]; omega
  have hp' : (s : Int)+(v : Int)=(a : Int)+(D : Int) := by omega
  have hsq : (D : Int)^2=((j : Int)+1)^2+(a : Int)^2+2*(U : Int)*(v : Int) := by
    rw [hp'] at hkey
    grind only
  have haD : a<D := by
    by_cases he : a<D
    · exact he
    · have hl:=Recaman.ShortCounterFactorBounds.square_lower (a : Int) (D : Int) (by omega) (by omega)
      have hr:=Recaman.ShortCounterFactorBounds.square_lower ((j : Int)+1) 1 (by decide) (by omega)
      have hu:=Int.mul_pos (show 0<(U : Int) by omega) (show 0<(v : Int) by omega)
      grind only
  change 1≤a ∧ a≤L ∧ s+v=a+D ∧ T+U=j+1+D ∧ j+1<D ∧ a<D ∧ _
  exact ⟨ha1,by dsimp [a]; omega,hp,by omega,by omega,haD,hsq⟩

end Recaman.SecondATargetProfile
