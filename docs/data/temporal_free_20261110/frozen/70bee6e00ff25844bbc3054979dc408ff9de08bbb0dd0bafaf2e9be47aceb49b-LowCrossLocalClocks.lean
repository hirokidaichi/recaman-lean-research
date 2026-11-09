import Recaman.OldMassEndpointGate

namespace Recaman.LowCrossLocalClocks

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.BlockOldRay
open Recaman.RunSupplyKeys Recaman.CapacityEqualityInduction

def cross (x : List Bool) : Int := runKey x+2*(cntF x : Int)^2

theorem cross_nonnegative (x : List Bool) : 0≤cross x := by
  have h:=runKey_count_lower x
  unfold cross
  omega

theorem cross_append (x y : List Bool) :
    cross (x++y)=cross x+cross y+4*ones x*(cntF y : Int) := by
  unfold cross
  have h:=Recaman.SourceCrossSurplus.cross_append x y
  omega

theorem cross_at_addition (x z : List Bool) :
    cross (x++[true]++z)=cross x+cross z+4*(ones x+1)*(cntF z : Int) := by
  rw [cross_append,cross_append,ones_append]
  have hc : cross [true]=0 := by decide
  have hf : cntF [true]=0 := by decide
  have ha : ones [true]=1 := by decide
  rw [hc,hf,ha]
  grind only

theorem cross_zero_of_no_A (x : List Bool) (ha : ones x=0) : cross x=0 := by
  have hu:=Recaman.PrimitiveClockRadius.cross_upper x
  change cross x≤4*ones x*(cntF x : Int) at hu
  rw [ha] at hu
  have hl:=cross_nonnegative x
  omega

theorem cross_zero_of_no_S (x : List Bool) (hs : cntF x=0) : cross x=0 := by
  have hu:=Recaman.PrimitiveClockRadius.cross_upper x
  change cross x≤4*ones x*(cntF x : Int) at hu
  rw [hs] at hu
  have hl:=cross_nonnegative x
  omega

private theorem small_cross_arith (q qp qz a m s : Int)
    (hQ : q≤20) (hOdd : q%8=4) (hqp : 0≤qp) (hqz : 0≤qz)
    (ha : 0≤a) (hs : 0≤s) (hm : 1≤m) (hmod : m%2=1)
    (h0p : a=0 → qp=0) (h0z : s=0 → qz=0)
    (he : q=qp+qz+2*m^2-2+4*a*m+4*(a+m+2)*s) : m=1 ∧ s≤1 := by
  have hm5 : m<5 := by
    by_cases h : m<5
    · exact h
    · have h1:=Int.mul_nonneg (show 0≤m-5 by omega) (show 0≤m+5 by omega)
      have h2:=Int.mul_nonneg ha (show 0≤m by omega)
      have h3:=Int.mul_nonneg (show 0≤a+m+2 by omega) hs
      grind only
  have hm1 : m=1 := by
    by_cases h : m=1
    · exact h
    · have h3 : m=3 := by omega
      rw [h3] at he
      have hs0 : s=0 := by
        by_cases hs' : s=0
        · exact hs'
        · have hn:=Int.mul_nonneg ha (show 0≤s by omega)
          grind only
      have hqz0:=h0z hs0
      rw [hs0,hqz0] at he
      have ha0 : a=0 := by omega
      have hqp0:=h0p ha0
      omega
  rw [hm1] at he
  refine ⟨hm1,?_⟩
  have hn:=Int.mul_nonneg ha hs
  grind only

private theorem mass_one_one_S (y : List Bool) (hm : mass y=1) (hf : cntF y=1) (hk : runKey y= -2) :
    y=[false,true,true] := by
  have hc:=cntF_int y
  have hm':=mass_eq y
  have hlen : y.length=3 := by omega
  cases y with
  | nil => simp at hlen
  | cons a y =>
    cases y with
    | nil => simp at hlen
    | cons b y =>
      cases y with
      | nil => simp at hlen
      | cons c y =>
        have h : y=[] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_cons] at hlen
          omega
        subst y
        cases a <;> cases b <;> cases c <;> simp [cntF,mass,runKey,areaW,Recaman.ShortPeriodicSupply.sign] at hm hf hk ⊢

/-- At small odd cross, a local supply endpoint belongs to one of the
last two subtraction ranks and its source is exactly SAA. -/
theorem local_source_at_last_two_S (x z : List Bool)
    (hq : cross (x++[true]++z)≤20) (ho : cross (x++[true]++z)%8=4)
    (hl : Recaman.ThreeNonsuppliedData.localSupply x=true) :
    (∃ v, x=v++[false,true,true]) ∧ cntF z≤1 := by
  have hloc : Recaman.ThreeNonsuppliedData.localSupply
      (x++List.replicate 0 true++List.replicate 0 false)=true := by
    simpa only [List.replicate_zero,List.append_nil] using hl
  obtain ⟨t,ht,hm,hk⟩:=(localSupply_A_S_iff x 0 0).mp hloc
  let v:=x.take t
  let y:=x.drop t
  have hxy : x=v++y := (List.take_append_drop t x).symm
  have hm1 : mass y=1 := by simpa [y] using hm
  have hk1 : runKey y= -2 := hk
  have hodd:=Recaman.MixedASQuarterBudget.source_subtraction_odd y hk1
  have hc:=cntF_int y
  have hy:=mass_eq y
  have hyA : ones y=(cntF y : Int)+1 := by omega
  have hQy : cross y=2*(cntF y : Int)^2-2 := by unfold cross; rw [hk1]; omega
  have hQ:=cross_at_addition x z
  rw [hxy,cross_append v y,hQy,ones_append v y,hyA] at hQ
  have hEq : cross (x++[true]++z)=cross v+cross z+2*(cntF y : Int)^2-2+
      4*ones v*(cntF y : Int)+4*(ones v+(cntF y : Int)+2)*(cntF z : Int) := by
    rw [hxy]
    grind only
  obtain ⟨h1,h2⟩:=small_cross_arith (cross (x++[true]++z)) (cross v) (cross z)
    (ones v) (cntF y : Int) (cntF z : Int) hq ho (cross_nonnegative v) (cross_nonnegative z)
    (ones_bounds v).1 (by omega) (by omega) hodd (cross_zero_of_no_A v)
    (fun hs=>cross_zero_of_no_S z (by omega)) hEq
  have hyword:=mass_one_one_S y hm1 (by omega) hk1
  exact ⟨⟨v,hxy.trans (congrArg (v++·) hyword)⟩,by omega⟩

end Recaman.LowCrossLocalClocks
