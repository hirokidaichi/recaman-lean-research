import Recaman.LowerMomentOldClock

namespace Recaman.MassThreeOldPair

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.ASourceReuse

def massThreeWords : List (List Bool) :=
  [[true,true,true],[false,true,true,true,true],[true,false,true,true,true]]
def areaPairs : List (Int × Int) :=
  [(10,6),(10,5),(13,7),(13,6),(11,5),(11,6),(9,6),(12,7),(12,6),(9,7)]

private theorem pair_table_checked :
    (massFourWords.all fun x => massThreeWords.all fun y =>
      decide ((x.IsSuffix y ∨ y.IsSuffix x) → (areaW x,areaW y) ∈ areaPairs))=true := by decide

/-- One common prefix supplies both suffixes. Both source-position
orders are included, unlike two independent low-mass signatures. -/
theorem common_prefix_mass_three_four_areas (w : List Bool) (hw : BlockWord w) (s t : Nat)
    (h4 : mass (w.drop s)=4) (h3 : mass (w.drop t)=3) :
    (areaW (w.drop s),areaW (w.drop t)) ∈ areaPairs := by
  have hs:=block_suffix hw (w.take s) (w.drop s) (List.take_append_drop s w)
  have ht:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hm4:=block_mass_four hs h4
  have hm3 : w.drop t ∈ massThreeWords := by
    rcases block_mass_three ht h3 with h|h|h <;> rw [h] <;> decide
  have hc:=List.all_eq_true.mp (List.all_eq_true.mp pair_table_checked (w.drop s) hm4) (w.drop t) hm3
  have hsuf : (w.drop s).IsSuffix w := ⟨w.take s,List.take_append_drop s w⟩
  have htuf : (w.drop t).IsSuffix w := ⟨w.take t,List.take_append_drop t w⟩
  exact of_decide_eq_true hc (List.suffix_or_suffix_of_suffix hsuf htuf)

private theorem square_mod_four (R : Int) : (R*R)%4=0 ∨ (R*R)%4=1 := by
  have hR : R=2*(R/2) ∨ R=2*(R/2)+1 := by omega
  rcases hR with he|ho
  · have hh : R*R=4*((R/2)*(R/2)) := by grind only
    left
    omega
  · have hh : R*R=4*((R/2)*(R/2)+(R/2))+1 := by grind only
    right
    omega

def coupledAreaPairs : List (Int × Int) := [(10,5),(13,6),(9,6),(12,7),(12,6)]

private theorem coupled_pair_filter (S R B a b : Int) (hp : (a,b)∈areaPairs)
    (hB : B=8*S+a+6) (hc : R*R=2*S+3+a-b) (hpar : B%2=S%2) :
    (a,b)∈coupledAreaPairs := by
  have hsq:=square_mod_four R
  simp only [areaPairs,List.mem_cons,List.mem_singleton,Prod.mk.injEq] at hp
  rcases hp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals first | decide | omega

/-- At final separator3, an old mass4 clock0 and the same old mass3
target exclude five source-area pairs through the measured head parity.
No head-size or future-clock cutoff occurs. Actual count/free is separate. -/
theorem mass_three_target_old_four_pair_cut (w z : List Bool) (hw : BlockWord w) (s t T j : Nat)
    (h4 : mass (w.drop s)=4) (h3 : mass (w.drop t)=3)
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B)
    (hsource : runKey (w.drop s++z++List.replicate 3 false)= -2)
    (hm : mass (w.drop t++z++List.replicate 3 false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (w.drop t++z++List.replicate 3 false++List.replicate T true++List.replicate j false)=0) :
    (areaW (w.drop s),areaW (w.drop t)) ∈ coupledAreaPairs ∧
      B=8*(cntF z : Int)+areaW (w.drop s)+6 ∧
      ((j : Int)+1)^2=2*(cntF z : Int)+3+areaW (w.drop s)-areaW (w.drop t) := by
  have hpair:=common_prefix_mass_three_four_areas w hw s t h4 h3
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  have hks : runKey (w.drop s)=2*areaW (w.drop s)-20 := by unfold runKey; rw [h4]; grind only
  have hkt : runKey (w.drop t)=2*areaW (w.drop t)-12 := by unfold runKey; rw [h3]; grind only
  have hs:=hsource
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz,h4,hks] at hs
  have ht:=source_key_before_gap (w.drop t++z++List.replicate 3 false) T j hm ha
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz,h3,hkt] at ht
  have hB : B=8*(cntF z : Int)+areaW (w.drop s)+6 := by grind only
  have hcircle : ((j : Int)+1)*((j : Int)+1)=2*(cntF z : Int)+3+areaW (w.drop s)-areaW (w.drop t) := by grind only
  have hp:=Recaman.LowerMomentOldClock.zero_mass_area_parity z hmz B haz
  exact ⟨coupled_pair_filter (cntF z : Int) ((j : Int)+1) B (areaW (w.drop s)) (areaW (w.drop t)) hpair hB hcircle hp,hB,by grind only⟩

end Recaman.MassThreeOldPair
