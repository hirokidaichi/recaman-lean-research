import Recaman.LowSeparatorLocalBudget

namespace Recaman.OneSLocalSaturation

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.OneGapInteriorA

/-- With S1, absence of the third-S clock0 lowers the remaining local
budget to two. Saturation therefore supplies its U4/s>=2 conditions. -/
theorem saturated_one_S_tail (u : List Bool) (hu : BlockWord u) (hcu : mass u=3)
    (h M m L s U R K : Nat) (hR : 1≤R) (hzero : M+L+U=h+m+s) (hs : 1≤s)
    (hbudget : M≤R+1) (B : Int)
    (hB : runKey (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -2*B)
    (hkeyTarget : runKey u=2*B-12*((h : Int)+(m : Int)+(s : Int)+1)+2-2*(R : Int)^2)
    (hcount : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 1 false) K=3) :
    U=4 ∧ 2≤s := by
  classical
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false++List.replicate U true
  have hmz : mass (List.replicate h false++x)=0 := by
    simp only [x,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hSz : cntF (List.replicate h false++x)=h+m+s := by
    have hc:=mass_cntF (List.replicate h false++x)
    have hl : (List.replicate h false++x).length=h+M+m+L+s+U := by
      simp only [x,List.length_append,List.length_replicate,Nat.add_assoc]
    rw [hmz,hl] at hc
    omega
  have hBx : runKey (List.replicate h false++x)= -2*B := by
    simpa only [x,List.append_assoc] using hB
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 1 false)
  by_cases htail : sourceAt false s (List.replicate U true++List.replicate 1 false) 0
  · obtain ⟨q,hq,hqs,hbal,hkey⟩:=htail
    have hm : mass (List.replicate q false++List.replicate U true++List.replicate 1 false)=1 := by
      simpa only [List.append_assoc,Int.natCast_zero,Int.add_zero] using hbal
    have hk : runKey (List.replicate q false++List.replicate U true++List.replicate 1 false)= -2 := by
      simpa only [List.append_assoc] using hkey
    rw [runKey_S_A_S] at hk
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm
    have he : ((q : Int)-2)*((q : Int)+2)=0 := by grind only
    rcases Int.mul_eq_zero.mp he with hq2|hqn
    · omega
    · omega
  · have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
        (List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
          List.replicate s false++List.replicate U true++List.replicate 1 false++List.replicate i true)=true →
        Q i ∨ i=2 := by
      intro i hi
      rcases (local_fourth_sources h M m L s U 1 i (by decide)).mp hi with h0|h1|h2|h3|h4|h5
      · have hn:=Recaman.LowSeparatorSources.low_separator_initial_source_excluded u x hu h 1 R i (Or.inl rfl) hR hmz
          (by rw [hBx,hSz]; simp only [Int.natCast_add,Int.natCast_one]; omega)
        exact False.elim (hn (by simpa only [x,List.append_assoc] using h0))
      · exact False.elim (Recaman.LowSeparatorSources.low_separator_first_A_excluded u hu hcu h M m L s U 1 R i
          (Or.inl rfl) hzero hbudget B hB (by simp only [Int.natCast_one]; omega) h1)
      · exact Or.inl h2
      · obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        right
        exact interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
      · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
        have hi02:=tail_S_small_gap_clock q U 1 i hq (by decide) (by decide)
          (by simpa only [List.append_assoc] using hbal)
          (by simpa only [List.append_assoc] using hkey)
        rcases hi02 with hi0|hi2
        · subst i
          exact False.elim (htail ⟨q,hq,hqs,hbal,hkey⟩)
        · exact Or.inr hi2
      · exact Or.inr h5
    have hc : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate 1 false) K≤
        cN (fun i=>Q i ∨ i=2) 0 K := by
      apply cN_mono
      intro i _ _ hi
      exact hpoint i (by simpa only [List.append_assoc] using hi)
    have hq : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
    have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
    have ho:=cN_or_le Q (fun i=>i=2) K
    omega

end Recaman.OneSLocalSaturation
