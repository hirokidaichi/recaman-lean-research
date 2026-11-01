import Recaman.FourthSourceFamilies

namespace Recaman.OldZeroInitialSource

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSourceFamilies

/-- In a zero-mass head, an old supplier at clock0 excludes every local
source in the initial S run, for every positive final separator length. -/
theorem old_zero_initial_source_exclusion (u x : List Bool) (hu : BlockWord u)
    (h v i : Nat) (hv : 1≤v)
    (hmz : mass (List.replicate h false++x)=0)
    (hS : 1≤cntF (List.replicate h false++x))
    (hmold : mass u-(v : Int)=1)
    (hkold : runKey (u++(List.replicate h false++x)++List.replicate v false)= -2) :
    ¬sourceAt false h (x++List.replicate v false) i := by
  rintro ⟨q,hq,hqh,hbal,hkey⟩
  let d:=h-q
  let r:=List.replicate q false++x
  let S:=(cntF (List.replicate h false++x) : Int)
  have hsplit : List.replicate h false++x=List.replicate d false++r := by
    dsimp [r]
    have hd : d≤h := by dsimp [d]; omega
    have ht : (List.replicate h false).take d=List.replicate d false := by
      rw [List.take_replicate,Nat.min_eq_left hd]
    have hh : (List.replicate h false).drop d=List.replicate q false := by
      rw [List.drop_replicate,show h-d=q by dsimp [d]; omega]
    rw [←ht,←hh,←List.append_assoc,List.take_append_drop]
  have hmr : mass r=(d : Int) := by
    rw [hsplit,mass_append,mass_rep_false] at hmz
    omega
  have hcr : (cntF r : Int)=S-(d : Int) := by
    have hc:=cntF_append (List.replicate d false) r
    rw [←hsplit,cntF_replicate_S] at hc
    dsimp [S]
    omega
  have hkeyr : runKey (r++List.replicate v false)= -2 := by
    simpa only [r,List.append_assoc] using hkey
  rw [runKey_append_S,hmr] at hkeyr
  have hdi : (d : Int)+(i : Int)=(v : Int)+1 := by
    have hbalr : mass (r++List.replicate v false)+(i : Int)=1 := by
      simpa only [r,List.append_assoc] using hbal
    rw [mass_append,hmr,mass_rep_false] at hbalr
    omega
  have hkz : runKey (List.replicate h false++x)=runKey r-4*(d : Int)*(S-(d : Int))-2*(d : Int)^2 := by
    rw [hsplit,runKey_prepend_S,hcr]
  have hD : mass u=(v : Int)+1 := by omega
  rw [runKey_append_S,runKey_append,mass_append,hmz,hkz,hD] at hkold
  have hku : runKey u= -4*(i : Int)*(S+(v : Int))-2*(d : Int)^2 := by
    grind only
  have hlu : -2≤runKey u := by
    have hh:=block_area_quadratic_lower hu
    unfold runKey
    omega
  have hS1 : 1≤S := by dsimp [S]; omega
  by_cases hi : i=0
  · have hd2 : 2≤d := by omega
    have hp:=Int.mul_nonneg (show 0≤(d : Int)-2 by omega) (show 0≤(d : Int)+2 by omega)
    rw [hi] at hku
    simp only [Int.natCast_zero,Int.mul_zero,Int.zero_mul,Int.zero_sub] at hku
    grind only
  · have hp:=Int.mul_nonneg (show 0≤(i : Int)-1 by omega) (show 0≤S+(v : Int) by omega)
    have hq:=Int.sq_nonneg (d : Int)
    grind only


/-- The oldclock0 exclusion removes one local source family before
counting the whole last ray, retaining every old mass in the same prefix. -/
theorem old_zero_fourth_ray_count_six (w : List Bool) (hw : BlockWord w)
    (h M m L s U v K : Nat) (hv : 1≤v)
    (hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0)
    (hS : 1≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true))
    (hseed : tailOldRay w (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) 0) :
    rayCount (w++(List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)) K≤6 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  let z:=List.replicate h false++x
  obtain ⟨t,ht,hmt,hkt⟩:=hseed
  have hu : BlockWord (w.drop t) :=
    block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hmold : mass (w.drop t)-(v : Int)=1 := by
    have hmass : mass z=0 := by simpa only [z,x,List.append_assoc] using hmz
    have hh : mass (w.drop t)+mass (z++List.replicate v false)+(0 : Int)=1 := by
      simpa only [z,x,List.append_assoc] using hmt
    simp only [mass_append,hmass,mass_rep_false] at hh
    omega
  have hkold : runKey (w.drop t++z++List.replicate v false)= -2 := by
    rw [List.append_assoc,runKey_append]
    simpa only [z,x,List.append_assoc] using hkt
  let P:=sourceAt true M (List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true++List.replicate v false)
  let Q:=sourceAt false m (List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate v false)
  let R:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  let A:=sourceAt false s (List.replicate U true++List.replicate v false)
  have hpnt : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (z++List.replicate v false++List.replicate i true)=true → P i ∨ Q i ∨ R i ∨ A i ∨ i=2 := by
    intro i hi
    have hi0 : Recaman.ThreeNonsuppliedData.localSupply
        (List.replicate h false++List.replicate M true++List.replicate m false++
          List.replicate L true++List.replicate s false++List.replicate U true++
          List.replicate v false++List.replicate i true)=true := by
      simpa only [z,x,List.append_assoc] using hi
    rcases (local_fourth_sources h M m L s U v i hv).mp hi0 with h0|h1|h2|h3|h4|h5
    · exact False.elim (old_zero_initial_source_exclusion (w.drop t) x hu h v i hv
        (by simpa only [x,List.append_assoc] using hmz)
        (by simpa only [x,List.append_assoc] using hS) hmold hkold
        (by simpa only [x,List.append_assoc] using h0))
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  have hc : rayCount (z++List.replicate v false) K≤cN (fun i=>P i ∨ Q i ∨ R i ∨ A i ∨ i=2) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpnt i hi
  have hp : cN P 0 K≤1 := sourceAt_count_le_one true M _ K
  have hq : cN Q 0 K≤1 := sourceAt_count_le_one false m _ K
  have hr : cN R 0 K≤1 := sourceAt_count_le_one true L _ K
  have ha : cN A 0 K≤1 := sourceAt_count_le_one false s _ K
  have h2 : cN (fun i=>i=2) 0 K≤1 := by apply cN_le_one_of_unique; intros; omega
  have ho1:=cN_or_le P (fun i=>Q i ∨ R i ∨ A i ∨ i=2) K
  have ho2:=cN_or_le Q (fun i=>R i ∨ A i ∨ i=2) K
  have ho3:=cN_or_le R (fun i=>A i ∨ i=2) K
  have ho4:=cN_or_le A (fun i=>i=2) K
  have hlocal5 : rayCount (z++List.replicate v false) K≤5 := by omega
  have hcnt : 3≤cntF (z++List.replicate v false) := by
    rw [cntF_append,cntF_replicate_S]
    change 1≤cntF z at hS
    have hD:=hmold
    -- A stronger S count is not needed: v=1 with head S1 cannot satisfy
    -- the old0/key and zero-head assumptions; use the raw old uniqueness
    -- only when the combined S count is at least three.
    by_cases hh : 3≤cntF z+v
    · exact hh
    · have hzS : cntF z=1 := by omega
      have hv1 : v=1 := by omega
      have hlow:=runKey_count_lower z
      have hlo : -2≤runKey (w.drop t) := by
        have hb:=block_area_quadratic_lower hu
        unfold runKey
        omega
      have hkz:=hkold
      rw [runKey_append_S,runKey_append,mass_append] at hkz
      have hm0 : mass z=0 := by simpa only [z,x,List.append_assoc] using hmz
      rw [hm0,hv1,hzS] at hkz
      have hmass2 : mass (w.drop t)=2 := by omega
      rw [hmass2] at hkz
      rw [hzS] at hlow
      grind only
  have hold:=block_rayCount_append hw (z++List.replicate v false) hcnt K
  change rayCount (w++(z++List.replicate v false)) K≤6
  omega

end Recaman.OldZeroInitialSource

