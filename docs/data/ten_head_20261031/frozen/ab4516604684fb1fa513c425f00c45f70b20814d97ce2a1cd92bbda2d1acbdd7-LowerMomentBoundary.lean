import Recaman.LowerMomentOldClock
import Recaman.ShortGapLocalBudget

namespace Recaman.LowerMomentBoundary

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

open Recaman.FourthSourceFamilies Recaman.ShortGapSourceClocks Recaman.OneGapInteriorA
open Recaman.ASourceReuse

private theorem boundary_scalar (S C V R : Int) (hS : 0≤S) (hC : 1≤C)
    (hV : 1≤V) (hR : 5≤R) (hCV : V-1≤C)
    (hk : R*R+2*C*(S+V)-V*V≤4*S+6) : C=1 ∧ V≤2 := by
  have hRp:=Int.mul_nonneg (show 0≤R-5 by omega) (show 0≤R+5 by omega)
  have hRsq : 25≤R*R := by grind only
  have hV2 : V≤2 := by
    by_cases hh : V≤2
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-V+1 by omega) (show 0≤S+V by omega)
      have hq:=Int.mul_nonneg (show 0≤V-3 by omega) hS
      have hr:=Int.mul_nonneg (show 0≤V-3 by omega) (show 0≤V+1 by omega)
      grind only
  have hv : V=1 ∨ V=2 := by omega
  have hC1 : C=1 := by
    by_cases hh : C=1
    · exact hh
    · have hp:=Int.mul_nonneg (show 0≤C-2 by omega) (show 0≤S+V by omega)
      rcases hv with rfl|rfl <;> grind only
  exact ⟨hC1,hV2⟩

/-- Exact boundary target coupling forces a single final S and a large
head. No bound on the other old-source masses is supplied as an input. -/
theorem lower_boundary_target (u z : List Bool) (hu : BlockWord u) (hne : u≠[])
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B) (hB : B=4*(cntF z : Int)+5)
    (v T j : Nat) (hv : 1≤v) (hR : 5≤j+1) (hband : T≤j+2)
    (hm : mass (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=0) :
    u=[true] ∧ v=1 ∧ T=j+1 ∧ 10≤cntF z := by
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hm' := hm
  simp only [mass_append,mass_rep_false,mass_replicate_A,hmz] at hm'
  have hk:=source_key_before_gap (u++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz] at hk
  have hkey : runKey u=2*B-4*mass u*((cntF z : Int)+(v : Int))+2*(v : Int)^2-2*((j : Int)+1)^2 := by grind only
  have hl:=block_area_quadratic_lower hu
  have hlow : -2≤runKey u := by unfold runKey; omega
  obtain ⟨hC1,hV2⟩:=boundary_scalar (cntF z : Int) (mass u) (v : Int) ((j : Int)+1)
    (by omega) hC (by omega) (by omega) (by omega) (by grind only)
  have huA:=block_mass_one hu hC1
  have hku : runKey u=0 := by rw [huA]; decide
  rw [hku,hC1] at hkey
  have hv12 : v=1 ∨ v=2 := by omega
  have hv1 : v=1 := by
    rcases hv12 with hh|hh
    · exact hh
    · rw [hh] at hkey
      have hc : ((j : Int)+1)*((j : Int)+1)=2*(cntF z : Int)+5 := by grind only
      exact False.elim (Recaman.LowerMomentOldClock.lower_five_circle_excluded z hmz B ((j : Int)+1) haz hB hc)
  refine ⟨huA,hv1,by omega,?_⟩
  rw [hv1] at hkey
  have hRprod:=Int.mul_nonneg (show 0≤((j : Int)+1)-5 by omega) (show 0≤((j : Int)+1)+5 by omega)
  grind only

private theorem initial_lower_clock (d v i : Nat) (x : List Bool) (B : Int)
    (hm : mass (List.replicate d false++x)=0)
    (ha : areaW (List.replicate d false++x)= -B)
    (hS : 3≤cntF (List.replicate d false++x))
    (hlo : 4*(cntF (List.replicate d false++x) : Int)+5≤B)
    (hhi : B≤6*(cntF (List.replicate d false++x) : Int)+4)
    (hv : 1≤v) (hv3 : v≤3)
    (hbal : mass (x++List.replicate v false)+(i : Int)=1)
    (hkey : runKey (x++List.replicate v false)= -2) :
    (v=2 ∧ i=0 ∧ B=6*(cntF (List.replicate d false++x) : Int)) ∨
      (v=3 ∧ i=1 ∧ B=6*(cntF (List.replicate d false++x) : Int)+1) := by
  let S:=cntF (List.replicate d false++x)
  have hcnt : (cntF x : Int)=(S : Int)-(d : Int) := by
    dsimp [S]
    rw [cntF_append,cntF_replicate_S]
    omega
  have hm' := hm
  rw [mass_append,mass_rep_false] at hm'
  have hbal' := hbal
  rw [mass_append,mass_rep_false] at hbal'
  have hd : d+i=v+1 := by omega
  have hkz : runKey (List.replicate d false++x)= -2*B := by unfold runKey; rw [hm,ha]; grind only
  rw [runKey_prepend_S,hcnt] at hkz
  have hkey' := hkey
  rw [runKey_append_S] at hkey'
  have hB : B=2*(d : Int)*((S : Int)+(v : Int))-(d : Int)^2-(v : Int)^2+1 := by grind only
  change 3≤S at hS
  change 4*(S : Int)+5≤B at hlo
  change B≤6*(S : Int)+4 at hhi
  change (v=2 ∧ i=0 ∧ B=6*(S : Int)) ∨ (v=3 ∧ i=1 ∧ B=6*(S : Int)+1)
  have hvv : v=1 ∨ v=2 ∨ v=3 := by omega
  rcases hvv with rfl|rfl|rfl
  · have hdv : d=0 ∨ d=1 ∨ d=2 := by omega
    rcases hdv with rfl|rfl|rfl <;> omega
  · have hdv : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases hdv with rfl|rfl|rfl|rfl <;> omega
  · have hdv : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
    rcases hdv with rfl|rfl|rfl|rfl|rfl <;> omega

private theorem initial_lower_family (h v i : Nat) (x : List Bool) (B : Int)
    (hm : mass (List.replicate h false++x)=0)
    (ha : areaW (List.replicate h false++x)= -B)
    (hS : 3≤cntF (List.replicate h false++x))
    (hlo : 4*(cntF (List.replicate h false++x) : Int)+5≤B)
    (hhi : B≤6*(cntF (List.replicate h false++x) : Int)+4)
    (hv : 1≤v) (hv3 : v≤3)
    (he : sourceAt false h (x++List.replicate v false) i) :
    (v=2 ∧ i=0) ∨ (v=3 ∧ i=1) := by
  obtain ⟨q,hq,hqh,hbal,hkey⟩:=he
  let d:=h-q
  have hd : d≤h := by dsimp [d]; omega
  have heq : List.replicate h false++x=List.replicate d false++(List.replicate q false++x) := by
    have htake : (List.replicate h false).take d=List.replicate d false := by
      rw [List.take_replicate,Nat.min_eq_left hd]
    have hdrop : (List.replicate h false).drop d=List.replicate q false := by
      rw [List.drop_replicate,show h-d=q by dsimp [d]; omega]
    rw [←htake,←hdrop,←List.append_assoc,List.take_append_drop]
  have hc:=initial_lower_clock d v i (List.replicate q false++x) B
    (by rw [←heq]; exact hm) (by rw [←heq]; exact ha)
    (by rw [←heq]; exact hS) (by rw [←heq]; exact hlo) (by rw [←heq]; exact hhi) hv hv3
    (by simpa only [List.append_assoc] using hbal) (by simpa only [List.append_assoc] using hkey)
  rcases hc with h|h
  · exact Or.inl ⟨h.1,h.2.1⟩
  · exact Or.inr ⟨h.1,h.2.1⟩


theorem lower_short_gap_local_budget (h M m L s U v K : Nat) (hs : 1≤s)
    (hmz : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0)
    (B : Int)
    (haz : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B)
    (hS : 3≤cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true))
    (hlo : 4*(cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true) : Int)+5≤B)
    (hhi : B≤6*(cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true) : Int)+4)
    (hv : v=1 ∨ v=2) :
    rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤v+3 := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true
  let P:=fun i : Nat=>i=0 ∨ i=2
  let Q:=sourceAt true M (List.replicate m false++List.replicate L true++List.replicate s false++
    List.replicate U true++List.replicate v false)
  let R:=sourceAt false m (List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false)
  let D:=sourceAt true L (List.replicate s false++List.replicate U true++List.replicate v false)
  have hvpos : 1≤v := by omega
  have hv3 : v≤3 := by omega
  have hpoint : ∀ i, Recaman.ThreeNonsuppliedData.localSupply
      (List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
        List.replicate i true)=true → P i ∨ Q i ∨ R i ∨ (v=2 ∧ D i) := by
    intro i hi
    rcases (local_fourth_sources h M m L s U v i hvpos).mp hi with h0|h1|h2|h3|h4|h5
    · have hx:=initial_lower_family h v i x B
        (by simpa only [x,List.append_assoc] using hmz)
        (by simpa only [x,List.append_assoc] using haz)
        (by simpa only [x,List.append_assoc] using hS)
        (by simpa only [x,List.append_assoc] using hlo)
        (by simpa only [x,List.append_assoc] using hhi) hvpos hv3
        (by simpa only [x,List.append_assoc] using h0)
      left
      change i=0 ∨ i=2
      rcases hx with hx|hx <;> omega
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h2))
    · by_cases hv2 : v=2
      · exact Or.inr (Or.inr (Or.inr ⟨hv2,h3⟩))
      · have hv1 : v=1 := by omega
        subst v
        obtain ⟨e,he,heL,hbal,hkey⟩:=h3
        have hi2:=interior_A_one_gap_clock e s U i he hs
          (by simpa only [List.replicate_one,List.append_assoc] using hbal)
          (by simpa only [List.replicate_one,List.append_assoc] using hkey)
        exact Or.inl (Or.inr hi2)
    · obtain ⟨q,hq,hqs,hbal,hkey⟩:=h4
      have hi02:=tail_S_small_gap_clock q U v i hq hvpos hv3
        (by simpa only [List.append_assoc] using hbal)
        (by simpa only [List.append_assoc] using hkey)
      exact Or.inl hi02
    · exact Or.inl (Or.inr h5)
  have hlocal : rayCount (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false) K≤
      cN (fun i=>P i ∨ Q i ∨ R i ∨ (v=2 ∧ D i)) 0 K := by
    apply cN_mono
    intro i _ _ hi
    exact hpoint i hi
  have hP : cN P 0 K≤2 := zero_two_count K
  have hQ : cN Q 0 K≤1 := sourceAt_count_le_one true M _ K
  have hR : cN R 0 K≤1 := sourceAt_count_le_one false m _ K
  have hD : cN (fun i=>v=2 ∧ D i) 0 K≤v-1 := by
    by_cases hv2 : v=2
    · have hh : cN (fun i=>v=2 ∧ D i) 0 K≤cN D 0 K := by
        apply cN_mono
        intro i _ _ hi
        exact hi.2
      have hd : cN D 0 K≤1 := sourceAt_count_le_one true L _ K
      omega
    · have hz : cN (fun i=>v=2 ∧ D i) 0 K=0 := by
        apply cN_zero_of
        intro i _ _ hi
        exact hv2 hi.1
      rw [hz]
      omega
  have h1:=cN_or_le P (fun i=>Q i ∨ R i ∨ (v=2 ∧ D i)) K
  have h2:=cN_or_le Q (fun i=>R i ∨ (v=2 ∧ D i)) K
  have h3:=cN_or_le R (fun i=>v=2 ∧ D i) K
  omega


/-- The apparently added lower5 boundary contains no actual zero-mass
word target in the R>=5 counter domain. Its free-gap extension must not
be counted as newly covered histories. -/
theorem lower_five_counter_target_absent (u z : List Bool) (hu : BlockWord u) (hne : u≠[])
    (hmz : mass z=0) (B : Int) (haz : areaW z= -B) (hB : B=4*(cntF z : Int)+5)
    (v T j : Nat) (hv : 1≤v) (hR : 5≤j+1) (hband : T≤j+2)
    (hm : mass (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=1)
    (ha : areaW (u++z++List.replicate v false++List.replicate T true++List.replicate j false)=0) : False := by
  have hc:=lower_boundary_target u z hu hne hmz B haz hB v T j hv hR hband hm ha
  obtain ⟨huA,hv1,hT,hS10⟩:=hc
  have hpar:=Recaman.LowerMomentOldClock.zero_mass_area_parity z hmz B haz
  let S:=(cntF z : Int)
  let R:=(j : Int)+1
  have hSodd : S%2=1 := by dsimp [S]; omega
  have hSr : S=2*(S/2)+1 := by omega
  have hRr : R=2*(R/2) ∨ R=2*(R/2)+1 := by omega
  have hk:=source_key_before_gap (u++z++List.replicate v false) T j hm ha
  have hkz : runKey z= -2*B := by unfold runKey; rw [hmz,haz]; grind only
  rw [runKey_append_S,runKey_append,hkz,mass_append,hmz,huA,hv1] at hk
  have hkeyA : runKey [true]=0 := by decide
  have hmassA : mass [true]=1 := by decide
  rw [hkeyA,hmassA] at hk
  have hcircle : R*R=2*S+4 := by dsimp [R,S]; grind only
  rcases hRr with he|ho
  · rw [he,hSr] at hcircle
    have hh : 4*((R/2)*(R/2))=4*(S/2)+6 := by grind only
    omega
  · rw [ho,hSr] at hcircle
    have hh : 4*((R/2)*(R/2))+4*(R/2)+1=4*(S/2)+6 := by grind only
    omega

end Recaman.LowerMomentBoundary
