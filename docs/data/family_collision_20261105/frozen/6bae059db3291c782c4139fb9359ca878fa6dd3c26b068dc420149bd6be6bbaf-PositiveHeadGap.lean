import Recaman.PositiveHeadCounter
import Recaman.UnitDefectLocalFour
import Recaman.MixedActualCircle
import Recaman.MomentNoOld
import Recaman.SourceFamilyFreeCount
import Recaman.OldSourceKeyOrder

namespace Recaman.PositiveHeadGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem positive_head_gap (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+1)
    (hheadMass : M+L+U=h+m+s+μ)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<U → f (n+h+M+m+L+s+k)=true)
    (hS4 : ∀ x, n+h+M+m+L+s+U≤x → x<n+h+M+m+L+s+U+v → f x=false)
    (hA4 : ∀ k, k<T → f (n+h+M+m+L+s+U+v+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (htarget : Win f t (n+h+M+m+L+s+U+v+T+j-t))
    (hC : mass (w.drop t)=1)
    (hpos : ∀ k, 0<k → k≤h+M+m+L+s+U+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k)
     :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact hgood
  have hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1 := by omega
  have hb:=Recaman.PositiveHeadCounter.positive_head_counter f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let P:=fun x=>f x=true ∧ ¬EndN f 0 x
  let free:=cN P n H
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hzeq : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true := hword
  have hmz : mass z=(μ : Int) := by rw [hzeq]; simp only [mass_append,mass_rep_false,mass_replicate_A]; omega
  have hSz : cntF z=h+m+s := by rw [hzeq]; simp only [cntF_append,cntF_A,cntF_replicate_S]; omega
  have hAc : cN (fun x=>f x=true) n H=M+L+U := by
    have hc:=ones_seg_eq_count f n H
    change ones z=_ at hc
    rw [hzeq] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hT : T=j+1 := hb.1
  have hR : 5≤j+1 := hb.2.1
  have hlocal:=Recaman.UnitDefectLocalFour.fourth_local_four h M m L s U v T j (by omega)
    (by omega) hM hb.2.2
    (by rw [←hzeq,hmz]; omega)
    (by simpa only [hu1,hzeq,hT,List.append_assoc] using hp.1)
    (by simpa only [hu1,hzeq,hT,List.append_assoc] using hp.2)
  have hlocal4 : rayCount (z++List.replicate v false) T≤4 := by
    simpa only [hzeq,List.append_assoc] using hlocal
  have hshape : seg f 0 (n+H+v)=w++(z++List.replicate v false) := by
    rw [show n+H+v=n+(H+v) by omega,seg_add,Nat.zero_add,hpre,seg_add]
    rw [seg_false f (n+H) v (by simpa only [H,Nat.add_assoc] using hS4)]
  have hcount:=endable_A_run_count f (n+H+v) T _ hshape
    (by simpa only [H,Nat.add_assoc] using hA4)
  have hlast5 : cN (EndN f 0) (n+H+v) T≤5 := by
    have hc : 3≤cntF (z++List.replicate v false) := by rw [cntF_append,cntF_replicate_S,hSz]; omega
    have ha:=block_rayCount_append hw (z++List.replicate v false) hc T
    rw [hcount]
    omega
  have hcost (K : Nat) (hk : cN (EndN f 0) (n+H+v) T≤K) : free<K := by
    have hc1:=cN_add P n H v
    have hc2:=cN_add P n (H+v) T
    have hc3:=addition_endable_partition f (n+H+v) T
    rw [count_A_run f (n+H+v) T (by simpa only [H,Nat.add_assoc] using hA4)] at hc3
    change T=cN (EndN f 0) (n+H+v) T+cN P (n+H+v) T at hc3
    change cN P n (H+v+T)<j+1 at hbad
    change cN P n H<K
    simp only [Nat.add_assoc] at hc1 hc2 hc3 hk
    omega
  by_cases hex : ∃ i, i<T ∧ ∃ r, r<n ∧ Win f r (n+H+v+i-r)
  · obtain ⟨i,hi,r,hr,hseed⟩:=hex
    have hprof:=Recaman.MomentTargetProfile.actual_target_word_profile f n r H v i 0 w z hpre hr rfl
      (by simpa only [H,Nat.add_assoc] using hS4)
      (fun k hk=>by simpa only [H,Nat.add_assoc] using hA4 k (by omega))
      (by intros; omega) (by simpa only [Nat.add_zero] using hseed)
    have hord:=Recaman.OldSourceKeyOrder.actual_old_target_prior_clock f n r t (H+v) i T j
      (by rw [hpre]; exact hw) hr ht (by omega) (by omega)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      (by simpa only [Nat.add_assoc] using hseed)
      (by simpa only [H,Nat.add_assoc] using htarget)
    have hdt:=seg_drop f 0 n t (by omega)
    have hdr:=seg_drop f 0 n r (by omega)
    simp only [Nat.zero_add,hpre] at hdt hdr
    have hDlo : 2≤mass (w.drop r) := by rw [←hdt,←hdr,hC] at hord; omega
    have hD : mass (w.drop r)=2 := by
      have he:=hprof.1
      simp only [mass_append,hmz,mass_rep_false,mass_replicate_A] at he
      omega
    have hc:=Recaman.MixedActualCircle.actual_mixed_old_two_circle f n H t r v T j i w z hw hpre rfl ht hr hi hC hD
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4)
      (by simpa only [H,Nat.add_assoc] using hgap)
      hseed (by simpa only [H,Nat.add_assoc] using htarget)
    have hfree4 : free≤4 := by have he:=hcost 5 hlast5; omega
    have hh10:=Recaman.InitialSTargetBounds.three_run_count_of_manyS f n h M m L s U w hw hpre hs
      (by omega) hS hA hS2 hA2 hS3 hA3 (fun k hk hkH=>hpos k hk (by omega))
    have hpart:=addition_endable_partition f n H
    rw [hAc] at hpart
    have hE : cntF z+v≤15 := by
      change M+L+U=cN (EndN f 0) n H+free at hpart
      change cN (EndN f 0) n H≤10 at hh10
      rw [hSz]
      omega
    have hR6 : (6 : Int)≤(j : Int)+1 := by have he:=hc.1; omega
    have hsquare:=hc.2.1
    have hmul:=Int.mul_nonneg (show 0≤(j : Int)+1-6 by omega) (show 0≤(j : Int)+1+6 by omega)
    have hEi : (cntF z : Int)+(v : Int)≤15 := by omega
    exact False.elim (by grind only)
  · have hno : ∀ i, i<T → ∀ r, r<n → ¬Win f r (n+H+v+i-r) := by
      intro i hi r hr he
      exact hex ⟨i,hi,r,hr,he⟩
    have hcnt:=Recaman.MomentNoOld.last_count_eq_local f n H v T z rfl
      (by simpa only [H,Nat.add_assoc] using hS4)
      (by simpa only [H,Nat.add_assoc] using hA4) hno
    have hf3 : free≤3 := by have he:=hcost 4 (by rw [hcnt]; exact hlocal4); omega
    have hbudget:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
      (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hf3
    rw [hAc] at hbudget
    change M+L+U≤2*free+1 at hbudget
    let S : Int:=(h : Int)+(m : Int)+(s : Int)
    let K : Int:=(M : Int)*((m : Int)+(s : Int))+(L : Int)*(s : Int)
    have hK : 3≤K := by
      have ha:=Int.mul_nonneg (show 0≤(M : Int)-1 by omega) (show 0≤(m : Int)+(s : Int) by omega)
      have hb:=Int.mul_nonneg (show 0≤(L : Int)-1 by omega) (show 0≤(s : Int) by omega)
      dsimp [K]
      grind only
    have hkz : runKey z=4*K-2*S^2 := by
      rw [hzeq,runKey_append_A,Recaman.SourceFamilyFreeCount.runKey_five_runs]
      dsimp [S,K]
      grind only
    have htkey:=Recaman.ASourceReuse.source_key_before_gap (w.drop t++z++List.replicate v false) T j hp.1 hp.2
    rw [hu1,runKey_append_S,runKey_append,mass_append,hmz,hkz] at htkey
    have hmu : mass [true]=1 := by decide
    have hku : runKey [true]=0 := by decide
    rw [hmu,hku,hSz] at htkey
    have hmass : S+(μ : Int)≤7 := by dsimp [S]; omega
    have hS3 : 3≤S := by dsimp [S]; omega
    have hμ4 : (μ : Int)≤4 := by omega
    have hfactor:=Int.mul_nonneg (show 0≤7-(μ : Int)-S by omega)
      (show 0≤7-(μ : Int)+S-2 by omega)
    have hRmul:=Int.mul_nonneg (show 0≤(j : Int)+1-5 by omega) (show 0≤(j : Int)+1+5 by omega)
    have hvInt : (v : Int)=(μ : Int)+1 := by omega
    simp only [Int.natCast_add] at htkey
    change 4*K-2*S^2+4*S+4*(v : Int)*(1+(μ : Int))-2*(v : Int)^2= -2*((j : Int)+1)^2 at htkey
    rw [hvInt] at htkey
    exact False.elim (by grind only)

end Recaman.PositiveHeadGap
