import Recaman.DoubleDefectActualFive
import Recaman.SourceFamilyFreeCount

namespace Recaman.DoubleDefectGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

theorem double_counter_excluded (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+2)
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
    (hbad : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)<j+1) : False := by
  have hb:=Recaman.DoubleDefectCounter.double_defect_counter f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hcut:=Recaman.DoubleDefectActualFive.double_defect_actual_five f n t h M m L s U v T j μ w hw hpre ht
    hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos hbad
  have hsmall:=hcut.2
  let H:=h+M+m+L+s+U
  let z:=seg f n H
  let free:=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n H
  have hf3 : free≤3 := hsmall.2
  have hword:=Recaman.SeparatorSupplyReset.three_run_word f n h M m L s U hS hA hS2 hA2 hS3 hA3
  have hzeq : z=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true := hword
  have hmz : mass z=(μ : Int) := by rw [hzeq]; simp only [mass_append,mass_rep_false,mass_replicate_A]; omega
  have hSz : cntF z=h+m+s := by
    have hc:=mass_cntF z
    rw [hmz,show z.length=H from seg_length f n H] at hc
    dsimp [H] at hc
    omega
  have hAc : cN (fun x=>f x=true) n H=M+L+U := by
    have hc:=ones_seg_eq_count f n H
    dsimp [H] at hc ⊢
    rw [hword] at hc
    simp only [ones_append,ones_replicate_A,ones_replicate_S] at hc
    omega
  have hbudget:=positive_r3_additions_free_bound f n 0 H hw (by simpa using hpre)
    (fun k hk hkH=>hpos k hk (by dsimp [H] at hkH; omega)) hf3
  rw [hAc] at hbudget
  change M+L+U≤2*free+1 at hbudget
  have hu:=block_suffix hw (w.take t) (w.drop t) (List.take_append_drop t w)
  have hu1 : w.drop t=[true] := block_mass_one hu hC
  have hp:=Recaman.MomentTargetProfile.actual_target_word_profile f n t H v T j w z hpre ht rfl
    (by simpa only [H,Nat.add_assoc] using hS4)
    (by simpa only [H,Nat.add_assoc] using hA4)
    (by simpa only [H,Nat.add_assoc] using hgap)
    (by simpa only [H,Nat.add_assoc] using htarget)
  have hR : 5≤j+1 := hb.2.1
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
  have hvInt : (v : Int)=(μ : Int)+2 := by omega
  simp only [Int.natCast_add] at htkey
  have htkey2 : 4*K-2*S^2+4*S+4*(v : Int)*(1+(μ : Int))-2*(v : Int)^2= -2*((j : Int)+1)^2 := by
    dsimp [S]; grind only
  rw [hvInt] at htkey2
  exact False.elim (by grind only)

theorem double_defect_gap (f : Nat → Bool) (n t h M m L s U v T j μ : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hμ : 1≤μ) (hv : v=μ+2)
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
  by_cases he : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (h+M+m+L+s+U+v+T)
  · exact he
  · exact False.elim (double_counter_excluded f n t h M m L s U v T j μ w hw hpre ht
      hh hM hm hL hs hU hμ hv hheadMass hS hA hS2 hA2 hS3 hA3 hS4 hA4 hgap htarget hC hpos (by omega))

end Recaman.DoubleDefectGap
