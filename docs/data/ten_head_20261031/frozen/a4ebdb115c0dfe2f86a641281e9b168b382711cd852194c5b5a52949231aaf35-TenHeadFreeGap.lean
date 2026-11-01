import Recaman.TenHeadActualCases
import Recaman.TenHeadLocalBudget

namespace Recaman.TenHeadFreeGap

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.TenHeadActualCases Recaman.TenHeadLocalBudget Recaman.TenHeadSourcePruning

private theorem count_shift (P : Nat → Prop) (s : Nat) : ∀ K,
    cN P s K=cN (fun i=>P (s+i)) 0 K
  | 0 => rfl
  | K+1 => by
    have ih:=count_shift P s K
    simp only [cN,Nat.zero_add,ih]
    simp only [Nat.zero_add]

/-- Old windows are removed only after their pointwise impossibility
has been supplied. This equality retains every local window. -/
theorem last_count_eq_local (f : Nat → Bool) (n v T : Nat) (z : List Bool)
    (hz : seg f n 20=z)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ k, k<T → f (n+20+v+k)=true)
    (hno : ∀ k, k<T → ∀ s, s<n → ¬Win f s (n+20+v+k-s)) :
    cN (EndN f 0) (n+20+v) T=rayCount (z++List.replicate v false) T := by
  rw [count_shift]
  apply cN_congr
  intro i _ hi
  have hei : EndN f 0 (n+20+v+i) ↔ EndN f n (n+20+v+i) := by
    constructor
    · rintro ⟨ha,s,l,h0s,heq,hw⟩
      have hns : n≤s := by
        by_cases hh : n≤s
        · exact hh
        · have heql : l=n+20+v+i-s := by omega
          rw [heql] at hw
          exact False.elim (hno i (by omega) s (by omega) hw)
      exact ⟨ha,s,l,hns,heq,hw⟩
    · exact end_mono f 0 n _ (Nat.zero_le _)
  have hword : seg f n (20+v+i)=z++List.replicate v false++List.replicate i true := by
    rw [seg_add,seg_add,hz,seg_false f (n+20) v hS]
    have hh : seg f (n+(20+v)) i=List.replicate i true := by
      apply seg_A
      intro x hx hxi
      have ha:=hA (x-(n+20+v)) (by omega)
      rw [show n+20+v+(x-(n+20+v))=x by omega] at ha
      exact ha
    rw [hh]
  have he:=localSupply_seg_iff f n (n+20+v+i) (by omega) (hA i (by omega))
  rw [show n+20+v+i-n=20+v+i by omega,hword] at he
  change EndN f 0 (n+20+v+i) ↔ _
  exact hei.trans he.symm

/-- All positive three-A-run heads with zero mass, ten S signs and area
in the moment band satisfy the actual final-S-source free-gap. The same
old target supplies the two cases internally; no local/free bound is
assumed and no other old history is truncated. -/
theorem ten_head_final_S_free_gap (f : Nat → Bool) (n t h M m L s U v T j q i : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hh : 1≤h) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U)
    (hS10 : h+m+s=10) (hA10 : M+L+U=10)
    (hz : seg f n 20=List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)
    (B : Int) (haz : areaW (seg f n 20)= -B) (hlo : 46≤B) (hhi : B≤64)
    (hv : 1≤v) (hq : 1≤q) (hqv : q≤v) (hi : i<T) (hband : T≤i+j)
    (hS : ∀ x, n+20≤x → x<n+20+v → f x=false)
    (hA : ∀ k, k<T → f (n+20+v+k)=true)
    (hgap : ∀ x, n+20+v+T≤x → x<n+20+v+T+j → f x=false)
    (htarget : Win f t (n+20+v+T+j-t))
    (hlocal : Win f (n+20+v-q) (q+i))
    (hpos : ∀ k, 0<k → k≤20+v+T →
      cN (EndN f 0) n k+1≤cN (fun x=>f x=false) n k) :
    j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T) := by
  by_cases hgood : j+1≤cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T)
  · exact hgood
  · have hcounter : cN (fun x=>f x=true ∧ ¬EndN f 0 x) n (20+v+T)<j+1 := by omega
    let z:=seg f n 20
    have hmz : mass z=0 := by
      simp only [z,hz,mass_append,mass_rep_false,mass_replicate_A]
      omega
    have hSz : cntF z=10 := by
      have hc:=mass_cntF z
      have hl : z.length=20 := seg_length f n 20
      rw [hmz,hl] at hc
      omega
    have hcases:=actual_ten_head_target_cases f n t v T j q i w z hw hpre ht rfl
      hmz hSz B haz hlo hhi hv hq hqv hi hband hS hA hgap htarget hlocal hpos hcounter
    have hF4:=ten_head_free_four f n w z hw hpre rfl hmz hSz
      (fun k hk hk20=>hpos k hk (by omega))
    have hno:=actual_two_cases_no_old f n t v T j w z hw hpre ht rfl hmz hSz B haz hlo hhi
      (by rcases hcases.2.2.2 with h|h; exact Or.inl ⟨h.1,h.2.1,h.2.2.1⟩; exact Or.inr ⟨h.1,h.2.1,h.2.2.1⟩)
      hS hA hgap htarget
    have heq:=last_count_eq_local f n v T z rfl hS hA hno
    have hpart:=addition_endable_partition f (n+20+v) T
    rw [count_A_run f (n+20+v) T hA] at hpart
    let P:=fun x=>f x=true ∧ ¬EndN f 0 x
    have hzero : cN P (n+20) v=0 := by
      apply cN_zero_of
      intro x hx hxv hp
      have hh:=hS x hx hxv
      change f x=true ∧ ¬EndN f 0 x at hp
      rw [hh] at hp
      simp at hp
    have h1:=cN_add P n 20 v
    have h2:=cN_add P n (20+v) T
    have haz' : areaW (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)= -B := by rw [←hz]; exact haz
    have hmz' : mass (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=0 := by rw [←hz]; exact hmz
    have hSz' : cntF (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true)=10 := by rw [←hz]; exact hSz
    change 4≤cN P n 20 at hF4
    change cN P n (20+v+T)<j+1 at hcounter
    change T=cN (EndN f 0) (n+20+v) T+cN P (n+20+v) T at hpart
    rcases hcases.2.2.2 with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩
    · have hb:=first_case_local_four h M m L s U hh hM hm hL hs hU hS10 hA10 haz'
      have hz' : z=List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true := hz
      rw [hz'] at heq
      have hlast : cN (EndN f 0) (n+20+1) 5≤4 := by omega
      simp only [P,Nat.add_assoc] at *
      omega
    · have hb:=ten_head_local_le_five h M m L s U 2 7 56 (by decide) hmz' hSz' haz'
        (Or.inr ⟨rfl,rfl⟩)
      have hz' : z=List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false++List.replicate U true := hz
      rw [hz'] at heq
      have hlast : cN (EndN f 0) (n+20+2) 7≤5 := by omega
      simp only [P,Nat.add_assoc] at *
      omega

end Recaman.TenHeadFreeGap
