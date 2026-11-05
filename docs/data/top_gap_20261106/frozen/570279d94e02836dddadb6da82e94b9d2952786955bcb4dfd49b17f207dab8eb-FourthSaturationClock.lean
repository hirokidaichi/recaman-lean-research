import Recaman.FourthSaturationSources
import Recaman.OldSourceKeyOrder
import Recaman.OldInitialClockOrder

namespace Recaman.FourthSaturationClock

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourthSaturationSources Recaman.OldSourceKeyOrder Recaman.OldInitialClockOrder

private theorem counted_source_win (f : Nat → Bool) (b i t : Nat) (v : List Bool)
    (ht : t<b) (hword : seg f 0 (b+i)=v++List.replicate i true)
    (hl : v.length=b) (hm : mass (v.drop t)+(i : Int)=1) (hk : runKey (v.drop t)= -2) :
    Win f t (b+i-t) := by
  have hd := seg_drop f 0 (b+i) t (by omega)
  simp only [hword,Nat.zero_add,List.drop_append,show t-v.length=0 by omega,List.drop_zero] at hd
  have hmass : mass (seg f t (b+i-t))=1 := by
    rw [←hd,mass_append,mass_replicate_A]
    exact hm
  have hkey : runKey (seg f t (b+i-t))= -2 := by
    rw [←hd,runKey_append_A]
    exact hk
  refine ⟨by omega,?_,?_⟩
  · rw [seg_mass] at hmass
    omega
  · rw [Ar_areaW]
    unfold runKey at hkey
    rw [hmass] at hkey
    omega

/-- Two counted sources on the final A ray, using the same original
old target. The early source and old source are distinct clocks. -/
theorem actual_last_seven_clock_cut (f : Nat → Bool) (n b t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n) (hnb : n≤b)
    (hm : 1≤m) (hs : 1≤s) (hv : 1≤v) (hj : 2≤j)
    (hword : seg f n (b-n)=List.replicate h false++(List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false))
    (hA : ∀ i, i<T → f (b+i)=true)
    (hgap : ∀ a, b+T≤a → a<b+T+j → f a=false)
    (htarget : Win f t (b+T+j-t))
    (h7 : 7≤cN (EndN f 0) b T) :
    j+2≤T ∧ mass (seg f t (n-t))+3≤(h : Int) ∧
    ∃ r q i k, r<n ∧ 1≤q ∧ q≤h ∧ k<i ∧ i+j<T ∧
      mass (seg f t (n-t))<mass (seg f r (n-r)) ∧
      Win f r (b+i-r) ∧ Win f (n+(h-q)) (b+k-(n+(h-q))) := by
  let x:=List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false++List.replicate U true++List.replicate v false
  let y:=List.replicate h false++x
  have hbase : seg f 0 b=w++y := by
    rw [show b=n+(b-n) by omega,seg_add,Nat.zero_add,hpre]
    exact hword
  have hl : (w++y).length=b := by rw [←hbase,seg_length]
  have hn : w.length=n := by rw [←hpre,seg_length]
  rw [endable_A_run_count f b T _ hbase hA] at h7
  obtain ⟨⟨i,hi,r,hr,hmi,hki⟩,⟨k,hk,q,hq,hqh,hmk,hkk⟩⟩ :=
    fourth_seven_sources w hw h M m L s U v T hm hs hv h7
  have hfull (a : Nat) (ha : a<T) : seg f 0 (b+a)=(w++y)++List.replicate a true := by
    have hseg : seg f b a=List.replicate a true := by
      apply seg_A
      intro u hu hua
      simpa only [Nat.add_sub_cancel' hu] using hA (u-b) (by omega)
    rw [seg_add,Nat.zero_add,hbase,hseg]
  have hrn : r<n := by omega
  have hdropOld : (w++y).drop r=w.drop r++y := by
    rw [List.drop_append,show r-w.length=0 by omega,List.drop_zero]
  have hwinOld : Win f r (b+i-r) := by
    apply counted_source_win f b i r (w++y) (by omega) (hfull i hi) hl
    · rw [hdropOld,mass_append]
      exact hmi
    · rw [hdropOld,runKey_append]
      exact hki
  have hqb : n+(h-q)<b := by
    have hh : y.length=b-n := by rw [←show seg f n (b-n)=y from hword,seg_length]
    simp only [y,List.length_append,List.length_replicate] at hh
    omega
  have hdropLocal : (w++y).drop (n+(h-q))=List.replicate q false++x := by
    rw [List.drop_append,List.drop_eq_nil_of_le (by omega),List.nil_append,
      show n+(h-q)-w.length=h-q by omega]
    rw [show y=List.replicate h false++x by rfl,List.drop_append,List.drop_replicate,
      List.length_replicate,show h-q-h=0 by omega,List.drop_zero,show h-(h-q)=q by omega]
  have hwinLocal : Win f (n+(h-q)) (b+k-(n+(h-q))) := by
    apply counted_source_win f b k _ (w++y) hqb (hfull k hk) hl
    · rwa [hdropLocal]
    · rwa [hdropLocal]
  have hprior := actual_old_target_prior_clock f n r t (b-n) i T j (hpre ▸ hw) hrn ht (by omega) hj
    (by simpa only [show n+(b-n)=b by omega] using hA)
    (by simpa only [show n+(b-n)=b by omega] using hgap)
    (by simpa only [show n+(b-n)=b by omega] using hwinOld)
    (by simpa only [show n+(b-n)=b by omega] using htarget)
  have hdr : w.drop r=seg f r (n-r) := by
    simpa only [hpre,Nat.zero_add] using seg_drop f 0 n r (by omega)
  have hu := block_suffix hw (w.take r) (w.drop r) (List.take_append_drop r w)
  have htpos : 0<mass (seg f t (n-t)) := by
    have hdt : w.drop t=seg f t (n-t) := by
      simpa only [hpre,Nat.zero_add] using seg_drop f 0 n t (by omega)
    rw [←hdt]
    apply block_suffix_positive hw (w.take t) (w.drop t) (List.take_append_drop t w)
    intro hz
    have hlz := List.length_drop t w
    rw [hz,List.length_nil] at hlz
    omega
  have hD : 2≤mass (w.drop r) := by rw [hdr]; have hp:=hprior.1; omega
  have hsplit : y=List.replicate (h-q) false++(List.replicate q false++x) := by
    rw [←List.append_assoc,←List.replicate_add,show h-q+q=h by omega]
  have hiOrd : k<i := by
    apply initial_clock_before_old (w.drop r) (List.replicate q false++x) (h-q) i k hu hD
    · rw [←hsplit,mass_append]
      exact hmi
    · rw [←hsplit,runKey_append]
      exact hki
    · exact hmk
    · exact hkk
  have hdelay : (h : Int)=(q : Int)+mass (seg f r (n-r))+(i : Int)-(k : Int) := by
    rw [hsplit,hdr,mass_append,mass_append,mass_rep_false,mass_rep_false] at hmi
    omega
  exact ⟨by have hp:=hprior.2; omega,by have hp:=hprior.1; omega,
    r,q,i,k,hrn,hq,hqh,hiOrd,hprior.2,hprior.1,hwinOld,hwinLocal⟩

end Recaman.FourthSaturationClock
