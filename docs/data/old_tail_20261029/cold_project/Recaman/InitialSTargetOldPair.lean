import Recaman.ThreeRunOldTargetGap

namespace Recaman.InitialSTargetOldPair

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.ASourceReuse
open Recaman.RunClockClassifier Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.OldTargetLocalTail Recaman.OldTargetClockCollision
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic

/-- Two old suppliers from one BlockWord cannot choose independent tags:
under the same initial-S target, an old third-ray supplier on the final
band forces the first old supplier beyond clock q+1. -/
theorem first_third_old_clock_order (w : List Bool) (hw : BlockWord w)
    (a b h q M m L s k i T j : Nat) (hj : 2≤j) (hqR : q<j+1) (hband : T≤i+j)
    (hm1 : mass (w.drop a++List.replicate h false)+(k : Int)=1)
    (hk1 : runKey (w.drop a++List.replicate h false)= -2)
    (hm3 : mass (w.drop b++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)+(i : Int)=1)
    (hk3 : runKey (w.drop b++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)= -2)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) : q+2≤k := by
  let v := List.replicate M true++List.replicate m false++List.replicate L true++List.replicate s false
  let C := mass (w.drop b++List.replicate h false)
  let K := (cntF v : Int)
  let R : Int := (j : Int)+1
  have hm : C+(q : Int)≤0 := by
    simp only [mass_append,mass_rep_false,mass_replicate_A] at hm3 hmt
    dsimp [C]
    rw [mass_append,mass_rep_false]
    omega
  have ht := source_key_before_gap (List.replicate q false++v) T j
    (by simpa only [v,List.append_assoc] using hmt)
    (by simpa only [v,List.append_assoc] using hat)
  rw [runKey_prepend_S] at ht
  have h3 : runKey ((w.drop b++List.replicate h false)++v)= -2 := by
    simpa only [v,List.append_assoc] using hk3
  rw [runKey_append] at h3
  have hprod := Int.mul_nonpos_of_nonpos_of_nonneg hm (show 0≤K by dsimp [K]; omega)
  have hRq := Int.mul_nonneg (show 0≤R-1-(q : Int) by dsimp [R]; omega)
    (show 0≤R-1+(q : Int) by dsimp [R]; omega)
  have hkey : runKey (w.drop a++List.replicate h false)+9≤
      runKey (w.drop b++List.replicate h false) := by
    dsimp [C,K,R] at *
    grind
  have horder := Recaman.OldSourceKeyOrder.old_key_mass_order w (List.replicate h false) hw b a hkey
  simp only [mass_append,mass_rep_false] at hm1
  dsimp [C] at hm
  simp only [mass_append,mass_rep_false] at hm
  omega

/-- If an old third-ray clock exists on the final band and the first run
is short, no old supplier can also occupy its first-run clocks. -/
theorem third_old_excludes_first_old (w : List Bool) (hw : BlockWord w)
    (h q M m L s i T j : Nat) (hj : 2≤j) (hqR : q<j+1) (hband : T≤i+j) (hM : M≤q+2)
    (hthird : tailOldRay w (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) i)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    ∀ k, k<M → ¬tailOldRay w (List.replicate h false) k := by
  rintro k hk ⟨a,ha,hm1,hk1⟩
  obtain ⟨b,hb,hm3,hk3⟩ := hthird
  have h1m : mass (w.drop a++List.replicate h false)+(k : Int)=1 := by rw [mass_append]; exact hm1
  have h1k : runKey (w.drop a++List.replicate h false)= -2 := by rw [runKey_append]; exact hk1
  have h3m : mass (w.drop b++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)+(i : Int)=1 := by
    simpa only [mass_append,List.append_assoc] using hm3
  have h3k : runKey (w.drop b++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false)= -2 := by
    have hh : runKey (w.drop b++(List.replicate h false++List.replicate M true++List.replicate m false++
        List.replicate L true++List.replicate s false))= -2 := by rw [runKey_append]; exact hk3
    simpa only [List.append_assoc] using hh
  have ho := first_third_old_clock_order w hw a b h q M m L s k i T j hj hqR hband h1m h1k h3m h3k hmt hat
  omega

theorem first_ray_le_one_of_third_old (w : List Bool) (hw : BlockWord w)
    (h q M m L s i T j : Nat) (hj : 2≤j) (hqR : q<j+1) (hband : T≤i+j) (hM : M≤q+2)
    (hthird : tailOldRay w (List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false) i)
    (hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1)
    (hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0) :
    rayCount (w++List.replicate h false) M≤1 := by
  have hn := third_old_excludes_first_old w hw h q M m L s i T j hj hqR hband hM hthird hmt hat
  unfold rayCount
  apply cN_le_one_of_unique
  intro a ha b hb hsa hsb
  have hlocal (k : Nat) (hk : k<M)
      (hs : Recaman.ThreeNonsuppliedData.localSupply
        ((w++List.replicate h false)++List.replicate k true)=true) : k=2 := by
    rcases (ray_supply_append_iff w (List.replicate h false) k).mp hs with ho|hl
    · exact False.elim (hn k hk ho)
    · have hh := (localSupply_three_runs_iff h k 0).mp (by simpa only [List.replicate_zero,List.append_nil] using hl)
      omega
  exact (hlocal a ha hsa).trans (hlocal b hb hsb).symm

private theorem actual_old_root (f : Nat → Bool) (n b i t : Nat) (w v : List Bool)
    (hnb : n≤b) (hw : seg f 0 n=w) (hv : seg f n (b-n)=v)
    (ha : seg f b i=List.replicate i true) (ht : t<n)
    (hwin : Win f t (b+i-t)) : tailOldRay w v i := by
  have hn : w.length=n := by rw [←hw,seg_length]
  have hbase := seg_add f 0 n (b-n)
  simp only [Nat.zero_add,hw,hv,Nat.add_sub_cancel' hnb] at hbase
  have hfull := seg_add f 0 b i
  simp only [Nat.zero_add,hbase,ha] at hfull
  rw [List.append_assoc] at hfull
  have hd := seg_drop f 0 (b+i) t (by omega)
  simp only [Nat.zero_add,Nat.sub_zero] at hd
  have hsuf : seg f t (b+i-t)=(w.drop t++v)++List.replicate i true := by
    rw [←hd,hfull,List.drop_append,show t-w.length=0 by omega,List.drop_zero,←List.append_assoc]
  have hm : mass (seg f t (b+i-t))=1 := by
    rw [seg_mass,show t+(b+i-t)=b+i by omega]
    have hl := hwin.2.1
    rw [show t+(b+i-t)=b+i by omega] at hl
    omega
  have harea : areaW (seg f t (b+i-t))=0 := by
    rw [←Ar_areaW]
    exact hwin.2.2
  have hk : runKey (seg f t (b+i-t))=-2 := by
    unfold runKey
    rw [hm,harea]
    decide
  rw [hsuf,mass_append,mass_append,mass_replicate_A] at hm
  rw [hsuf,runKey_append_A,runKey_append] at hk
  exact ⟨t,by omega,hm,hk⟩

theorem actual_first_supply_le_one (f : Nat → Bool)
    (n z h q M m L s i T j : Nat) (w : List Bool) (hw : BlockWord w)
    (hpre : seg f 0 n=w) (hz : z<n) (hqh : q≤h) (hi : i<T)
    (hj : 2≤j) (hqR : q<j+1) (hband : T≤i+j) (hM : M≤q+2)
    (hS : ∀ x, n≤x → x<n+h → f x=false)
    (hA : ∀ k, k<M → f (n+h+k)=true)
    (hS2 : ∀ x, n+h+M≤x → x<n+h+M+m → f x=false)
    (hA2 : ∀ k, k<L → f (n+h+M+m+k)=true)
    (hS3 : ∀ x, n+h+M+m+L≤x → x<n+h+M+m+L+s → f x=false)
    (hA3 : ∀ k, k<T → f (n+h+M+m+L+s+k)=true)
    (hgap : ∀ x, n+h+M+m+L+s+T≤x → x<n+h+M+m+L+s+T+j → f x=false)
    (htarget : Win f (n+h-q) (q+M+m+L+s+T+j))
    (hthird : Win f z (n+h+M+m+L+s+i-z)) :
    cN (EndN f 0) (n+h) M≤1 := by
  have htargetword := Recaman.InitialSTargetBounds.initial_S_source_word f n h q M m L s T j hqh
    hS hA hS2 hA2 hS3 hA3 hgap
  have hmt : mass (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=1 := by
    rw [←htargetword,seg_mass]
    have hh := htarget.2.1
    omega
  have hat : areaW (List.replicate q false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate T true++List.replicate j false)=0 := by
    rw [←htargetword,←Ar_areaW]
    exact htarget.2.2
  let v := List.replicate h false++List.replicate M true++List.replicate m false++List.replicate L true++
    List.replicate s false
  let b := n+h+M+m+L+s
  have hv : seg f n (b-n)=v := by
    have hh := Recaman.SeparatorSupplyReset.three_run_word f n h M m L s 0 hS hA hS2 hA2 hS3
      (by intro k hk; omega)
    simpa only [b,show n+h+M+m+L+s-n=h+M+m+L+s by omega,Nat.add_zero,
      List.replicate_zero,List.append_nil] using hh
  have hAi : seg f b i=List.replicate i true := by
    apply seg_A
    intro x hx hxi
    have hh := hA3 (x-b) (by omega)
    change f (b+(x-b))=true at hh
    simpa only [Nat.add_sub_cancel' hx] using hh
  have ho := actual_old_root f n b i z w v (by dsimp [b]; omega) hpre hv hAi hz hthird
  have hb := first_ray_le_one_of_third_old w hw h q M m L s i T j hj hqR hband hM ho hmt hat
  have hfirst : seg f 0 (n+h)=w++List.replicate h false := by
    rw [seg_add,show 0+n=n by omega,hpre,seg_false f n h hS]
  have hcount := endable_A_run_count f (n+h) M (w++List.replicate h false) hfirst hA
  omega

end Recaman.InitialSTargetOldPair
