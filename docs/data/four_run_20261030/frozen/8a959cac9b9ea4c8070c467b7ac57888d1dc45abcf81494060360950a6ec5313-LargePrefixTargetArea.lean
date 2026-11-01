import Recaman.FourRunTargetArea

namespace Recaman.LargePrefixTargetArea

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea

/-- When the first two A runs already contain R signs, the same target
area rules out the even boundary A=2R+2. This is an A count, not free. -/
theorem large_first_two_A_budget (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2) (hML : j+1≤M+L)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    2*(j+1)+3≤M+L+U+T := by
  have hb:=old_target_short_last_A_budget u hu hne h M m L s U v T j
    hM hm hL hs hU hv hshort hmass harea
  let A : Int := (M : Int)+(L : Int)+(U : Int)+(T : Int)
  let R : Int := (j : Int)+1
  let I : Int := (M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he:=old_target_area_identity u h M m L s U v T j hmass harea
  have hlow:=block_area_quadratic_lower hu
  have hC : 1≤mass u := (sufPos_block hu [] u rfl hne).1
  have hmp:=Int.mul_nonneg (show 0≤(M : Int) by omega)
    (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hlp:=Int.mul_nonneg (show 0≤(L : Int) by omega)
    (show 0≤(s : Int)+(v : Int)-2 by omega)
  have hup:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : A≤I := by dsimp [A,I]; grind only
  by_cases hh : 2*(j+1)+3≤M+L+U+T
  · exact hh
  · have hAe : A=2*R+2 := by dsimp [A,R]; omega
    have hq : mass u*mass u+2*I≤A*(A-2*R)+1 := by dsimp [A,R,I]; grind only
    have hq' : mass u*mass u≤1 := by
      have hhq : A*(A-2*R)=2*A := by rw [hAe]; grind only
      rw [hhq] at hq
      omega
    have hC1 : mass u=1 := by
      by_cases hhC : mass u=1
      · exact hhC
      · have hp:=Int.mul_nonneg (show 0≤mass u-2 by omega) (show 0≤mass u+2 by omega)
        have h4 : 4≤mass u*mass u := by grind only
        omega
    have huA:=block_mass_one hu hC1
    rw [huA] at he
    have hmA : mass [true]=1 := by decide
    have haA : areaW [true]=1 := by decide
    rw [hmA,haA] at he
    have he' : 2=2*A*(A-2*R)-4*I := he
    rw [hAe] at he'
    have hz : 2*I=2*R*2+3 := by grind only
    omega

/-- Same actual old window, with all earlier history retained. -/
theorem actual_large_first_two_A_budget (f : Nat → Bool) (n t h M m L s U v T j : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hshort : T≤j+2) (hML : j+1≤M+L)
    (hword : seg f n (h+M+m+L+s+U+v+T)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hwin : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    2*(j+1)+3≤cN (fun x=>f x=true) n (h+M+m+L+s+U+v+T) := by
  let B:=h+M+m+L+s+U+v+T
  let u:=w.drop t
  have hwin' : Win f t (n+B+j-t) := by simpa only [B,Nat.add_assoc] using hwin
  have hn : w.length=n := by rw [←hpre,seg_length]
  have hu : BlockWord u := block_suffix hw (w.take t) u (List.take_append_drop t w)
  have hne : u≠[] := by
    intro hh
    have hlen : (w.drop t).length=w.length-t := List.length_drop
    change (w.drop t)=[] at hh
    rw [hh,hn] at hlen
    simp only [List.length_nil] at hlen
    omega
  have hd := seg_drop f 0 n t (by omega)
  simp only [Nat.zero_add,hpre] at hd
  have hfull : seg f t (n+B+j-t)=u++List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false := by
    rw [show n+B+j-t=(n-t)+(B+j) by omega,seg_add,show t+(n-t)=n by omega,←hd,
      seg_add,show n+B=n+h+M+m+L+s+U+v+T by omega,
      seg_false f (n+h+M+m+L+s+U+v+T) j hgap,hword]
    simp only [u,List.append_assoc]
  have hmwin : mass (u++List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=1 := by
    rw [←hfull,seg_mass]
    have hh:=hwin'.2.1
    rw [show t+(n+B+j-t)=n+B+j by omega] at hh
    rw [show t+(n+B+j-t)=n+B+j by omega]
    omega
  have hawin : areaW (u++List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true++List.replicate j false)=0 := by
    rw [←hfull,←Ar_areaW]
    exact hwin'.2.2
  have hb := large_first_two_A_budget u hu hne h M m L s U v T j hM hm hL hs hU hv hshort hML hmwin hawin
  have ha:=ones_seg_eq_count f n B
  change ones (seg f n (h+M+m+L+s+U+v+T))=_ at ha
  rw [hword] at ha
  simp only [ones_append,ones_replicate_A,ones_replicate_S] at ha
  dsimp only [B] at ha
  omega

/-- A raw boundary family. For r>=1 all four runs/separators are
genuine, M+L=R and total A=2R+3. No actual free-count claim is made. -/
theorem large_first_two_raw_boundary (r : Nat) :
    let b := List.replicate 6 false++List.replicate 1 true++List.replicate r false++
      List.replicate (r+1) true++List.replicate 1 false++List.replicate 2 true++List.replicate 1 false
    mass (List.replicate 3 true++b++List.replicate (r+3) true++List.replicate (r+1) false)=1 ∧
    areaW (List.replicate 3 true++b++List.replicate (r+3) true++List.replicate (r+1) false)=0 ∧
    (1+(r+1)+2+(r+3) : Nat)=2*((r+1)+1)+3 := by
  dsimp only
  let b := List.replicate 6 false++List.replicate 1 true++List.replicate r false++
    List.replicate (r+1) true++List.replicate 1 false++List.replicate 2 true++List.replicate 1 false
  have hmB : mass b= -4 := by
    simp only [b,mass_append,mass_rep_false,mass_replicate_A]
    omega
  have hcB : cntF b=r+8 := by
    have hA0 (k : Nat) : cntF (List.replicate k true)=0 := by
      have hh:=cntF_int (List.replicate k true)
      rw [List.length_replicate,ones_replicate_A] at hh
      omega
    simp only [b,cntF_append,cntF_replicate_S,hA0]
    omega
  have hkB:=runKey_seven_runs 6 1 r (r+1) 1 2 1
  change runKey b=_ at hkB
  have hk0 : runKey (List.replicate 3 true++b)= -2*((r : Int)+2)^2 := by
    rw [runKey_append,hkB,hcB,mass_replicate_A]
    have hku : runKey (List.replicate 3 true)=0 := by decide
    rw [hku]
    grind only
  have hm0 : mass (List.replicate 3 true++b++List.replicate (r+3) true)=(r : Int)+2 := by
    rw [mass_append,mass_append,mass_replicate_A,mass_replicate_A,hmB]
    omega
  have hm : mass (List.replicate 3 true++b++List.replicate (r+3) true++List.replicate (r+1) false)=1 := by
    rw [mass_append,hm0,mass_rep_false]
    omega
  have hk := runKey_append_S (List.replicate 3 true++b++List.replicate (r+3) true) (r+1)
  rw [runKey_append_A,hk0,hm0] at hk
  have hk' : runKey (List.replicate 3 true++b++List.replicate (r+3) true++List.replicate (r+1) false)= -2 := by grind only
  unfold runKey at hk'
  rw [hm] at hk'
  change mass (List.replicate 3 true++b++List.replicate (r+3) true++List.replicate (r+1) false)=1 ∧
    areaW (List.replicate 3 true++b++List.replicate (r+3) true++List.replicate (r+1) false)=0 ∧ _
  exact ⟨hm,by omega,by omega⟩

end Recaman.LargePrefixTargetArea
