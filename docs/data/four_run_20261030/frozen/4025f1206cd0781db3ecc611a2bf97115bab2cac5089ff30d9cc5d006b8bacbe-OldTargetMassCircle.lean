import Recaman.LargePrefixTargetArea

namespace Recaman.OldTargetMassCircle

open Recaman.LeadingRunSupply Recaman.BlockSuffixPositivity Recaman.PrefixMassBarrier
open Recaman.BlockOldRay Recaman.RunSupplyKeys Recaman.RunSupplyBudget Recaman.TwoRunSupply
open Recaman.SourceFamilyFreeCount Recaman.ASourceReuse Recaman.RunClockClassifier
open Recaman.CapacityEqualityInduction Recaman.SingleWindowEquality Recaman.LineCapacityPeriodic
open Recaman.FourRunTargetArea

/-- A measured A budget bounds only the target old suffix mass. It does
not bound other suppliers or permit erasing earlier actual history. -/
theorem target_mass_circle (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j budget : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2)
    (hbudget : M+L+U+T≤j+1+budget)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    (mass u)^2+((j : Int)+1)^2≤((budget : Int)-1)^2-4 := by
  let A : Int:=(M : Int)+(L : Int)+(U : Int)+(T : Int)
  let R : Int:=(j : Int)+1
  let I : Int:=(M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he:=old_target_area_identity u h M m L s U v T j hmass harea
  have hl:=block_area_quadratic_lower hu
  have hAlo:=old_target_short_last_A_budget u hu hne h M m L s U v T j
    hM hm hL hs hU hv hshort hmass harea
  have hpM:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hpL:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)+(v : Int)-2 by omega)
  have hpU:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : A-R+2≤I := by dsimp [A,R,I]; grind only
  have hq : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [A,R,I]; grind only
  have hx : 0≤A-R-1 := by dsimp [A,R]; omega
  have hxb : A-R-1≤(budget : Int)-1 := by dsimp [A,R]; omega
  have hp:=Int.mul_nonneg (show 0≤(budget : Int)-1-(A-R-1) by omega)
    (show 0≤(budget : Int)-1+(A-R-1) by omega)
  have hb : (A-R-1)^2≤((budget : Int)-1)^2 := by grind only
  change (mass u)^2+R^2≤((budget : Int)-1)^2-4
  grind only

/-- If the first-two-run A count is large, the cross term is at least A
and gives the tighter circle with R+1. -/
theorem large_prefix_mass_circle (u : List Bool) (hu : BlockWord u) (hne : u≠[])
    (h M m L s U v T j budget : Nat) (hM : 1≤M) (hm : 1≤m) (hL : 1≤L)
    (hs : 1≤s) (hU : 1≤U) (hv : 1≤v) (hshort : T≤j+2) (hML : j+1≤M+L)
    (hbudget : M+L+U+T≤j+1+budget)
    (hmass : mass (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=1)
    (harea : areaW (u++List.replicate h false++List.replicate M true++List.replicate m false++
      List.replicate L true++List.replicate s false++List.replicate U true++List.replicate v false++
      List.replicate T true++List.replicate j false)=0) :
    (mass u)^2+((j : Int)+2)^2≤((budget : Int)-1)^2+1 := by
  let A : Int:=(M : Int)+(L : Int)+(U : Int)+(T : Int)
  let R : Int:=(j : Int)+1
  let I : Int:=(M : Int)*((m : Int)+(s : Int)+(v : Int))+
    (L : Int)*((s : Int)+(v : Int))+(U : Int)*(v : Int)
  have he:=old_target_area_identity u h M m L s U v T j hmass harea
  have hl:=block_area_quadratic_lower hu
  have hAlo:=old_target_short_last_A_budget u hu hne h M m L s U v T j
    hM hm hL hs hU hv hshort hmass harea
  have hpM:=Int.mul_nonneg (show 0≤(M : Int) by omega) (show 0≤(m : Int)+(s : Int)+(v : Int)-3 by omega)
  have hpL:=Int.mul_nonneg (show 0≤(L : Int) by omega) (show 0≤(s : Int)+(v : Int)-2 by omega)
  have hpU:=Int.mul_nonneg (show 0≤(U : Int) by omega) (show 0≤(v : Int)-1 by omega)
  have hI : A≤I := by dsimp [A,I]; grind only
  have hq : (mass u)^2+2*I≤A*(A-2*R)+1 := by dsimp [A,R,I]; grind only
  have hx : 0≤A-R-1 := by dsimp [A,R]; omega
  have hxb : A-R-1≤(budget : Int)-1 := by dsimp [A,R]; omega
  have hp:=Int.mul_nonneg (show 0≤(budget : Int)-1-(A-R-1) by omega)
    (show 0≤(budget : Int)-1+(A-R-1) by omega)
  have hb : (A-R-1)^2≤((budget : Int)-1)^2 := by grind only
  have heq : ((j : Int)+2)^2=(R+1)^2 := by dsimp [R]; grind only
  rw [heq]
  grind only


theorem actual_target_mass_circle (f : Nat → Bool) (n t h M m L s U v T j budget : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hshort : T≤j+2) (hbudget : M+L+U+T≤j+1+budget)
    (hword : seg f n (h+M+m+L+s+U+v+T)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hwin : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    (Fw f n-Fw f t)^2+((j : Int)+1)^2≤((budget : Int)-1)^2-4 := by
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
  have hb := target_mass_circle u hu hne h M m L s U v T j budget hM hm hL hs hU hv hshort hbudget hmwin hawin
  have hmu : mass u=Fw f n-Fw f t := by
    rw [u,hd,seg_mass,show t+(n-t)=n by omega]
  rw [hmu] at hb
  exact hb

theorem actual_large_prefix_mass_circle (f : Nat → Bool) (n t h M m L s U v T j budget : Nat)
    (w : List Bool) (hw : BlockWord w) (hpre : seg f 0 n=w) (ht : t<n)
    (hM : 1≤M) (hm : 1≤m) (hL : 1≤L) (hs : 1≤s) (hU : 1≤U) (hv : 1≤v)
    (hshort : T≤j+2) (hML : j+1≤M+L) (hbudget : M+L+U+T≤j+1+budget)
    (hword : seg f n (h+M+m+L+s+U+v+T)=List.replicate h false++List.replicate M true++
      List.replicate m false++List.replicate L true++List.replicate s false++
      List.replicate U true++List.replicate v false++List.replicate T true)
    (hgap : ∀ x, n+h+M+m+L+s+U+v+T≤x → x<n+h+M+m+L+s+U+v+T+j → f x=false)
    (hwin : Win f t (n+h+M+m+L+s+U+v+T+j-t)) :
    (Fw f n-Fw f t)^2+((j : Int)+2)^2≤((budget : Int)-1)^2+1 := by
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
  have hb := large_prefix_mass_circle u hu hne h M m L s U v T j budget hM hm hL hs hU hv hshort hML hbudget hmwin hawin
  have hmu : mass u=Fw f n-Fw f t := by
    rw [u,hd,seg_mass,show t+(n-t)=n by omega]
  rw [hmu] at hb
  exact hb

end Recaman.OldTargetMassCircle
