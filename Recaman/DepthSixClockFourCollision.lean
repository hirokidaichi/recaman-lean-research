import Recaman.DepthSixClockFourHighWindow

namespace Recaman.DepthSixClockFourCollision

open Recaman.DepthSixClockFourHighWindow Recaman.DepthSixClockFourPrefix Recaman.FirstSFourPrefix
open Recaman.DepthSixGapResidual Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction

/-- The clock-four source branch is excluded by two internally supplied
high SAA windows, whose overlapping clocks demand opposite signs. -/
theorem clock_four_actual_counter_excluded (f : Nat → Bool) (n a b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n=w++List.replicate a true)
    (hnb : n<b) (hfloor : ∀ i, n≤i → i≤b → Fw f n-6≤Fw f i)
    (hpos : ∀ k, 0<k → k≤b-n → cN (EndN f 0) n k+1≤cN (fun i => f i=false) n k)
    (hS : ∀ i, b≤i → i<b+j → f i=false) (he : EndN f 0 (b+j))
    (hcounter : cN (fun i => f i=true ∧ ¬EndN f 0 i) n (b-n)≤j)
    (hj : j=4 ∨ j=5) (htb : n+4<b) (hwin : Win f (n+4) (b+j-(n+4))) : False := by
  obtain ⟨hWords,_,_,hActual⟩ := clock_four_actual_prefix_packet f n a b j hw hpre hnb hfloor hpos hS he hcounter hj htb hwin
  obtain ⟨_,_,_,hTarget,_⟩ := positive_depth_six_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
  have hLevel := hwin.2.1
  rw [show n+4+(b+j-(n+4))=b+j by omega] at hLevel
  have hEnd : Fw f (n+4)=Fw f n-2 := by omega
  have hnS : f n=false := by
    have hGet := seg_get f n 4 0 (by decide)
    rcases hWords with h | h | h <;> rw [h] at hGet <;> exact (Option.some.inj hGet).symm
  have hCeil := first_S_four_ceiling f n hnS hEnd
  have hDown := fw_false_run f b j hS
  have hJ : 4≤j ∧ j≤5 := by omega
  obtain ⟨q,hq4,hqb,hq,hqA⟩ := ivt f b (Fw f n+(j : Int)-1) (by omega)
    (b-(n+4)) (n+4) (by omega) (by omega)
  have hqe := hActual q hq4 hqb (by omega) hqA
  obtain ⟨u,hnu,huq,huH,hWin⟩ := clock_four_high_source_SAA f n a b j q ((j : Int)-1) hw hpre
    hnb hfloor hpos hS he hcounter hj htb hwin (by omega) hqb (by omega) (by omega) hqe
  have hnu4 : n+4≤u := by
    by_cases h : n+4≤u
    · exact h
    · have hh := hCeil u hnu (by omega)
      omega
  obtain ⟨hSu,_,hA2⟩ := win3 f u hWin
  have hPrevA : f (q-1)=true := by rwa [show q-1=u+2 by omega]
  have hPrevF : Fw f (q-1)=Fw f n+(j : Int)-3 := by
    rcases fw_cases f (q-1) with ⟨h,_⟩ | ⟨_,h⟩
    · rw [show q-1+1=q by omega] at h
      omega
    · simp [hPrevA] at h
  have hPrevE := hActual (q-1) (by omega) (by omega) (by omega) hPrevA
  obtain ⟨v,_,hvq,_,hInner⟩ := clock_four_high_source_SAA f n a b j (q-1) ((j : Int)-2) hw hpre
    hnb hfloor hpos hS he hcounter hj htb hwin (by omega) (by omega) (by omega) (by omega) hPrevE
  have hA := (win3 f v hInner).2.1
  rw [show v+1=u by omega] at hA
  simp [hSu] at hA

end Recaman.DepthSixClockFourCollision
