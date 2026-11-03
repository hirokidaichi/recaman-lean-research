import Recaman.ShortCounterFactorBounds

namespace Recaman.MassTwoSmallHeadKey

private theorem quadratic_upper (x b : Int) (hx : 3≤x) (hxb : x≤b) :
    x^2-4*x≤b^2-4*b := by
  have hp:=Int.mul_nonneg (show 0≤b-x by omega) (show 0≤b+x-4 by omega)
  have he : (b-x)*(b+x-4)=b^2-4*b-(x^2-4*x) := by grind only
  omega

theorem late_small_free_key_excluded (S v R K r ku : Int)
    (hr1 : 1≤r) (hr3 : r≤3) (hcost : r+v≤8) (hv : 5≤v)
    (hS3 : 3≤S) (hS : S≤2*r+1) (hR : 5≤R) (hK : 3≤K) (hku : -2≤ku)
    (hkey : ku=2*S^2-4*K-8*(S+v)+2*v^2-2*R^2) : False := by
  have hR5:=Recaman.ShortCounterFactorBounds.square_lower R 5 (by omega) hR
  rcases (show r=1 ∨ r=2 ∨ r=3 by omega) with rfl|rfl|rfl
  · have hs:=quadratic_upper S 3 hS3 (by omega)
    have hv:=quadratic_upper v 7 (by omega) (by omega)
    omega
  · have hs:=quadratic_upper S 5 hS3 (by omega)
    have hv:=quadratic_upper v 6 (by omega) (by omega)
    omega
  · have hs:=quadratic_upper S 7 hS3 (by omega)
    have hv:=quadratic_upper v 5 (by omega) (by omega)
    omega

private theorem positive_quadratic_upper (x b : Int) (hx : 1≤x) (hb : 3≤b) (hxb : x≤b) :
    x^2-4*x≤b^2-4*b := by
  have hp:=Int.mul_nonneg (show 0≤b-x by omega) (show 0≤b+x-4 by omega)
  have he : (b-x)*(b+x-4)=b^2-4*b-(x^2-4*x) := by grind only
  omega

theorem no_old_small_free_key_excluded (S v R K r ku : Int)
    (hr1 : 1≤r) (hr3 : r≤3) (hcost : r+v≤7) (hv : 1≤v)
    (hS3 : 3≤S) (hS : S≤2*r+1) (hR : 5≤R) (hK : 0≤K) (hku : -2≤ku)
    (hkey : ku=2*S^2-4*K-8*(S+v)+2*v^2-2*R^2) : False := by
  have hR5:=Recaman.ShortCounterFactorBounds.square_lower R 5 (by omega) hR
  rcases (show r=1 ∨ r=2 ∨ r=3 by omega) with rfl|rfl|rfl
  · have hs:=positive_quadratic_upper S 3 (by omega) (by omega) (by omega)
    have hv:=positive_quadratic_upper v 6 (by omega) (by omega) (by omega)
    omega
  · have hs:=positive_quadratic_upper S 5 (by omega) (by omega) (by omega)
    have hv:=positive_quadratic_upper v 5 (by omega) (by omega) (by omega)
    omega
  · have hs:=positive_quadratic_upper S 7 (by omega) (by omega) (by omega)
    have hv:=positive_quadratic_upper v 4 (by omega) (by omega) (by omega)
    omega

end Recaman.MassTwoSmallHeadKey
