module
public import CatalanCore.Cert.QuarterCompute.ModelDefs
public import CatalanCore.Cert.QuarterContour.LogModelDyadic
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.Polynomial

lemma logUp_eq (N : ℕ) : Model.logUpS N = CatalanLambda.Cert.logUpS N := by rfl

lemma ceil_real_ge (n d : ℕ) (hd : 0 < d) :
    (n : ℝ)/(d : ℝ) ≤ (((n+d-1)/d : ℕ) : ℝ) := by
  have h := CatalanLambda.Cert.ceil_div_ge n d hd
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast h

lemma centre_log_upper (m : Params) (p : Pt) (hU : 0 < m.U) (hq : 0 < q0N m p) :
    Real.log ((q0N m p : ℝ)/(m.U : ℝ)^2) ≤ (Model.logUpS (centreArg m p) : ℝ)/2^64 := by
  have hqN : 0 < (q0N m p).toNat := by omega
  have hd : 0 < m.U^2 := by positivity
  have hbound := CatalanLambda.Cert.ceil_div_ge ((q0N m p).toNat*2^80) (m.U^2) hd
  change (q0N m p).toNat*2^80 ≤ centreArg m p*m.U^2 at hbound
  have harg : 0 < centreArg m p := by
    by_contra hz
    have he : centreArg m p = 0 := Nat.eq_zero_of_not_pos hz
    rw [he,zero_mul] at hbound
    have hp : 0 < (q0N m p).toNat*2^80 := by positivity
    omega
  have hcast : ((q0N m p).toNat : ℝ) = (q0N m p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hq)
  have hboundR : (q0N m p : ℝ)*2^80 ≤ (centreArg m p : ℝ)*(m.U : ℝ)^2 := by
    have h := (show (((q0N m p).toNat*2^80 : ℕ) : ℝ) ≤ ((centreArg m p*m.U^2 : ℕ) : ℝ) by exact_mod_cast hbound)
    push_cast at h
    rw [hcast] at h
    convert h using 1 <;> norm_num
  have hUr : 0 < (m.U : ℝ) := by exact_mod_cast hU
  have hqr : 0 < (q0N m p : ℝ) := by exact_mod_cast hq
  have hfrac : (q0N m p : ℝ)/(m.U : ℝ)^2 ≤ (centreArg m p : ℝ)/2^80 :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr hboundR
  exact (Real.log_le_log (by positivity) hfrac).trans (by
    rw [logUp_eq]
    exact CatalanLambda.Cert.logUpS_spec harg)

end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.centre_log_upper
