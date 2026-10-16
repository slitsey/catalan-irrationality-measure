module
public import CatalanMeasure.Parametric.SecondaryTentSourceSectors

/-! Elementary rational coordinates of the actual source substitution. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem secondaryTent_source_coordinate_curve {K : Type*} [Field K]
    (z : K) (h2 : (2:K)≠0) (hz : z≠0) :
    ((z^2-1)/(2*z))^2=((1+z^2)/(2*z))^2-1 := by
  field_simp [h2, hz]
  <;> ring

theorem secondaryTent_source_coordinate_jacobian {K : Type*} [Field K]
    (z : K) (h2 : (2:K)≠0) (hz : z≠0) (hq : 1+z^2≠0) :
    (1-z^2)/(1+z^2) = -((z^2-1)/(2*z))/((1+z^2)/(2*z)) := by
  field_simp [h2, hz, hq]
  <;> ring

theorem secondaryTent_source_coordinate_b0 {K : Type*} [Field K]
    (z : K) (h2 : (2:K)≠0) (hz : z≠0) (hq : 1+z^2≠0) :
    z^4*(z-1)/(1+z^2)^4 =
      (((1+z^2)/(2*z))-1+((z^2-1)/(2*z))) /
        (16*((1+z^2)/(2*z))^4) := by
  have h16 : (16:K)≠0 := by convert pow_ne_zero 4 h2 using 1 <;> norm_num
  field_simp [h2, hz, hq, h16]
  <;> ring

theorem secondaryTent_source_inverse_t {p : ℕ} [Fact p.Prime] (hp2 : p≠2) :
    (palindromicRatT p)⁻¹ =
      (1+palindromicRatW p^2)/(2*palindromicRatW p) := by
  rw [palindromicRatT, inv_div]

end
end CatalanMeasure.Parametric
