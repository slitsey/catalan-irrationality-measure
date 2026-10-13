module
public import CatalanMeasure.PopulationFields
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace CatalanMeasure.Parametric

/-- A uniform first-case missing-mass estimate, including zero missing mass. -/
theorem first_population_missing_mass_le {C Q delta t : ℝ}
    (hC : C ≤ 481/100) (hQ : Q ≤ -(53/50)) (hdelta : 8/125 ≤ delta) (ht : 0 ≤ t) :
    -delta+t*(C+Q*t) ≤ (43/10)*t :=by
  have hCt :=mul_le_mul_of_nonneg_right hC ht
  have hQt :=mul_le_mul_of_nonneg_right hQ (sq_nonneg t)
  nlinarith only [hCt,hQt,hdelta,sq_nonneg (t-51/212)]

theorem second_population_missing_mass_le {C Q t : ℝ}
    (hC : C ≤ 43/10) (hQ : Q ≤ 0) (ht : 0 ≤ t) :
    t*(C+Q*t) ≤ (43/10)*t :=by
  have hCt :=mul_le_mul_of_nonneg_right hC ht
  have hQt :=mul_nonpos_of_nonpos_of_nonneg hQ (sq_nonneg t)
  nlinarith only [hCt,hQt]

/-- Both cases can use the same rational perturbation budget after interpolation. -/
theorem first_population_endpoint_le {K0 K1 B0 B1 Y0 Y1 U t : ℝ}
    (ht : 0 ≤ t) (hdelta : K0+B0 ≤ U-8/125)
    (hC : K1-K0+B1-2*B0+Y0+2*Real.log 2 ≤ 481/100)
    (hQ : B0-B1+Y1-Y0-Real.log 2 ≤ -(53/50)) :
    (1-t)*(K0+(1-t)*B0+t*Y0)+t*(K1+(1-t)*B1+t*Y1)+(2*t-t^2)*Real.log 2 ≤
      U+(43/10)*t :=by
  rw [OAI.InternalCatalan.population_endpoint_quadratic]
  have hh :=first_population_missing_mass_le hC hQ (by rfl : (8/125:ℝ) ≤ 8/125) ht
  nlinarith only [hh,hdelta]

end CatalanMeasure.Parametric
