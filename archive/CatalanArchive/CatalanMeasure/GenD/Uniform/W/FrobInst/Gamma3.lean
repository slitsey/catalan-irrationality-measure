module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.Gamma2
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W Matrix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem sourceM_eq (hp2 : p ≠ 2) (hp3 : p ≠ 3) (J v : ℕ) (a : ℤ) (b : ℕ) (hb : b ∣ 72)
    (hb0 : b ≠ 0) (h : momentRatSigned ((v : ℤ) - 1) J = (a : ℚ) / (b : ℚ)) :
    sourceM (p := p) J v = (a : ZMod p) / (b : ZMod p) := by
  unfold sourceM
  rw [h]
  exact palRes_div a b (unit_of_dvd_72 hp2 hp3 b hb hb0)

theorem sourceZ_eq (hp2 : p ≠ 2) (hp3 : p ≠ 3) (J v : ℕ) (a : ℤ) (b : ℕ) (hb : b ∣ 72)
    (hb0 : b ≠ 0) (h : zetaRat v J = (a : ℚ) / (b : ℚ)) :
    sourceZ (p := p) J v = (a : ZMod p) / (b : ZMod p) := by
  unfold sourceZ
  rw [h]
  exact palRes_div a b (unit_of_dvd_72 hp2 hp3 b hb hb0)

theorem psiLinH_cutoff (H : ℕ) (hH : 4 ≤ H) (J : ℕ) (y : Fin 2 → ZMod p) :
    psiLinH p 2 0 H J 3 y =
      digitPhi 4 3 (sourceM (p := p) J) (sourceZ (p := p) J) (gyH p 2 0 y) (tyH p 2 0 y) (3 / 2) := by
  show digitPhi H 3 _ _ _ _ _ = _
  exact digitPhi_cutoff_signed H 4 3 hH (by norm_num) _ _ _ _ _

theorem gyH_e1' : gyH p 2 0 (Pi.single 1 1) = 2 * X ^ 3 - X ^ 2 - 2 * X + (1 : (ZMod p)[X]) := by
  rw [gyH_e1]; ring

theorem tyH_e1' : tyH p 2 0 (Pi.single 1 1) = 2 * X ^ 2 - X - (1 : (ZMod p)[X]) := by
  rw [tyH_e1]; ring

theorem gam_1_0 (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    digitPhi 4 3 (sourceM (p := p) 1) (sourceZ (p := p) 1)
      (gyH p 2 0 (Pi.single 0 1)) (tyH p 2 0 (Pi.single 0 1)) (3 / 2) =
      palindromicRatResidue p (gammaQ 0 0) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 2 (by norm_num) (by norm_num); simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 3 (by norm_num) (by norm_num); simpa using this
  have h4 : (4 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 4 (by norm_num) (by norm_num); simpa using this
  have h12 : (12 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 12 (by norm_num) (by norm_num); simpa using this
  have h24 : (24 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 24 (by norm_num) (by norm_num); simpa using this
  have m0 := sourceM_eq (p := p) hp2 hp3 1 0 (2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m1 := sourceM_eq (p := p) hp2 hp3 1 1 (0) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m2 := sourceM_eq (p := p) hp2 hp3 1 2 (-2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m3 := sourceM_eq (p := p) hp2 hp3 1 3 (2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m4 := sourceM_eq (p := p) hp2 hp3 1 4 (-1) 3 (by norm_num) (by norm_num) (by decide +kernel)
  have z0 := sourceZ_eq (p := p) hp2 hp3 1 0 (1) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have z1 := sourceZ_eq (p := p) hp2 hp3 1 1 (-1) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have z2 := sourceZ_eq (p := p) hp2 hp3 1 2 (1) 2 (by norm_num) (by norm_num) (by decide +kernel)
  have z3 := sourceZ_eq (p := p) hp2 hp3 1 3 (5) 12 (by norm_num) (by norm_num) (by decide +kernel)
  have g : palindromicRatResidue p (gammaQ 0 0) = ((-43 : ℤ) : ZMod p) / ((24 : ℕ) : ZMod p) := by
    have : gammaQ 0 0 = ((-43 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    rw [this]; exact palRes_div _ _ (unit_of_dvd_72 hp2 hp3 24 (by norm_num) (by norm_num))
  rw [g, gyH_e0, tyH_e0]
  unfold digitPhi
  simp [intrinsicCoeff, Finset.sum_range_succ, coeff_X_pow, coeff_X, coeff_one, coeff_sub, coeff_ofNat_mul, m0, m1, m2, m3, m4, z0, z1, z2, z3]
  field_simp
  ring

theorem gam_1_1 (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    digitPhi 4 3 (sourceM (p := p) 1) (sourceZ (p := p) 1)
      (gyH p 2 0 (Pi.single 1 1)) (tyH p 2 0 (Pi.single 1 1)) (3 / 2) =
      palindromicRatResidue p (gammaQ 0 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 2 (by norm_num) (by norm_num); simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 3 (by norm_num) (by norm_num); simpa using this
  have h4 : (4 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 4 (by norm_num) (by norm_num); simpa using this
  have h12 : (12 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 12 (by norm_num) (by norm_num); simpa using this
  have h24 : (24 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 24 (by norm_num) (by norm_num); simpa using this
  have m0 := sourceM_eq (p := p) hp2 hp3 1 0 (2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m1 := sourceM_eq (p := p) hp2 hp3 1 1 (0) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m2 := sourceM_eq (p := p) hp2 hp3 1 2 (-2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m3 := sourceM_eq (p := p) hp2 hp3 1 3 (2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m4 := sourceM_eq (p := p) hp2 hp3 1 4 (-1) 3 (by norm_num) (by norm_num) (by decide +kernel)
  have z0 := sourceZ_eq (p := p) hp2 hp3 1 0 (1) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have z1 := sourceZ_eq (p := p) hp2 hp3 1 1 (-1) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have z2 := sourceZ_eq (p := p) hp2 hp3 1 2 (1) 2 (by norm_num) (by norm_num) (by decide +kernel)
  have z3 := sourceZ_eq (p := p) hp2 hp3 1 3 (5) 12 (by norm_num) (by norm_num) (by decide +kernel)
  have g : palindromicRatResidue p (gammaQ 0 1) = ((49 : ℤ) : ZMod p) / ((24 : ℕ) : ZMod p) := by
    have : gammaQ 0 1 = ((49 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    rw [this]; exact palRes_div _ _ (unit_of_dvd_72 hp2 hp3 24 (by norm_num) (by norm_num))
  rw [g, gyH_e1', tyH_e1']
  unfold digitPhi
  simp [intrinsicCoeff, Finset.sum_range_succ, coeff_X_pow, coeff_X, coeff_one, coeff_sub, coeff_ofNat_mul, m0, m1, m2, m3, m4, z0, z1, z2, z3]
  field_simp
  ring

theorem gam_2_0 (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    digitPhi 4 3 (sourceM (p := p) 2) (sourceZ (p := p) 2)
      (gyH p 2 0 (Pi.single 0 1)) (tyH p 2 0 (Pi.single 0 1)) (3 / 2) =
      palindromicRatResidue p (gammaQ 1 0) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 2 (by norm_num) (by norm_num); simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 3 (by norm_num) (by norm_num); simpa using this
  have h4 : (4 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 4 (by norm_num) (by norm_num); simpa using this
  have h12 : (12 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 12 (by norm_num) (by norm_num); simpa using this
  have h24 : (24 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 24 (by norm_num) (by norm_num); simpa using this
  have m0 := sourceM_eq (p := p) hp2 hp3 2 0 (1) 2 (by norm_num) (by norm_num) (by decide +kernel)
  have m1 := sourceM_eq (p := p) hp2 hp3 2 1 (2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m2 := sourceM_eq (p := p) hp2 hp3 2 2 (-1) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m3 := sourceM_eq (p := p) hp2 hp3 2 3 (-2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m4 := sourceM_eq (p := p) hp2 hp3 2 4 (4) 3 (by norm_num) (by norm_num) (by decide +kernel)
  have z0 := sourceZ_eq (p := p) hp2 hp3 2 0 (3) 4 (by norm_num) (by norm_num) (by decide +kernel)
  have z1 := sourceZ_eq (p := p) hp2 hp3 2 1 (1) 2 (by norm_num) (by norm_num) (by decide +kernel)
  have z2 := sourceZ_eq (p := p) hp2 hp3 2 2 (-5) 4 (by norm_num) (by norm_num) (by decide +kernel)
  have z3 := sourceZ_eq (p := p) hp2 hp3 2 3 (1) 3 (by norm_num) (by norm_num) (by decide +kernel)
  have g : palindromicRatResidue p (gammaQ 1 0) = ((1 : ℤ) : ZMod p) / ((24 : ℕ) : ZMod p) := by
    have : gammaQ 1 0 = ((1 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    rw [this]; exact palRes_div _ _ (unit_of_dvd_72 hp2 hp3 24 (by norm_num) (by norm_num))
  rw [g, gyH_e0, tyH_e0]
  unfold digitPhi
  simp [intrinsicCoeff, Finset.sum_range_succ, coeff_X_pow, coeff_X, coeff_one, coeff_sub, coeff_ofNat_mul, m0, m1, m2, m3, m4, z0, z1, z2, z3]
  field_simp
  ring

theorem gam_2_1 (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    digitPhi 4 3 (sourceM (p := p) 2) (sourceZ (p := p) 2)
      (gyH p 2 0 (Pi.single 1 1)) (tyH p 2 0 (Pi.single 1 1)) (3 / 2) =
      palindromicRatResidue p (gammaQ 1 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 2 (by norm_num) (by norm_num); simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 3 (by norm_num) (by norm_num); simpa using this
  have h4 : (4 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 4 (by norm_num) (by norm_num); simpa using this
  have h12 : (12 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 12 (by norm_num) (by norm_num); simpa using this
  have h24 : (24 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 24 (by norm_num) (by norm_num); simpa using this
  have m0 := sourceM_eq (p := p) hp2 hp3 2 0 (1) 2 (by norm_num) (by norm_num) (by decide +kernel)
  have m1 := sourceM_eq (p := p) hp2 hp3 2 1 (2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m2 := sourceM_eq (p := p) hp2 hp3 2 2 (-1) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m3 := sourceM_eq (p := p) hp2 hp3 2 3 (-2) 1 (by norm_num) (by norm_num) (by decide +kernel)
  have m4 := sourceM_eq (p := p) hp2 hp3 2 4 (4) 3 (by norm_num) (by norm_num) (by decide +kernel)
  have z0 := sourceZ_eq (p := p) hp2 hp3 2 0 (3) 4 (by norm_num) (by norm_num) (by decide +kernel)
  have z1 := sourceZ_eq (p := p) hp2 hp3 2 1 (1) 2 (by norm_num) (by norm_num) (by decide +kernel)
  have z2 := sourceZ_eq (p := p) hp2 hp3 2 2 (-5) 4 (by norm_num) (by norm_num) (by decide +kernel)
  have z3 := sourceZ_eq (p := p) hp2 hp3 2 3 (1) 3 (by norm_num) (by norm_num) (by decide +kernel)
  have g : palindromicRatResidue p (gammaQ 1 1) = ((179 : ℤ) : ZMod p) / ((24 : ℕ) : ZMod p) := by
    have : gammaQ 1 1 = ((179 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    rw [this]; exact palRes_div _ _ (unit_of_dvd_72 hp2 hp3 24 (by norm_num) (by norm_num))
  rw [g, gyH_e1', tyH_e1']
  unfold digitPhi
  simp [intrinsicCoeff, Finset.sum_range_succ, coeff_X_pow, coeff_X, coeff_one, coeff_sub, coeff_ofNat_mul, m0, m1, m2, m3, m4, z0, z1, z2, z3]
  field_simp
  ring

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
