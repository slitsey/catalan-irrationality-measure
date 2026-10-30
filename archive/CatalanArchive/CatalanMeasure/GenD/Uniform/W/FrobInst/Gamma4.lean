module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.Gamma3
@[expose] public section
set_option Elab.async false

/-!
# `Γ` of Theorem M, derived

`gamMat p H` is the matrix of the derived digit-`3` covectors `psiLinH p 2 0 H (J+1) 3 (e_i)`
(`J, i ∈ {0,1}`).  `gamMat_eq_residue` : it equals `residueMat p gammaQ` for `p ∉ {2,3}`;
`gamMat_det` : its determinant, computed on the derived entries, is `-1291/96`.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W Matrix
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The derived `Γ` matrix: `psiLinH` at the digit-`3` covectors of `J = 1, 2` on `e_0, e_1`. -/
def gamMat (p H : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  fun J i => psiLinH p 2 0 H ((J : ℕ) + 1) 3 (Pi.single i 1)

/-- The derived `Γ` as a linear map on the `τ`-profile of the truncated atoms. -/
def gammaH (p H : ℕ) [Fact p.Prime] : (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p) :=
  LinearMap.pi fun J : Fin 2 => psiLinH p 2 0 H ((J : ℕ) + 1) 3

theorem gammaH_eq_mulVec (H : ℕ) : gammaH p H = (gamMat p H).mulVecLin := by
  refine LinearMap.ext fun y => funext fun J => ?_
  have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → ZMod p) + y 1 • (Pi.single 1 1 : Fin 2 → ZMod p) := by
    ext k; fin_cases k <;> simp
  simp only [gammaH, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, gamMat, LinearMap.pi_apply]
  conv_lhs => rw [hy]
  simp [map_add, map_smul, Fin.sum_univ_two, mul_comm]

theorem gamMat_eq_residue (hp2 : p ≠ 2) (hp3 : p ≠ 3) {H : ℕ} (hH : 4 ≤ H) :
    gamMat p H = residueMat p gammaQ := by
  ext J i
  unfold gamMat residueMat
  rw [psiLinH_cutoff H hH]
  fin_cases J <;> fin_cases i
  · exact gam_1_0 hp2 hp3
  · exact gam_1_1 hp2 hp3
  · exact gam_2_0 hp2 hp3
  · exact gam_2_1 hp2 hp3

theorem gammaH_eq_residue (hp2 : p ≠ 2) (hp3 : p ≠ 3) {H : ℕ} (hH : 4 ≤ H) :
    gammaH p H = (residueMat p gammaQ).mulVecLin := by
  rw [gammaH_eq_mulVec, gamMat_eq_residue hp2 hp3 hH]

/-- Entries of `gammaQ` as residues of `a / 24`. -/
theorem res_gammaQ (hp2 : p ≠ 2) (hp3 : p ≠ 3) (i j : Fin 2) :
    palindromicRatResidue p (gammaQ i j) =
      ((if i = 0 then (if j = 0 then -43 else 49) else (if j = 0 then 1 else 179) : ℤ) : ZMod p) /
        ((24 : ℕ) : ZMod p) := by
  have h24 := unit_of_dvd_72 (p := p) hp2 hp3 24 (by norm_num) (by norm_num)
  fin_cases i <;> fin_cases j
  · have : gammaQ 0 0 = ((-43 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    simpa [this] using palRes_div (p := p) (-43) 24 h24
  · have : gammaQ 0 1 = ((49 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    simpa [this] using palRes_div (p := p) 49 24 h24
  · have : gammaQ 1 0 = ((1 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    simpa [this] using palRes_div (p := p) 1 24 h24
  · have : gammaQ 1 1 = ((179 : ℤ) : ℚ) / ((24 : ℕ) : ℚ) := by simp [gammaQ]
    simpa [this] using palRes_div (p := p) 179 24 h24

/-- **The determinant, computed on the derived entries.** -/
theorem gamMat_det (hp2 : p ≠ 2) (hp3 : p ≠ 3) {H : ℕ} (hH : 4 ≤ H) :
    (gamMat p H).det = (-1291 : ZMod p) / 96 := by
  have h24 := unit_of_dvd_72 (p := p) hp2 hp3 24 (by norm_num) (by norm_num)
  have h96 := unit_of_dvd_72 (p := p) hp2 hp3 1 (by norm_num) (by norm_num)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 2 (by norm_num) (by norm_num); simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := unit_of_dvd_72 (p := p) hp2 hp3 3 (by norm_num) (by norm_num); simpa using this
  rw [gamMat_eq_residue hp2 hp3 hH, Matrix.det_fin_two]
  simp only [residueMat, res_gammaQ hp2 hp3]
  have h24' : (24 : ZMod p) = 2 ^ 3 * 3 := by norm_num
  have h96' : (96 : ZMod p) = 2 ^ 5 * 3 := by norm_num
  simp only [Nat.cast_ofNat] at h24 ⊢
  rw [h96']
  rw [h24'] at h24 ⊢
  field_simp
  push_cast
  ring

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
