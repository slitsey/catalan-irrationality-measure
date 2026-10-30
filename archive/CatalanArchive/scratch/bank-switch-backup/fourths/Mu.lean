import CatalanCore.Uniform.Bank.LambdaContent.AutoData
import CatalanCore.Uniform.Bank.Lambda.Final
set_option Elab.async false

/-! # The λ μ target with the finite UF constant (lane C1L)

`lambda_mu_le : cL / (DL - Λ_fin) ≤ 315113/10000`, `Λ_fin = bankData.Λ` (`AutoData`, `n = 100`), with the decay
constants `DL`, `cL` of `Bank/Lambda/Final` (equal to `D_lower`, `c_upper` of
`hybrid-exact-receipts-2026-10-27/exact-LAMB.json`). -/

namespace CatalanCore.Uniform.Bank.LambdaContent.Auto
open CatalanCore.Uniform.Bank.Lambda

/-- **The λ μ target**: `cL / (DL - Λ_fin) ≤ 315113/10000` with the finite UF constant `Λ_fin = bankData.Λ`. -/
theorem lambda_mu_le : (cL : ℝ) / ((DL : ℝ) - (bankData.Λ : ℝ)) ≤ ((315113 / 10000 : ℚ) : ℝ) := by
  have h1 : bankData.Λ < DL := by rw [bankData_Λ]; unfold DL; norm_num
  have h2 : cL ≤ 315113 / 10000 * (DL - bankData.Λ) := by rw [bankData_Λ]; unfold cL DL; norm_num
  have hpos : (0 : ℝ) < (DL : ℝ) - (bankData.Λ : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 h1; linarith
  rw [div_le_iff₀ hpos]
  have h3 := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h3 ⊢
  linarith

#print axioms lambda_mu_le

end CatalanCore.Uniform.Bank.LambdaContent.Auto
