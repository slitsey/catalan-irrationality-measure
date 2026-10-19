module

public import CatalanCore.Decay.Rect.Energy2

@[expose] public section

/-!
# `g_h = g_sq + h` (WP-H2-core)

For the cheap hybrid certificate `(1+α) σ_h = σ₃₀₀ + λ` (a concatenation of the square measure and a
correction measure of mass `α`), the hybrid function decomposes as the square one plus a
correction:  `g_h = (U^{σ₃₀₀} - U^τ + field) + (U^λ - U^{ex}_{2α})`.  So the legacy fact
"`g_sq ≥ MPRAY` on the ray cells" is reused unchanged and only `h = U^λ - U^ex` needs new cells.
-/

open Finset
open CatalanLambda.Decay (Usig Utau)

namespace CatalanCore.Decay

theorem Usig_smul {K : ℕ} (ρ a : ℝ) (c : Fin K → ℂ) (wt : Fin K → ℝ) (s : ℂ) :
    Usig ρ c (fun k => a * wt k) s = a * Usig ρ c wt s := by
  unfold Usig
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem Usig_append {K1 K2 : ℕ} (ρ : ℝ) (c1 : Fin K1 → ℂ) (w1 : Fin K1 → ℝ) (c2 : Fin K2 → ℂ)
    (w2 : Fin K2 → ℝ) (s : ℂ) :
    Usig ρ (Fin.append c1 c2) (Fin.append w1 w2) s = Usig ρ c1 w1 s + Usig ρ c2 w2 s := by
  unfold Usig
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- **Decomposition.**  If `c = c₁ ⧺ c₂` and `wt = (w₁ ⧺ w₂)/(1+α)`, then
`(1+α) U^σ_h - U^ν + (1-ε)π|Im| = (U^{σ₁} - U^τ + (1-ε)π|Im|) + (U^{σ₂} - U^{ex}_{2α})`,
where `σ₁ = (c₁, w₁)` is the square measure and `σ₂ = (c₂, w₂)` the correction. -/
theorem hyb_g_decomp {K1 K2 : ℕ} (ρ ε α : ℝ) (hα : 1 + α ≠ 0) (c1 : Fin K1 → ℂ) (w1 : Fin K1 → ℝ)
    (c2 : Fin K2 → ℂ) (w2 : Fin K2 → ℝ) (s : ℂ) :
    (1 + α) * Usig ρ (Fin.append c1 c2) (fun k => (Fin.append w1 w2 k) / (1 + α)) s
        - Unu α s + (1 - ε) * Real.pi * |s.im|
      = (Usig ρ c1 w1 s - Utau s + (1 - ε) * Real.pi * |s.im|)
        + (Usig ρ c2 w2 s - Uex (2 * α) s) := by
  have h1 : (fun k => (Fin.append w1 w2 k) / (1 + α))
      = fun k => (1 / (1 + α)) * (Fin.append w1 w2 k) := by
    funext k; ring
  rw [h1, Usig_smul, Usig_append]
  unfold Unu
  field_simp
  ring

/-! ### Negative control: the square case is `α = 0` -/

theorem Uex_zero (σ : ℂ) : Uex 0 σ = 0 := by simp [Uex]

theorem Unu_zero (σ : ℂ) : Unu 0 σ = Utau σ := by simp [Unu, Uex_zero]

/-- The bridge `CertCore.toG` satisfies the hybrid soundness identity at `α = 0`
(so the hybrid interface specialises to the square one). -/
theorem toG_hg_square {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : Cert.CertCore K ρ ε c m) (s : ℂ) :
    F.toG.g s = (1 + (0 : ℝ)) * Usig ρ c m s - Unu (0 : ℝ) s + (1 - ε) * Real.pi * |s.im| := by
  simp [Cert.CertCore.toG, CatalanLambda.Decay.gfun, Unu_zero]

end CatalanCore.Decay
