module

public import CatalanCore.Uniform.Content.Smith.Weights

@[expose] public section

/-!
# Theorem UF from the compressed loads (derived frame)

H1's compression (`LeadingData.nextRed_eq_loadMat`) identifies `M_next mod p` with the load matrix
`ω(x_i, y_j)/(σ_j - ρ_i)` of the kernel loads.  If the loads of the `J`-supported kernels are
`(m, m·h(z))` with `h(z) = Σ_c v(c)/(c - z)` (the derived frame: poles `c` with weights `v(c)`), the load
matrix is the weighted Cauchy matrix `m m' Σ_c v(c)/((c-z)(c-y))` (`loewner_of_loads`), whose rank is at
most the number of retained poles.  `LeadingData.gle_det_uf_loads` is the resulting price, with
no further hypothesis on the weights.
-/

open Finset Matrix Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}

open scoped Classical in
/-- **Theorem UF (loads form).** -/
theorem _root_.CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_uf_loads
    (D : LeadingData p Φ) (α β Lr Lc : ι → ZMod p)
    (hCr : ∀ i j, phiP p (D.Cr i j) = rfC p ((Lc j - Lr i) / (β j - α i)))
    (ρ σ : D.s → ZMod p)
    (hu : ∀ (i : D.s) k, redQ p (D.L i k) ≠ 0 → α k = ρ i)
    (hv : ∀ (j : D.s) l, redQ p (D.P l j) ≠ 0 → β l = σ j)
    (R0 : ℕ) (hR : R0 + D.s.card = Fintype.card ι)
    (Ret : Finset (ZMod p)) (w : ZMod p → ZMod p) (mR mC : D.s → ZMod p)
    (hrow : ∀ i, D.rowLoad Lr i = (mR i, mR i * ∑ c ∈ Ret, w c * (c - ρ i)⁻¹))
    (hcol : ∀ j, D.colLoad Lc j = (mC j, mC j * ∑ c ∈ Ret, w c * (c - σ j)⁻¹))
    (hρσ : ∀ i j, ρ i ≠ σ j)
    (hz : ∀ i, ∀ c ∈ Ret, w c ≠ 0 → c ≠ ρ i) (hy : ∀ j, ∀ c ∈ Ret, w c ≠ 0 → c ≠ σ j) :
    GLE p (Fintype.card ι + R0 - (D.s.card - Ret.card)) Φ.det := by
  refine D.gle_det_derived R0 hR Ret w mR mC ρ σ fun i j => ?_
  have hmat := D.nextRed_eq_loadMat α β Lr Lc hCr ρ σ hu hv
  rw [hmat]
  simp only [Matrix.map_apply, loadMat, Matrix.of_apply, hrow i, hcol j, omegaL_apply]
  congr 1
  exact loewner_of_loads Ret w (hρσ i j) (hz i) (hy j)

end CatalanCore.Uniform.Content.Smith
