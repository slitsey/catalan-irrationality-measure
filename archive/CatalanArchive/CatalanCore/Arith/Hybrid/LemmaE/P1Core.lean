module

public import CatalanArchive.CatalanCore.Arith.Hybrid.LemmaE.Vanish

@[expose] public section

/-!
# The scalar-Schur T-route theorem (class `p ≡ 1`, C7, and the core of GK)

`p1_core` bundles `tcore_scaled`, `T_decomp`, `bilin_vanish` and `LNL_gle`.  All hypotheses are
*congruence statements about explicit rational entries* (the instance supplies them):

* `Ã = D A D` is integral and congruent to a model `M` of primitive determinant;
* the second difference `Δ² = D - Sr B - C Sc + Sr A Sc` has entries in `p^{-b} ℤ_(p)`;
* the scaled defect rows/columns `μ_z = p^a ℓ_z D`, `ν_y = p^a D ℓ'_y` are integral and congruent to
  multiples of the unit vectors `e_{cz z}`, `e_{cy y}`;
* the model's adjugate vanishes at `(cz z, cy y)` (for a model with scalar Schur complement this is
  `adj(M)_{UU} = det(M) s₀⁻¹ I`).

Conclusion: `v_p(det Full) ≥ -(2 ∑ d + m · max(b, 2a-1))`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

theorem p1_core (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (d : ι → ℕ) (M : Matrix ι ι ℚ[X])
    (cz cy : κ → ι) (a b : ℕ) (β β' : κ → ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p d Full.toBlocks₁₁ i j)) (hM : ∀ i j, Int1 p (M i j))
    (hc : ∀ i j, Cng p (Atil p d Full.toBlocks₁₁ i j) (M i j)) (hprim : gn p M.det = 1)
    (hΔ : ∀ z y, GLE p b ((Full.toBlocks₂₂ - (selR cz : Matrix κ ι ℚ[X]) * Full.toBlocks₁₂
        - Full.toBlocks₂₁ * (selC cy : Matrix ι κ ℚ[X]) +
        (selR cz : Matrix κ ι ℚ[X]) * Full.toBlocks₁₁ * (selC cy : Matrix ι κ ℚ[X])) z y))
    (hμ : ∀ z c, Int1 p (C ((p : ℚ) ^ a) * defL Full.toBlocks₁₁ Full.toBlocks₂₁ cz z c *
        C ((p : ℚ) ^ d c)))
    (hν : ∀ y c, Int1 p (C ((p : ℚ) ^ a) * C ((p : ℚ) ^ d c) *
        defR Full.toBlocks₁₁ Full.toBlocks₁₂ cy c y))
    (hβ : ∀ z, Int1 p (β z)) (hβ' : ∀ y, Int1 p (β' y))
    (cμ : ∀ z c, Cng p (C ((p : ℚ) ^ a) * defL Full.toBlocks₁₁ Full.toBlocks₂₁ cz z c *
        C ((p : ℚ) ^ d c)) (if c = cz z then β z else 0))
    (cν : ∀ y c, Cng p (C ((p : ℚ) ^ a) * C ((p : ℚ) ^ d c) *
        defR Full.toBlocks₁₁ Full.toBlocks₁₂ cy c y) (if c = cy y then β' y else 0))
    (hadjM : ∀ z y, Cng p (M.adjugate (cz z) (cy y)) 0) :
    GLE p (Fintype.card κ * max b (2 * a - 1) + 2 * ∑ i, d i) Full.det := by
  set A := Full.toBlocks₁₁
  set g := (Atil p d A).det with hg
  have hgI : gn p g ≤ 1 := det_int1 hI
  refine tcore_scaled p Full d M hI hM hc hprim (max b (2 * a - 1)) ?_
  intro z y
  have hdec := T_decomp A (Nmat p d A) Full.toBlocks₁₂ Full.toBlocks₂₁ Full.toBlocks₂₂ g
    (AN_eq p d A) (NA_eq p d A) cz cy
  have hT : Tscaled g A Full.toBlocks₁₂ Full.toBlocks₂₁ Full.toBlocks₂₂ (Nmat p d A) =
      g • Full.toBlocks₂₂ - Full.toBlocks₂₁ * Nmat p d A * Full.toBlocks₁₂ := rfl
  rw [hT, hdec]
  rw [Matrix.sub_apply]
  -- first term
  have h1 : GLE p (max b (2 * a - 1)) ((g • (Full.toBlocks₂₂ - (selR cz : Matrix κ ι ℚ[X]) *
      Full.toBlocks₁₂ - Full.toBlocks₂₁ * (selC cy : Matrix ι κ ℚ[X]) +
      (selR cz : Matrix κ ι ℚ[X]) * A * (selC cy : Matrix ι κ ℚ[X]))) z y) := by
    rw [Matrix.smul_apply, smul_eq_mul, gle_iff_gn, gn_mul]
    have := (gle_iff_gn p _ _).mp ((hΔ z y).mono (le_max_left b (2 * a - 1)))
    calc gn p g * gn p _ ≤ 1 * (p : ℝ) ^ (max b (2 * a - 1)) :=
          mul_le_mul hgI this (gn_nonneg p _) zero_le_one
      _ = _ := one_mul _
  -- second term
  have hadj : ∀ c c', Int1 p ((Atil p d A).adjugate c c') := adj_int1 hI
  have hvan : Cng p (∑ c, ∑ c', (C ((p : ℚ) ^ a) * defL A Full.toBlocks₂₁ cz z c *
        C ((p : ℚ) ^ d c)) * (Atil p d A).adjugate c c' *
        (C ((p : ℚ) ^ a) * C ((p : ℚ) ^ d c') * defR A Full.toBlocks₁₂ cy c' y)) 0 := by
    refine bilin_vanish _ _ _ (cz z) (cy y) (β z) (β' y) (hμ z) (fun c => hν y c) hadj (hβ z)
      (hβ' y) (cμ z) (fun c => cν y c) ?_
    exact (adj_cng hI hM hc _ _).trans (hadjM z y)
  have h2 := (LNL_gle d A (defL A Full.toBlocks₂₁ cz) (defR A Full.toBlocks₁₂ cy) a z y hvan).mono
    (le_max_right b (2 * a - 1))
  rw [gle_iff_gn] at h1 h2 ⊢
  calc gn p _ ≤ max (gn p _) (gn p _) := gn_sub_le _ _
    _ ≤ _ := max_le h1 h2

end CatalanCore.Arith.Hybrid.LemmaE
