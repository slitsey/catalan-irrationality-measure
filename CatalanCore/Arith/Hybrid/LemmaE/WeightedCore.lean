module

public import CatalanCore.Arith.Hybrid.LemmaE.BlockScale
public import CatalanCore.Arith.Hybrid.BorderCore

@[expose] public section

/-! # Weighted primitive Schur bounds

The fraction-field determinant identity lives only in `TCore`. Here the
existing tropical determinant and bordering lemmas supply its bound.
-/
open Polynomial Matrix Finset CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid.LemmaE
variable (p : ℕ) [Fact p.Prime]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The primitive Schur core with arbitrary entry weights. -/
theorem tcore_weighted (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (g : ℚ[X]) (hg : gn p g = 1) (N : Matrix ι ι ℚ[X])
    (hAN : Full.toBlocks₁₁ * N = g • (1 : Matrix ι ι ℚ[X]))
    (s : ℕ) (hdet : C ((p : ℚ) ^ s) * Full.toBlocks₁₁.det = g)
    (W : κ → κ → ℕ)
    (hT : ∀ z y, GLE p (W z y) (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂
      Full.toBlocks₂₁ Full.toBlocks₂₂ N z y)) :
    GLE p (tropVal W + s) Full.det :=
  tcore_of_det_gle p Full g hg N hAN s hdet (tropVal W) (det_gle _ W hT)

/-- An explicit majorant avoids needing an assignment-optimality theorem. -/
theorem tcore_weighted_le (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (g : ℚ[X]) (hg : gn p g = 1) (N : Matrix ι ι ℚ[X])
    (hAN : Full.toBlocks₁₁ * N = g • (1 : Matrix ι ι ℚ[X]))
    (s : ℕ) (hdet : C ((p : ℚ) ^ s) * Full.toBlocks₁₁.det = g)
    (W : κ → κ → ℕ) (e : ℕ) (he : tropVal W ≤ e)
    (hT : ∀ z y, GLE p (W z y) (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂
      Full.toBlocks₂₁ Full.toBlocks₂₂ N z y)) :
    GLE p (e + s) Full.det :=
  (tcore_weighted p Full g hg N hAN s hdet W hT).mono (Nat.add_le_add_right he s)

/-- Arbitrary old block scaling feeds the same weighted core. -/
theorem tcore_scaled_weighted (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (d : ι → ℕ)
    (hg : gn p (Atil p d Full.toBlocks₁₁).det = 1) (W : κ → κ → ℕ)
    (hT : ∀ z y, GLE p (W z y) (Tscaled (Atil p d Full.toBlocks₁₁).det
      Full.toBlocks₁₁ Full.toBlocks₁₂ Full.toBlocks₂₁ Full.toBlocks₂₂
      (Nmat p d Full.toBlocks₁₁) z y)) :
    GLE p (tropVal W + 2 * ∑ i, d i) Full.det := by
  exact tcore_weighted p Full _ hg _ (AN_eq p d _) _ (det_Atil p d _).symm W hT

/-- One new Schur row and column cost at most `2w`, preserving the inner weights. -/
theorem tcore_weighted_border (Full : Matrix (ι ⊕ Option κ) (ι ⊕ Option κ) ℚ[X])
    (g : ℚ[X]) (hg : gn p g = 1) (N : Matrix ι ι ℚ[X])
    (hAN : Full.toBlocks₁₁ * N = g • (1 : Matrix ι ι ℚ[X]))
    (s : ℕ) (hdet : C ((p : ℚ) ^ s) * Full.toBlocks₁₁.det = g)
    (W : κ → κ → ℕ) (w : ℕ)
    (hT : ∀ z y, GLE p (W z y) (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂
      Full.toBlocks₂₁ Full.toBlocks₂₂ N (some z) (some y)))
    (hr : ∀ z, GLE p w (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂
      Full.toBlocks₂₁ Full.toBlocks₂₂ N (some z) none))
    (hc : ∀ y, GLE p w (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂
      Full.toBlocks₂₁ Full.toBlocks₂₂ N none (some y)))
    (hd : GLE p (w+w) (Tscaled g Full.toBlocks₁₁ Full.toBlocks₁₂
      Full.toBlocks₂₁ Full.toBlocks₂₂ N none none)) :
    GLE p (tropVal W + (w+w) + s) Full.det :=
  tcore_of_det_gle p Full g hg N hAN s hdet _
    (det_gle_border p _ W hT w hr hc hd)

end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.tcore_weighted
#print axioms CatalanCore.Arith.Hybrid.LemmaE.tcore_weighted_border
