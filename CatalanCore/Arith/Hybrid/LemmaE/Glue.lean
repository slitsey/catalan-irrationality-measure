module

public import CatalanCore.Arith.Hybrid.LemmaE.TCore
public import CatalanCore.Arith.Hybrid.Deficit

@[expose] public section

/-!
# Gluing the T-route criterion to WP-H5's `LemmaEHyp`

`Frame.fullPoly r m` is `det` of `fullMat` (indexed by `Fin r ⊕ Fin m`), whose `(inl, inl)` block
is `A = R_CC + X` and whose remaining blocks are the Loewner blocks `B, C, D`.  `TData` packages
the output of the T-route at one prime (primitive `g`, `N = g A⁻¹`, scaling exponent `s`, bound
`b` for the entries of `g T`), and `lemmaEHyp_of_tdata` turns, for every clean prime, such data
plus the tropical lower bound `tropExp ≥ m + m b + s` into `LemmaEHyp`.
-/

open Polynomial Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Arith.Hybrid.LemmaE

/-- The matrix whose determinant is `Frame.fullPoly`. -/
noncomputable def fullMat (Fr : Frame) (r m : ℕ) : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) ℚ[X] :=
  Matrix.of fun a b : Fin r ⊕ Fin m =>
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' then (X : ℚ[X]) else 0
      | _, _ => 0) + C (Fr.Mn (Frame.hybRow r m a) (Frame.hybCol r m b))

lemma fullPoly_eq (Fr : Frame) (r m : ℕ) : Fr.fullPoly r m = (fullMat Fr r m).det := rfl

/-- The output of the T-route at a prime `p`. -/
structure TData (p : ℕ) [Fact p.Prime] (Fr : Frame) (r m : ℕ) where
  g : ℚ[X]
  N : Matrix (Fin r) (Fin r) ℚ[X]
  s : ℕ
  b : ℕ
  hg : gn p g = 1
  hAN : (fullMat Fr r m).toBlocks₁₁ * N = g • (1 : Matrix (Fin r) (Fin r) ℚ[X])
  hdet : C ((p : ℚ) ^ s) * (fullMat Fr r m).toBlocks₁₁.det = g
  hT : ∀ z y, GLE p b (Tscaled g (fullMat Fr r m).toBlocks₁₁ (fullMat Fr r m).toBlocks₁₂
      (fullMat Fr r m).toBlocks₂₁ (fullMat Fr r m).toBlocks₂₂ N z y)

theorem TData.gle {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m : ℕ} (T : TData p Fr r m) :
    GLE p (m * T.b + T.s) (Fr.fullPoly r m) := by
  have := tcore p (fullMat Fr r m) T.g T.hg T.N T.hAN T.s T.hdet T.b T.hT
  simpa [fullPoly_eq] using this

/-- **Lemma E from T-route data.**  If every clean prime carries `TData` whose bound is
compatible with the tropical exponent, then `LemmaEHyp` holds. -/
theorem lemmaEHyp_of_tdata {Fr : Frame} (I : HybInst Fr) (r m : ℕ) {clean : ℕ → Prop}
    (h : ∀ p : ℕ, p.Prime → p < Bnd I r m → clean p →
      m ≤ tropExp I r m p ∧ ∃ (_ : Fact p.Prime) (T : TData p Fr r m),
        m + (m * T.b + T.s) ≤ tropExp I r m p) :
    LemmaEHyp I r m clean := by
  intro p hp hb hc
  obtain ⟨hm, hF, T, hle⟩ := h p hp hb hc
  refine ⟨hm, fun [Fact p.Prime] => ?_⟩
  exact (T.gle).mono (by omega)

end CatalanCore.Arith.Hybrid.LemmaE
