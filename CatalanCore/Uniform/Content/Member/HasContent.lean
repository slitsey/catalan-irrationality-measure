module

public import CatalanCore.Uniform.Content.Member.Combine

@[expose] public section

/-!
# `HasContent` for the BlockGeom common-deletion family from debit layers (lane H5, output)

The per-prime minimum of the proved layers (tropical, rank, M3D, LPD, Smith; each a `DebitLayer`
valid on a window of `(r, p)`) is covered, class by class, by the exact piecewise-linear
templates.  The covering hypotheses are stated for the EFFECTIVE price
`base r p + debit · depth` of the layers, i.e. the full-member price plus the worst debit.

Output: `HasContent (G.family Fr depth) Λ` with
`Λ = (1 / mass)² · (Σ_{c unit mod M} (α0_c t1_c + Σ ∫ pieces_c)) / φ(M)`,
generic in the frame `Fr`, the block geometry `G` and the layers.
-/

open Polynomial Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Uniform

namespace CatalanCore.Uniform.Content.Member

variable {M : ℕ} [NeZero M]

/-- **Main theorem (lane H5).**  `HasContent` for the BlockGeom common-deletion family from a
finite list of debit layers (layer `0` is global) and the class templates covering their
per-prime minimum. -/
theorem hasContent_of_debitLayers (G : BlockGeom) (Fr : Frame) (depth : ℕ) {k : ℕ}
    (L : Fin (k + 1) → DebitLayer G Fr depth) (h0 : ∀ r p, (L 0).valid r p)
    (tmpl : ZMod M → Template) (K : ℝ) (hK : 0 ≤ K)
    (tail : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p → ∃ j, (L j).valid r p ∧ (L j).eff r p = 0)
    (pre : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ (tmpl c).α0 * r)
    (cov : ∀ r : ℕ, ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊P.s * r⌋₊ < p → p ≤ ⌊P.t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ P.α * r + P.β * p + P.C)
    (exc : ∀ r p : ℕ, p.Prime → p ∣ M →
      ∃ j, (L j).valid r p ∧ (((L j).eff r p : ℕ) : ℝ) ≤ K * r) :
    HasContent (G.family Fr depth)
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M tmpl) := by
  classical
  let w : Fin (k + 1) → NodeFamily.Index G.geometry → ℕ → ℕ := fun j i p =>
    if (L j).valid i.1 p then (L j).base i.1 p + (L j).debit * delCount G i
    else (L 0).base i.1 p + (L 0).debit * delCount G i
  have hw_le : ∀ j (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i → ∀ p,
      (L j).valid i.1 p → w j i p ≤ (L j).eff i.1 p := by
    intro j i hi p hv
    have hd := delCount_le G Fr depth i hi
    simp only [w, if_pos hv, DebitLayer.eff]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hd) _
  have hw_le_real : ∀ j (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i → ∀ p,
      (L j).valid i.1 p → (w j i p : ℝ) ≤ (((L j).eff i.1 p : ℕ) : ℝ) := by
    intro j i hi p hv
    exact_mod_cast hw_le j i hi p hv
  let CC : ContentCover (G.family Fr depth) G.scale M :=
    ContentCover.ofLayers (Fam := G.family Fr depth) (sc := G.scale) tmpl w K hK
      (by
        intro j i hi p hp
        by_cases hv : (L j).valid i.1 p
        · simp only [w, if_pos hv]
          exact (L j).gle i hi p hv
        · simp only [w, if_neg hv]
          exact (L 0).gle i hi p (h0 _ _))
      (by
        intro i hi c hc p hp hpc hlt
        obtain ⟨j, hv, he⟩ := tail i.1 c hc p hp hpc hlt
        exact ⟨j, Nat.le_zero.1 (he ▸ hw_le j i hi p hv)⟩)
      (by
        intro i hi c hc p h1 hp hpc
        obtain ⟨j, hv, he⟩ := pre i.1 c hc p h1 hp hpc
        exact ⟨j, (hw_le_real j i hi p hv).trans he⟩)
      (by
        intro i hi c hc P hP p h1 h2 hp hpc
        obtain ⟨j, hv, he⟩ := cov i.1 c hc P hP p h1 h2 hp hpc
        exact ⟨j, (hw_le_real j i hi p hv).trans he⟩)
      (by
        intro i hi p hp hpd
        obtain ⟨j, hv, he⟩ := exc i.1 p hp hpd
        exact ⟨j, (hw_le_real j i hi p hv).trans he⟩)
  exact hasContent_blockGeom G Fr depth CC

end CatalanCore.Uniform.Content.Member
