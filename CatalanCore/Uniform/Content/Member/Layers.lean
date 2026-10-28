module

public import CatalanCore.Uniform.Content.Member.Assemble
public import CatalanCore.Uniform.Content.ClearMin

@[expose] public section

/-!
# Per-prime minimum of the proved layers (lane H5)

`layerMin w` is the minimum of finitely many layer prices.  If every layer is a valid
coefficientwise `p`-integrality price of the member polynomial, so is the minimum
(`gle_layerMin`, the finite form of `ClearMin.gle_min`; no valuation law is used).  The cover
hypotheses of `ContentCover` for the minimum price are pointwise: at each prime some layer lies
under the class template (`ContentCover.ofLayers`).  This is exactly "the pointwise minimum of
the proved layers is bounded by the lower envelope of the exact piecewise-linear pieces".
-/

open CatalanCore CatalanCore.Arith.Hybrid Filter Finset

namespace CatalanCore.Uniform.Content.Member

/-- The minimum of `k + 1` layer prices. -/
def layerMin {k : ℕ} (w : Fin (k + 1) → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (k + 1))).inf' ⟨0, Finset.mem_univ _⟩ w

lemma layerMin_le {k : ℕ} (w : Fin (k + 1) → ℕ) (j : Fin (k + 1)) : layerMin w ≤ w j :=
  Finset.inf'_le _ (Finset.mem_univ j)

lemma exists_layerMin_eq {k : ℕ} (w : Fin (k + 1) → ℕ) : ∃ j, layerMin w = w j := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin (k + 1))))
    ⟨0, Finset.mem_univ _⟩ w
  exact ⟨j, hj⟩

/-- Finite pointwise minimum of valid layers is a valid layer. -/
theorem gle_layerMin {p : ℕ} [Fact p.Prime] {k : ℕ} {w : Fin (k + 1) → ℕ} {f : Polynomial ℚ}
    (h : ∀ j, GLE p (w j) f) : GLE p (layerMin w) f := by
  obtain ⟨j, hj⟩ := exists_layerMin_eq w
  rw [hj]; exact h j

/-- The minimum is below every layer, also after casting to the reals. -/
lemma cast_layerMin_le {k : ℕ} (w : Fin (k + 1) → ℕ) (j : Fin (k + 1)) :
    (layerMin w : ℝ) ≤ w j := by exact_mod_cast layerMin_le w j

/-- Pointwise: the minimum is below `B` as soon as one layer is. -/
lemma layerMin_le_of_exists {k : ℕ} {w : Fin (k + 1) → ℕ} {B : ℝ}
    (h : ∃ j, (w j : ℝ) ≤ B) : (layerMin w : ℝ) ≤ B := by
  obtain ⟨j, hj⟩ := h
  exact (cast_layerMin_le w j).trans hj

lemma layerMin_eq_zero_of_exists {k : ℕ} {w : Fin (k + 1) → ℕ} (h : ∃ j, w j = 0) :
    layerMin w = 0 := by
  obtain ⟨j, hj⟩ := h
  have := layerMin_le w j
  omega

variable {Fam : PolyFamily} {sc : Fam.ι → ℕ} {M : ℕ} [NeZero M]

/-- **The cover from layers.**  Layers `w j i p` (`j ≤ k`) are valid per-prime prices of the
members; the price is their per-prime minimum, and the cover hypotheses ask only that at each
prime some layer lies under the class template. -/
noncomputable def ContentCover.ofLayers {k : ℕ} (tmpl : ZMod M → Template)
    (w : Fin (k + 1) → Fam.ι → ℕ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (gle : ∀ j i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], GLE p (w j i p) (Fam.Q i))
    (tail : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * sc i⌋₊ < p → ∃ j, w j i p = 0)
    (pre : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (w j i p : ℝ) ≤ (tmpl c).α0 * sc i)
    (cov : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l, ∀ p : ℕ,
      ⌊P.s * sc i⌋₊ < p → p ≤ ⌊P.t * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
        ∃ j, (w j i p : ℝ) ≤ P.α * sc i + P.β * p + P.C)
    (exc : ∀ i, Fam.Adm i → ∀ p : ℕ, p.Prime → p ∣ M → ∃ j, (w j i p : ℝ) ≤ K * sc i) :
    ContentCover Fam sc M where
  tmpl := tmpl
  price := fun i p => layerMin (fun j => w j i p)
  K := K
  hK := hK
  gle := fun i hi p _ => gle_layerMin (fun j => gle j i hi p)
  tail := fun i hi c hc p hp hpc hlt => layerMin_eq_zero_of_exists (tail i hi c hc p hp hpc hlt)
  pre := fun i hi c hc p h1 hp hpc => layerMin_le_of_exists (pre i hi c hc p h1 hp hpc)
  cov := fun i hi c hc P hP p h1 h2 hp hpc =>
    layerMin_le_of_exists (cov i hi c hc P hP p h1 h2 hp hpc)
  exc := fun i hi p hp hpd => layerMin_le_of_exists (exc i hi p hp hpd)

end CatalanCore.Uniform.Content.Member
