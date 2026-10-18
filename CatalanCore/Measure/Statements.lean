module

public import CatalanCore.Frame.Spec
public import Mathlib.NumberTheory.Real.Irrational

/-!
# WP6 STATEMENTS ONLY (early stub; `sorry` allowed in THIS file only)

Statements of the generic measure deduction.  WP7/WP12 may import this module and instantiate.
When the proofs land, this file is replaced by a thin re-export of `Sep`, `Core`,
`Irrational`, `Exponent`, with the SAME declaration names and signatures.

Hypotheses (see `FX-lean-wp/WP6/notes.md`):
* `HasContent Fam Λ`, `HasDecay Fam D c`, `HasNV Fam R g₁ g₂` : the Spec interfaces.
* `PrimeRule.HasWindow R` : the node-removal prime window, `exists_prime_window` of design 2.4:
  for `0 < a`, `a + R.s < b` and all large `q` there is a prime `l ≡ R.r (mod R.m)` in
  `(a log q, b log q]` with `¬ R.Bad l q`.  (Proved elsewhere by PNT in APs; hypothesis here.)
-/

@[expose] public section

namespace CatalanCore

/-- The prime window of design 2.4 / BN: hypothesis of the measure theorem. -/
def PrimeRule.HasWindow (R : PrimeRule) : Prop :=
  ∀ a b : ℝ, 0 < a → a + (R.s : ℝ) < b →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ l : ℕ, l.Prime ∧ (l : ZMod R.m) = R.r ∧
      a * Real.log q < l ∧ (l : ℝ) ≤ b * Real.log q ∧ ¬ R.Bad l q

namespace Measure

/-- Separation core: nonvanishing `Q_n(p/q)` very near the constant forces `θ deg n ≤ log q`. -/
theorem sep_core (Fam : PolyFamily) {Λ D c : ℝ} (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < D - Λ) :
    ∃ N₀ : ℕ, ∀ n, Fam.Adm n → N₀ ≤ Fam.deg n → ∀ p q : ℤ, 0 < q →
      Fam.evalQ n (p / q) ≠ 0 → |Fam.const - (p : ℝ) / q| ≤ Real.exp (-c * Fam.deg n) →
      θ * Fam.deg n ≤ Real.log q := by
  sorry

/-- The generic deduction, real parameters. -/
theorem measure_of_family_real (Fam : PolyFamily) {Λ D c g₁ g₂ : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hw : 0 < R.weight) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV Fam R g₁ g₂) (hwin : R.HasWindow) {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(c * (g₂ / (g₁ * (D - Λ)) + g₂ * (R.s : ℝ)) + e)) < |Fam.const - (p : ℝ) / q| := by
  sorry

/-- The generic deduction with rational parameters: exponent `measureExp c Λ D g₁ g₂ R.s`. -/
theorem measure_of_family (Fam : PolyFamily) {c Λ D g₁ g₂ : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hw : 0 < R.weight) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV Fam R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow) :
    Fam.MeasureLB ((measureExp c Λ D g₁ g₂ R.s : ℚ) : ℝ) := by
  sorry

/-- Rounding helper: any rational `E' ≥ measureExp …` is also a valid exponent. -/
theorem measure_of_family_le (Fam : PolyFamily) {c Λ D g₁ g₂ E' : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hw : 0 < R.weight) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV Fam R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow)
    (hE : measureExp c Λ D g₁ g₂ R.s ≤ E') :
    Fam.MeasureLB (E' : ℝ) := by
  sorry

/-- Square-frame corollary. -/
theorem measure_of_frame (Fr : Frame) {c Λ D g₁ g₂ : ℚ}
    (hΛ : HasContent (PolyFamily.ofFrame Fr) (Λ : ℝ))
    (hD : HasDecay (PolyFamily.ofFrame Fr) (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hw : 0 < R.weight) (hg : 0 < g₁ ∧ g₁ ≤ g₂)
    (hNV : HasNV (PolyFamily.ofFrame Fr) R (g₁ : ℝ) (g₂ : ℝ)) (hwin : R.HasWindow) :
    (PolyFamily.ofFrame Fr).MeasureLB ((measureExp c Λ D g₁ g₂ R.s : ℚ) : ℝ) :=
  measure_of_family _ hΛ hD hη hc R hw hg hNV hwin

/-- Irrationality of the constant of a family (no window needed; Dirichlet's theorem and
finiteness of the bad primes for a fixed `q`). -/
theorem irrational_of_family (Fam : PolyFamily) {Λ D c g₁ g₂ : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D)
    (R : PrimeRule) (hm : R.m ≠ 0) (hg : 0 < g₁)
    (hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ R.Bad l q)
    (hNV : HasNV Fam R g₁ g₂) : Irrational Fam.const := by
  sorry

theorem irrational_of_frame (Fr : Frame) {Λ D c g₁ g₂ : ℝ}
    (hΛ : HasContent (PolyFamily.ofFrame Fr) Λ) (hD : HasDecay (PolyFamily.ofFrame Fr) D c)
    (hη : Λ < D) (R : PrimeRule) (hm : R.m ≠ 0) (hg : 0 < g₁)
    (hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ R.Bad l q)
    (hNV : HasNV (PolyFamily.ofFrame Fr) R g₁ g₂) : Irrational Fr.const :=
  irrational_of_family _ hΛ hD hη R hm hg hbad hNV

end Measure
end CatalanCore
