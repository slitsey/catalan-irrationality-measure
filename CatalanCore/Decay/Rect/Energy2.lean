module

public import CatalanCore.Decay.Rect.Energy1

@[expose] public section

/-!
# Two-family energy step, part 2: `energy_rect` (WP-H2-core)

The rectangular analogue of `Frame.lemmaA`.  Row nodes `xnode r (s i)` and column nodes
`ynode r (s i)` (`s : Fin k → Fin (r + m)` with all extra nodes kept), the removed nodes are common
nodes, so the two energies share `energy_B` and the removed-node terms.

Assumptions on the certificate: `CertCoreG` for the abstract `g`, plus the soundness identity
`hg : g = (1+α) U^σ - (U^τ + U^ex_{2α}) + (1-ε) π |Im|`, and `α r ≤ m ≤ α r + 1`.
-/

open Finset
open CatalanLambda.Decay

namespace CatalanCore.Decay

lemma xnode_inj (r : ℕ) {a b : ℕ} (h : xnode r a = xnode r b) : a = b := by
  unfold xnode at h
  split_ifs at h <;> omega

lemma ynode_inj (r : ℕ) {a b : ℕ} (h : ynode r a = ynode r b) : a = b := by
  unfold ynode at h
  split_ifs at h <;> omega

lemma xnode_lt (r : ℕ) {b : ℕ} (hb : b < r) : xnode r b = b := by simp [xnode, hb]

lemma ynode_lt (r : ℕ) {b : ℕ} (hb : b < r) : ynode r b = b := by simp [ynode, hb]

lemma nodeC_inj_nat {r : ℕ} (hr : 0 < r) {a b : ℕ} (h : nodeC r a = nodeC r b) : a = b := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  simp only [nodeC, Complex.ofReal_inj] at h
  have : (a : ℝ) = b := by field_simp at h; exact h
  exact_mod_cast this

lemma natC_div (r b : ℕ) (hr : 0 < r) : (b : ℂ) / r = nodeC r b := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have := nat_eq_h_mul_nodeC hr b
  rw [this]
  exact mul_div_cancel_left₀ _ hrC

lemma nodeC_re (r b : ℕ) : (nodeC r b).re = (b : ℝ) / r := by simp [nodeC]

lemma nodeC_im (r b : ℕ) : (nodeC r b).im = 0 := by simp [nodeC]

/-- The `B`-expression of `energy_B`. -/
noncomputable def Bexp {k N : ℕ} (σ : Fin k → ℂ) (τ : Fin N → ℂ) (msk : Fin N → ℝ) : ℝ :=
  ∑ l, ∑ l', elog (σ l) (σ l') + 2 * ∑ l, ∑ b, msk b * elog (σ l) (τ b)
    + ∑ b, ∑ b', msk b * msk b' * elog (τ b) (τ b')

lemma Bexp_congr {k N : ℕ} (σ : Fin k → ℂ) (τ τ' : Fin N → ℂ) (msk : Fin N → ℝ)
    (h : ∀ b, msk b ≠ 0 → τ b = τ' b) : Bexp σ τ msk = Bexp σ τ' msk := by
  unfold Bexp
  have h1 : ∀ l b, msk b * elog (σ l) (τ b) = msk b * elog (σ l) (τ' b) := by
    intro l b
    by_cases hb : msk b = 0
    · simp [hb]
    · rw [h b hb]
  have h2 : ∀ b b', msk b * msk b' * elog (τ b) (τ b') = msk b * msk b' * elog (τ' b) (τ' b') := by
    intro b b'
    by_cases hb : msk b = 0
    · simp [hb]
    · by_cases hb' : msk b' = 0
      · simp [hb']
      · rw [h b hb, h b' hb']
  simp only [h1, h2]

/-- Pointwise comparison used for free points and for removed nodes. -/
lemma pt_ineq {r m : ℕ} {α ε A0 Y U I g δ' : ℝ} (hr' : 0 < (r : ℝ)) (hδ0 : 0 ≤ δ')
    (hδ1 : δ' ≤ 1) (hδdef : δ' = m - α * r) (hI : 0 ≤ I) (hA0 : 0 ≤ A0)
    (hY : -(A0 + (2 / r) * I) ≤ Y) (hg : g = (1 + α) * Y - U + ((1 - ε) * Real.pi / r) * I) :
    2 * r * g - 2 * (1 - ε) * Real.pi * I - 2 * A0 - (4 / r) * I
      ≤ 2 * ((r : ℝ) + m) * Y - 2 * r * U := by
  have hX0 : 0 ≤ A0 + (2 / r) * I := by positivity
  have h1 : 0 ≤ δ' * (Y + (A0 + (2 / r) * I)) := mul_nonneg hδ0 (by linarith)
  have h2 : δ' * (A0 + (2 / r) * I) ≤ A0 + (2 / r) * I := by nlinarith
  have hm : (m : ℝ) = δ' + α * r := by linarith
  have e : 2 * (r : ℝ) * g = 2 * r * (1 + α) * Y - 2 * r * U + 2 * (1 - ε) * Real.pi * I := by
    rw [hg]; field_simp
  have e2 : (4 / (r : ℝ)) * I = 2 * ((2 / r) * I) := by ring
  rw [e, hm, e2]
  nlinarith [h1, h2]

/-- Cross sums of an energy configuration. -/
noncomputable def PS {k N : ℕ} (σ : Fin k → ℂ) (τ : Fin N → ℂ) : ℝ := ∑ l, ∑ b, elog (σ l) (τ b)

noncomputable def AS {N : ℕ} (τ : Fin N → ℂ) : ℝ := ∑ b, ∑ b', elog (τ b) (τ b')

noncomputable def RS {N : ℕ} (msk : Fin N → ℝ) (τ : Fin N → ℂ) : ℝ :=
  ∑ b, ∑ b', msk b * elog (τ b) (τ b')

theorem Esc_decomp' {k N : ℕ} (σ : Fin k → ℂ) (τ : Fin N → ℂ) (s : Fin k → Fin N)
    (hs : Function.Injective s) :
    Esc σ (fun i => τ (s i)) = Bexp σ τ (rmask s) + AS τ - 2 * PS σ τ - 2 * RS (rmask s) τ :=
  Esc_decomp σ τ s hs

/-- The node potential `U^τ + U^ex_{2α}` of the hybrid node measure `Leb[0,1] + ½ Leb[1, 1+2α]`. -/
noncomputable def Unu (α : ℝ) (σ : ℂ) : ℝ := Utau σ + Uex (2 * α) σ

/-- The explicit error term of the rectangular Lemma A. -/
noncomputable def RerrR (Γd A0 ρ m0 Cl α : ℝ) (r m : ℕ) : ℝ :=
  2 * r * Γd + 2 * ((r : ℝ) + m) * A0 + m * Real.log (r + 2 * m)
    + 2 * ((r : ℝ) + m) * (Real.log (1 + r / m0) + Real.log (1 + 2 * m / r))
    + 2 * ((r : ℝ) + m) * (Real.log (1 + 2 * m) + |Real.log (2 * α)|)
    + ((r : ℝ) + m) * |Real.log ρ| + ((r : ℝ) + m) * Cl

end CatalanCore.Decay
