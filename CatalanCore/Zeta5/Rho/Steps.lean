module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# Riemann-sum comparison by the mean value theorem (generic; ledger ZR02, ZR04)

`φ' = f` monotone gives one-step bounds `(y - x) f x ≤ φ y - φ x ≤ (y - x) f y` using only the
mean value theorem: `φ` need be continuous on `[x, y]` and differentiable on the open interval, so
that an endpoint where `f` is singular (a logarithmic pole) costs nothing.  The sum versions
telescope.  No integrals appear.
-/

namespace CatalanCore.Zeta5.Rho

open Set Finset

/-- One step, monotone derivative, left value: `(y - x) f x ≤ φ y - φ x`. -/
theorem step_left_le {φ f : ℝ → ℝ} {x y : ℝ} (hxy : x < y) (hc : ContinuousOn φ (Icc x y))
    (hd : ∀ s ∈ Ioo x y, HasDerivAt φ (f s) s) (hm : MonotoneOn f (Ico x y)) :
    (y - x) * f x ≤ φ y - φ x := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope φ f hxy hc hd
  have h1 : f x ≤ f ξ := hm ⟨le_refl x, hxy⟩ ⟨hξ.1.le, hξ.2⟩ hξ.1.le
  have h2 : φ y - φ x = f ξ * (y - x) := by
    rw [h]; field_simp [(sub_pos.mpr hxy).ne']
  rw [h2]; nlinarith [sub_pos.mpr hxy]

/-- One step, monotone derivative, right value: `φ y - φ x ≤ (y - x) f y`. -/
theorem step_le_right {φ f : ℝ → ℝ} {x y : ℝ} (hxy : x < y) (hc : ContinuousOn φ (Icc x y))
    (hd : ∀ s ∈ Ioo x y, HasDerivAt φ (f s) s) (hm : MonotoneOn f (Ioc x y)) :
    φ y - φ x ≤ (y - x) * f y := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope φ f hxy hc hd
  have h1 : f ξ ≤ f y := hm ⟨hξ.1, hξ.2.le⟩ ⟨hxy, le_refl y⟩ hξ.2.le
  have h2 : φ y - φ x = f ξ * (y - x) := by
    rw [h]; field_simp [(sub_pos.mpr hxy).ne']
  rw [h2]; nlinarith [sub_pos.mpr hxy]

/-- One step, antitone derivative, left value: `φ y - φ x ≤ (y - x) f x`. -/
theorem step_le_left_anti {φ f : ℝ → ℝ} {x y : ℝ} (hxy : x < y) (hc : ContinuousOn φ (Icc x y))
    (hd : ∀ s ∈ Ioo x y, HasDerivAt φ (f s) s) (hm : AntitoneOn f (Ico x y)) :
    φ y - φ x ≤ (y - x) * f x := by
  have := step_left_le (φ := fun s => -φ s) (f := fun s => -f s) hxy hc.neg
    (fun s hs => (hd s hs).neg) (fun a ha b hb hab => neg_le_neg (hm ha hb hab))
  linarith

/-- One step, antitone derivative, right value: `(y - x) f y ≤ φ y - φ x`. -/
theorem step_right_le_anti {φ f : ℝ → ℝ} {x y : ℝ} (hxy : x < y) (hc : ContinuousOn φ (Icc x y))
    (hd : ∀ s ∈ Ioo x y, HasDerivAt φ (f s) s) (hm : AntitoneOn f (Ioc x y)) :
    (y - x) * f y ≤ φ y - φ x := by
  have := step_le_right (φ := fun s => -φ s) (f := fun s => -f s) hxy hc.neg
    (fun s hs => (hd s hs).neg) (fun a ha b hb hab => neg_le_neg (hm ha hb hab))
  linarith

/-- Telescoping: termwise `a i ≤ b (i+1) - b i` on `[p, q)` sums to `b q - b p`. -/
theorem sum_Ico_le_telescope (a b : ℕ → ℝ) {p q : ℕ} (hpq : p ≤ q)
    (h : ∀ i, p ≤ i → i < q → a i ≤ b (i + 1) - b i) :
    ∑ i ∈ Ico p q, a i ≤ b q - b p := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    rw [Finset.sum_Ico_succ_top hpq]
    have h1 := ih (fun i hi hiq => h i hi (by omega))
    have h2 := h q hpq (by omega)
    linarith

/-- Telescoping, reverse inequality. -/
theorem telescope_le_sum_Ico (a b : ℕ → ℝ) {p q : ℕ} (hpq : p ≤ q)
    (h : ∀ i, p ≤ i → i < q → b (i + 1) - b i ≤ a i) :
    b q - b p ≤ ∑ i ∈ Ico p q, a i := by
  have := sum_Ico_le_telescope (fun i => - a i) (fun i => - b i) hpq
    (fun i hi hiq => by have := h i hi hiq; linarith)
  simp only [Finset.sum_neg_distrib] at this
  linarith

/-- Telescoping over `Icc 1 N`: `a l ≤ b l - b (l-1)`. -/
theorem sum_Icc_le_telescope (a b : ℕ → ℝ) (N : ℕ)
    (h : ∀ l, 1 ≤ l → l ≤ N → a l ≤ b l - b (l - 1)) :
    ∑ l ∈ Icc 1 N, a l ≤ b N - b 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := ih (fun l h1 h2 => h l h1 (by omega))
    have h2 := h (N + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at h2
    linarith

/-- Telescoping over `Icc 1 N`, reverse inequality. -/
theorem telescope_le_sum_Icc (a b : ℕ → ℝ) (N : ℕ)
    (h : ∀ l, 1 ≤ l → l ≤ N → b l - b (l - 1) ≤ a l) :
    b N - b 0 ≤ ∑ l ∈ Icc 1 N, a l := by
  have := sum_Icc_le_telescope (fun i => - a i) (fun i => - b i) N
    (fun l h1 h2 => by have := h l h1 h2; linarith)
  simp only [Finset.sum_neg_distrib] at this
  linarith

/-- Telescoping over `Ioc p q`: `b l - b (l-1) ≤ a l`. -/
theorem telescope_le_sum_Ioc (a b : ℕ → ℝ) (p q : ℕ) (hpq : p ≤ q)
    (h : ∀ l, p < l → l ≤ q → b l - b (l - 1) ≤ a l) :
    b q - b p ≤ ∑ l ∈ Ioc p q, a l := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ q hpq ih =>
    rw [Finset.sum_Ioc_succ_top hpq]
    have h1 := ih (fun l h1 h2 => h l h1 (by omega))
    have h2 := h (q + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at h2
    linarith

end CatalanCore.Zeta5.Rho
