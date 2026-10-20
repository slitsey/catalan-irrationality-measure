module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic

@[expose] public section

/-! # Finite moment interpolation without Laurent series

Vanishing moments shift the interpolation numerator by multiplication with X.
This gives its degree bound by one polynomial-product calculation.
-/

open Polynomial Finset

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k] [DecidableEq k]

noncomputable def rootProduct (s : Finset k) : k[X] :=
  ∏ a ∈ s, (X - C a)

noncomputable def punctured (s : Finset k) (a : k) : k[X] :=
  ∏ b ∈ s.erase a, (X - C b)

noncomputable def numerator (s : Finset k) (w : k → k) : k[X] :=
  ∑ a ∈ s, C (w a) * punctured s a

lemma rootProduct_factor (s : Finset k) {a : k} (ha : a ∈ s) :
    rootProduct s = (X - C a) * punctured s a := by
  classical
  unfold rootProduct punctured
  exact (Finset.mul_prod_erase s (fun b => (X - C b : k[X])) ha).symm

lemma numerator_recurrence (s : Finset k) (w : k → k) :
    X * numerator s w = numerator s (fun a => w a * a) +
      C (∑ a ∈ s, w a) * rootProduct s := by
  classical
  unfold numerator
  rw [Finset.mul_sum]
  calc
    (∑ a ∈ s, X * (C (w a) * punctured s a)) =
        ∑ a ∈ s, (C (w a * a) * punctured s a + C (w a) * rootProduct s) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [rootProduct_factor s ha, map_mul]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum]

lemma natDegree_numerator_le (s : Finset k) (w : k → k) :
    (numerator s w).natDegree ≤ s.card - 1 := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro a ha
  apply (natDegree_C_mul_le _ _).trans
  simp only [punctured, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_erase_of_mem ha]
  omega

lemma eval_punctured_of_ne (s : Finset k) {a b : k}
    (ha : a ∈ s) (hab : a ≠ b) : (punctured s b).eval a = 0 := by
  classical
  simp only [punctured, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, ha⟩)
  simp

lemma eval_numerator (s : Finset k) (w : k → k) {a : k} (ha : a ∈ s) :
    (numerator s w).eval a = w a * (rootProduct s).derivative.eval a := by
  classical
  have hs : (numerator s w).eval a = w a * (punctured s a).eval a := by
    simp only [numerator, eval_finsetSum, eval_mul, eval_C]
    apply Finset.sum_eq_single a
    · intro b hb hba
      rw [eval_punctured_of_ne s ha (Ne.symm hba), mul_zero]
    · exact fun h => (h ha).elim
  rw [hs, rootProduct_factor s ha, derivative_mul]
  simp

noncomputable def momentNumerator (s : Finset k) (w : k → k) (j : ℕ) : k[X] :=
  numerator s (fun a => w a * a ^ j)

lemma momentNumerator_succ (s : Finset k) (w : k → k) (j : ℕ)
    (hm : ∑ a ∈ s, w a * a ^ j = 0) :
    X * momentNumerator s w j = momentNumerator s w (j + 1) := by
  classical
  have he : (fun a => (w a * a ^ j) * a) = (fun a => w a * a ^ (j + 1)) := by
    funext a
    ring
  unfold momentNumerator
  rw [numerator_recurrence, hm, map_zero, zero_mul, add_zero, he]

lemma pow_mul_numerator (s : Finset k) (w : k → k) (n : ℕ)
    (hm : ∀ j < n, ∑ a ∈ s, w a * a ^ j = 0) :
    X ^ n * numerator s w = momentNumerator s w n := by
  classical
  induction n with
  | zero => simp [momentNumerator]
  | succ n ih =>
    have hi := ih (fun j hj => hm j (by omega))
    calc
      X ^ (n + 1) * numerator s w = X * (X ^ n * numerator s w) := by ring
      _ = X * momentNumerator s w n := by rw [hi]
      _ = momentNumerator s w (n + 1) :=
        momentNumerator_succ s w n (hm n (by omega))

/-- n vanishing moments lower the interpolation-numerator degree by n. -/
theorem natDegree_numerator_le_of_moments (s : Finset k) (w : k → k) (n : ℕ)
    (hm : ∀ j < n, ∑ a ∈ s, w a * a ^ j = 0) :
    (numerator s w).natDegree ≤ s.card - n - 1 := by
  classical
  by_cases hz : numerator s w = 0
  · simp [hz]
  have hpow : (X ^ n : k[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have he := pow_mul_numerator s w n hm
  have hb := natDegree_numerator_le s (fun a => w a * a ^ n)
  change (momentNumerator s w n).natDegree ≤ s.card - 1 at hb
  rw [← he, natDegree_mul hpow hz, natDegree_X_pow] at hb
  omega

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
