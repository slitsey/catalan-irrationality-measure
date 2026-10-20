module

public import CatalanCore.Rect.CharZeroNV.Wronskian

@[expose] public section

/-! # Rigidity of consecutive rational Hermite interpolation

All arithmetic data enter through cleared value and first-jet increment
identities. The conclusion excludes a low-degree pair, including pairs with
common factors or zeros at interpolation nodes.
-/

open Polynomial Finset

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K]

structure IncrementData (D A : K[X]) where
  f : ℕ → K
  tau : ℕ → K
  value_step : ∀ i : ℕ, D.eval (i : K) * (f (i + 1) - f i) = A.eval (i : K)
  jet_step : ∀ i : ℕ, D.derivative.eval (i : K) * (f (i + 1) - f i) +
    D.eval (i : K) * (tau (i + 1) - tau i) = A.derivative.eval (i : K)

structure Interpolates {D A : K[X]} (data : IncrementData D A)
    (N r : ℕ) (q p : K[X]) : Prop where
  value : ∀ i < N, q.eval (i : K) = data.f i * p.eval (i : K)
  jet : ∀ i < r, q.derivative.eval (i : K) =
    data.f i * p.derivative.eval (i : K) + data.tau i * p.eval (i : K)

noncomputable def natNodes (n : ℕ) : Finset K := by
  classical
  exact (range n).image (fun i : ℕ => (i : K))

omit [CharZero K] in
lemma mem_natNodes {n : ℕ} {x : K} : x ∈ natNodes n ↔ ∃ i < n, (i : K) = x := by
  classical
  simp [natNodes]

lemma card_natNodes (n : ℕ) : (natNodes n : Finset K).card = n := by
  classical
  rw [natNodes, card_image_of_injective _ (Nat.cast_injective (R := K)), card_range]

theorem no_short_pair {D A : K[X]} (data : IncrementData D A)
    (hpole : IsolatedIntegerPole D A) (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1)
    (N r d : ℕ)
    (hr : 1 ≤ r) (hrN : r ≤ N) (hsize : 2 * d + 1 < N + r - 2)
    (q p : K[X]) (hq : q.natDegree ≤ d) (hp : p.natDegree ≤ d)
    (hint : Interpolates data N r q p) : p = 0 := by
  classical
  by_contra hp0
  have hW : defect D A q p = 0 := by
    apply eq_zero_of_hermite_roots (natNodes (N - 1)) (natNodes (r - 1))
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
      exact mem_natNodes.mpr ⟨i, by omega, rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
      apply defect_eval_zero D A q p (i : K) (data.f i) (data.f (i + 1))
      · exact hint.value i (by omega)
      · simpa only [Nat.cast_succ] using hint.value (i + 1) (by omega)
      · exact data.value_step i
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
      apply defect_derivative_eval_zero D A q p (i : K)
        (data.f i) (data.f (i + 1)) (data.tau i) (data.tau (i + 1))
      · exact hint.value i (by omega)
      · simpa only [Nat.cast_succ] using hint.value (i + 1) (by omega)
      · exact hint.jet i (by omega)
      · simpa only [Nat.cast_succ] using hint.jet (i + 1) (by omega)
      · exact data.value_step i
      · exact data.jet_step i
    · rw [card_natNodes, card_natNodes]
      have hd := natDegree_defect_le D A q p d hD hA hq hp
      omega
  apply no_antidifference hpole q p hp0
  exact sub_eq_zero.mp hW

/-- The version with only consecutive values, used after removing a common
factor from a pair that vanishes on every common node. -/
theorem no_value_pair {D A : K[X]} (data : IncrementData D A)
    (hpole : IsolatedIntegerPole D A) (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1)
    (N d : ℕ) (hsize : 2 * d + 1 < N - 1)
    (q p : K[X]) (hq : q.natDegree ≤ d) (hp : p.natDegree ≤ d)
    (hint : ∀ i < N, q.eval (i : K) = data.f i * p.eval (i : K)) : p = 0 := by
  classical
  by_contra hp0
  have hW : defect D A q p = 0 := by
    apply eq_zero_of_hermite_roots (natNodes (N - 1)) ∅ (by simp)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
      apply defect_eval_zero D A q p (i : K) (data.f i) (data.f (i + 1))
      · exact hint i (by omega)
      · simpa only [Nat.cast_succ] using hint (i + 1) (by omega)
      · exact data.value_step i
    · simp
    · rw [card_natNodes, card_empty, add_zero]
      exact (natDegree_defect_le D A q p d hD hA hq hp).trans_lt hsize
  exact no_antidifference hpole q p hp0 (sub_eq_zero.mp hW)

/-- Two rational Hermite pairs have identically zero cross product. -/
theorem cross_product_eq_zero {D A : K[X]} (data : IncrementData D A)
    (N r d : ℕ) (hrN : r ≤ N) (hsize : 2 * d < N + r)
    (q p q' p' : K[X]) (hq : q.natDegree ≤ d) (hp : p.natDegree ≤ d)
    (hq' : q'.natDegree ≤ d) (hp' : p'.natDegree ≤ d)
    (h : Interpolates data N r q p) (h' : Interpolates data N r q' p') :
    q * p' - q' * p = 0 := by
  classical
  apply eq_zero_of_hermite_roots (natNodes N) (natNodes r)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    exact mem_natNodes.mpr ⟨i, by omega, rfl⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    simp only [eval_sub, eval_mul, h.value i hi, h'.value i hi]
    ring
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    simp only [derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul,
      h.value i (by omega), h'.value i (by omega), h.jet i hi, h'.jet i hi]
    ring
  · rw [card_natNodes, card_natNodes]
    have hd1 := natDegree_mul_le (p := q) (q := p')
    have hd2 := natDegree_mul_le (p := q') (q := p)
    have hd := natDegree_sub_le (q * p') (q' * p)
    omega

/-- Cleared increment data for a rational function without poles on the data grid. -/
noncomputable def quotientData (D A : K[X]) (hD : ∀ i : ℕ, D.eval (i : K) ≠ 0)
    (U : K) : IncrementData D A where
  f i := ∑ j ∈ range i, A.eval (j : K) / D.eval (j : K)
  tau i := U + ∑ j ∈ range i,
    (A.derivative.eval (j : K) * D.eval (j : K) -
      A.eval (j : K) * D.derivative.eval (j : K)) / (D.eval (j : K)) ^ 2
  value_step i := by
    simp only [sum_range_succ, add_sub_cancel_left]
    exact mul_div_cancel₀ _ (hD i)
  jet_step i := by
    simp only [sum_range_succ]
    field_simp [hD i]
    ring

end CatalanCore.Rect.CharZeroNV
