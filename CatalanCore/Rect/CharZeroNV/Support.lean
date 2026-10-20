module

public import CatalanCore.Rect.CharZeroNV.Barycentric

@[expose] public section

/-! # A nonzero interpolation pair meets the common nodes

Division by the common-node polynomial turns the common first jets into
ordinary values. The consecutive-value rigidity then excludes a kernel
supported only on the rational border.
-/

open Polynomial Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K]

theorem pair_eq_zero_of_common_values {D A : K[X]} (data : IncrementData D A)
    (hpole : IsolatedIntegerPole D A) (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1)
    (r m : ℕ) (hr : 1 ≤ r) (q p : K[X])
    (hq : q.natDegree ≤ r + m - 1) (hp : p.natDegree ≤ r + m - 1)
    (hint : Interpolates data (r + 2 * m) r q p)
    (hz : ∀ i < r, p.eval (i : K) = 0) : p = 0 := by
  classical
  let nodes : Finset K := natNodes r
  let DC := rootProduct nodes
  have hDC : DC.Monic := rootProduct_monic nodes
  have hdDC : DC.natDegree = r := by
    change (rootProduct nodes).natDegree = r
    rw [natDegree_rootProduct, card_natNodes]
  have hzC : ∀ x ∈ nodes, p.eval x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    exact hz i hi
  have hzqC : ∀ x ∈ nodes, q.eval x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
    rw [hint.value i (by omega), hz i hi, mul_zero]
  have hdp : DC ∣ p := by
    simpa using rootProduct_pow_dvd nodes 1 p (fun x hx => by
      simpa using (dvd_iff_isRoot.mpr (hzC x hx) : X - C x ∣ p))
  have hdq : DC ∣ q := by
    simpa using rootProduct_pow_dvd nodes 1 q (fun x hx => by
      simpa using (dvd_iff_isRoot.mpr (hzqC x hx) : X - C x ∣ q))
  obtain ⟨p₀, hpform⟩ := hdp
  obtain ⟨q₀, hqform⟩ := hdq
  by_contra hp0
  have hp₀0 : p₀ ≠ 0 := by intro h; simp [hpform, h] at hp0
  have hpmul := natDegree_mul hDC.ne_zero hp₀0
  rw [← hpform, hdDC] at hpmul
  have hm : 1 ≤ m := by omega
  have hpd : p₀.natDegree ≤ m - 1 := by omega
  have hqd : q₀.natDegree ≤ m - 1 := by
    by_cases hq0 : q₀ = 0
    · simp [hq0]
    have hqmul := natDegree_mul hDC.ne_zero hq0
    rw [← hqform, hdDC] at hqmul
    omega
  have hvalues : ∀ i < r + 2 * m,
      q₀.eval (i : K) = data.f i * p₀.eval (i : K) := by
    intro i hi
    by_cases hic : i < r
    · have him : (i : K) ∈ nodes := mem_natNodes.mpr ⟨i, hic, rfl⟩
      have heD : DC.eval (i : K) = 0 := by
        change (rootProduct nodes).eval (i : K) = 0
        rw [rootProduct_factor nodes him]
        simp
      have heD' : DC.derivative.eval (i : K) ≠ 0 := by
        change (rootProduct nodes).derivative.eval (i : K) ≠ 0
        rw [rootProduct_factor nodes him, derivative_mul]
        simpa using punctured_eval_ne_zero nodes (i : K)
      have hj := hint.jet i hic
      rw [hqform, hpform] at hj
      simp only [derivative_mul, eval_add, eval_mul, heD, zero_mul, add_zero] at hj
      apply mul_left_cancel₀ heD'
      linear_combination hj
    · have him : (i : K) ∉ nodes := by
        intro hm'
        obtain ⟨j, hj, he⟩ := mem_natNodes.mp hm'
        have : j = i := Nat.cast_injective he
        omega
      have heD : DC.eval (i : K) ≠ 0 := rootProduct_eval_ne_zero nodes (i : K) him
      have hv := hint.value i hi
      rw [hqform, hpform, eval_mul, eval_mul] at hv
      apply mul_left_cancel₀ heD
      linear_combination hv
  exact hp₀0 (no_value_pair data hpole hD hA (r + 2 * m) (m - 1)
    (by omega) q₀ p₀ hqd hpd hvalues)

end CatalanCore.Rect.CharZeroNV
