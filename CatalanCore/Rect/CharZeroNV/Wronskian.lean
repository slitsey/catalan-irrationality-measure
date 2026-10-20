module

public import CatalanCore.Rect.CharZeroNV.Antidifference
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.RootFactor

@[expose] public section

/-! # Degree and Hermite-root certificates for difference defects

Reuse the existing forward Wronskian and root-product infrastructure. The new
degree estimate cancels two terms when both input degrees are bounded by `d`.
-/

open Polynomial Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K]

theorem natDegree_wronskian_le (q p : K[X]) (d : ℕ)
    (hq : q.natDegree ≤ d) (hp : p.natDegree ≤ d)
    (hW : wronskian q p ≠ 0) : (wronskian q p).natDegree ≤ 2 * d - 2 := by
  have hlt := natDegree_wronskian_lt q p hW
  by_cases hpd : p.natDegree = d
  · have hp0 : p ≠ 0 := by intro hz; simp [hz, wronskian] at hW
    have hc : p.coeff d ≠ 0 := by
      rw [← hpd, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp0
    let q₀ := C (p.coeff d) * q - C (q.coeff d) * p
    have hq₀ : q₀.natDegree ≤ d - 1 := by
      apply natDegree_le_pred
      · exact (natDegree_sub_le _ _).trans (max_le
          ((natDegree_C_mul_le _ _).trans hq) ((natDegree_C_mul_le _ _).trans hp))
      · simp [q₀, mul_comm]
    have he : wronskian q₀ p = C (p.coeff d) * wronskian q p := by
      simp only [q₀, wronskian, sub_comp, mul_comp, C_comp]
      ring
    have hw₀ : wronskian q₀ p ≠ 0 := by
      rw [he]
      exact mul_ne_zero (C_ne_zero.mpr hc) hW
    have hd := natDegree_wronskian_lt q₀ p hw₀
    rw [he, natDegree_C_mul hc] at hd
    omega
  · omega

/-- The cleared difference equation. -/
noncomputable def defect (D A q p : K[X]) : K[X] :=
  D * wronskian q p - A * p * shift p

theorem natDegree_defect_le (D A q p : K[X]) (d : ℕ)
    (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1)
    (hq : q.natDegree ≤ d) (hp : p.natDegree ≤ d) :
    (defect D A q p).natDegree ≤ 2 * d + 1 := by
  have hr : (A * p * shift p).natDegree ≤ 2 * d + 1 := by
    have hs : (shift p).natDegree = p.natDegree := natDegree_shift p
    have h1 := natDegree_mul_le (p := A) (q := p)
    have h2 := natDegree_mul_le (p := A * p) (q := shift p)
    omega
  by_cases hw : wronskian q p = 0
  · simpa [defect, hw] using hr
  have hd := natDegree_wronskian_le q p d hq hp hw
  have hpos : 0 < d := by
    have hlt := natDegree_wronskian_lt q p hw
    omega
  have hl := natDegree_mul_le (p := D) (q := wronskian q p)
  exact (natDegree_sub_le _ _).trans (max_le (by omega) hr)

lemma square_dvd_of_value_derivative (p : K[X]) (a : K)
    (h0 : p.eval a = 0) (h1 : p.derivative.eval a = 0) :
    (X - C a) ^ 2 ∣ p := by
  obtain ⟨q, rfl⟩ := (dvd_iff_isRoot.mpr h0 : X - C a ∣ p)
  have hq : q.eval a = 0 := by simpa [derivative_mul] using h1
  obtain ⟨u, hu⟩ := (dvd_iff_isRoot.mpr hq : X - C a ∣ q)
  exact ⟨u, by rw [hu]; ring⟩

/-- A convenient multiplicity certificate, permitting overlap of the root sets. -/
theorem hermite_root_divisor [DecidableEq K] (s t : Finset K) (W : K[X])
    (hs : ∀ x ∈ s, W.eval x = 0) (ht : ∀ x ∈ t, W.derivative.eval x = 0) :
    (∏ x ∈ s, (X - C x) ^ (if x ∈ t then 2 else 1)) ∣ W := by
  classical
  apply prod_root_powers_dvd
  intro x hx
  by_cases hxt : x ∈ t
  · simpa [hxt] using square_dvd_of_value_derivative W x (hs x hx) (ht x hxt)
  · simpa [hxt] using (dvd_iff_isRoot.mpr (hs x hx) : X - C x ∣ W)

theorem eq_zero_of_hermite_roots [DecidableEq K] (s t : Finset K)
    (hts : t ⊆ s) (W : K[X]) (hs : ∀ x ∈ s, W.eval x = 0)
    (ht : ∀ x ∈ t, W.derivative.eval x = 0)
    (hd : W.natDegree < s.card + t.card) : W = 0 := by
  classical
  by_contra hW
  let G : K[X] := ∏ x ∈ s, (X - C x) ^ (if x ∈ t then 2 else 1)
  have hG : G.Monic := monic_prod_of_monic _ _ (fun x _ => (monic_X_sub_C x).pow _)
  have hdeg : G.natDegree = s.card + t.card := by
    rw [show G.natDegree = ∑ x ∈ s, (if x ∈ t then 2 else 1) by
      change (∏ x ∈ s, (X - C x) ^ (if x ∈ t then 2 else 1)).natDegree = _
      rw [natDegree_prod s (fun x : K => (X - C x : K[X]) ^ (if x ∈ t then 2 else 1))
        (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))]
      apply Finset.sum_congr rfl
      intro x _
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]]
    calc
      (∑ x ∈ s, if x ∈ t then 2 else 1) =
          ∑ x ∈ s, (1 + if x ∈ t then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
      _ = s.card + t.card := by
        rw [Finset.sum_add_distrib]
        simp [Finset.inter_eq_right.mpr hts]
  have hdiv : G ∣ W := hermite_root_divisor s t W hs ht
  have hle := natDegree_le_of_dvd hdiv hW
  omega

/-- Value interpolation at adjacent nodes gives a zero of the defect. -/
theorem defect_eval_zero (D A q p : K[X]) (x f₀ f₁ : K)
    (h0 : q.eval x = f₀ * p.eval x)
    (h1 : q.eval (x + 1) = f₁ * p.eval (x + 1))
    (hf : D.eval x * (f₁ - f₀) = A.eval x) :
    (defect D A q p).eval x = 0 := by
  simp only [defect, wronskian, eval_sub, eval_mul, eval_comp, eval_add,
    eval_X, eval_one, eval_shift, h0, h1]
  linear_combination hf * p.eval x * p.eval (x + 1)

/-- First-jet interpolation gives a double zero when the increment jets agree. -/
theorem defect_derivative_eval_zero (D A q p : K[X]) (x f₀ f₁ t₀ t₁ : K)
    (h0 : q.eval x = f₀ * p.eval x)
    (h1 : q.eval (x + 1) = f₁ * p.eval (x + 1))
    (hj0 : q.derivative.eval x = f₀ * p.derivative.eval x + t₀ * p.eval x)
    (hj1 : q.derivative.eval (x + 1) =
      f₁ * p.derivative.eval (x + 1) + t₁ * p.eval (x + 1))
    (hf : D.eval x * (f₁ - f₀) = A.eval x)
    (ht : D.derivative.eval x * (f₁ - f₀) + D.eval x * (t₁ - t₀) =
      A.derivative.eval x) :
    (defect D A q p).derivative.eval x = 0 := by
  simp only [defect, wronskian, shift, derivative_sub, derivative_mul,
    derivative_comp, derivative_add, derivative_X, derivative_one, add_zero,
    eval_sub, eval_add, eval_mul, eval_comp, eval_X, eval_one,
    h0, h1, hj0, hj1]
  linear_combination ht * p.eval x * p.eval (x + 1) +
    hf * (p.derivative.eval x * p.eval (x + 1) + p.eval x * p.derivative.eval (x + 1))

end CatalanCore.Rect.CharZeroNV
