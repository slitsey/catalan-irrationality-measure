module
public import CatalanCore.Uniform.Measure.NV0
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Tactic.FieldSimp
@[expose] public section

namespace CatalanCore.Uniform
open Polynomial Finset

/-- Literal coefficient clearing, independent of evaluation points. -/
def Clears (P : ℚ[X]) (d : ℕ) : Prop :=
  0 < d ∧ ∀ k, ∃ z : ℤ, (d : ℚ) * P.coeff k = z

/-- Every rational polynomial has a positive coefficient denominator, including
zero polynomials and the finitely many scales outside an eventual estimate. -/
theorem exists_clears (P : ℚ[X]) : ∃ d, Clears P d := by
  let d := P.support.lcm (fun k => (P.coeff k).den)
  have hd : 0 < d := by
    rw [Nat.pos_iff_ne_zero, show d = P.support.lcm (fun k => (P.coeff k).den) from rfl,
      Ne, Finset.lcm_eq_zero_iff]
    simp only [not_exists, not_and]
    intro k hk
    exact Rat.den_nz _
  refine ⟨d, hd, ?_⟩
  intro k
  by_cases hk : k ∈ P.support
  · obtain ⟨u, hu⟩ := Finset.dvd_lcm (f := fun k => (P.coeff k).den) hk
    refine ⟨(P.coeff k).num * (u : ℤ), ?_⟩
    have hden : (d : ℚ) = (P.coeff k).den * u := by exact_mod_cast hu
    rw [hden]
    push_cast
    calc
      ((P.coeff k).den : ℚ) * u * P.coeff k =
        (P.coeff k * (P.coeff k).den) * u := by ring
      _ = _ := by rw [Rat.mul_den_eq_num]
  · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hk]⟩

noncomputable def leastDenominator (P : ℚ[X]) : ℕ := by
  classical
  exact Nat.find (exists_clears P)

theorem leastDenominator_clears (P : ℚ[X]) : Clears P (leastDenominator P) := by
  classical
  exact Nat.find_spec (exists_clears P)

theorem leastDenominator_le (P : ℚ[X]) {d : ℕ} (hd : Clears P d) :
    leastDenominator P ≤ d := by
  classical
  exact Nat.find_min' (exists_clears P) hd

/-- The degree upper bound, not exact polynomial degree or monicity, suffices. -/
theorem integral_evaluation (P : ℚ[X]) (n d : ℕ) (hP : P.natDegree ≤ n)
    (hd : Clears P d) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ n * d * P.eval ((p : ℚ) / q) = z := by
  choose z hz using hd.2
  refine ⟨∑ i ∈ range (n + 1), z i * p ^ i * q ^ (n - i), ?_⟩
  rw [Polynomial.eval_eq_sum_range' (n := n + 1) (by omega), Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (q : ℚ) ^ n = q ^ (n - i) * q ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [← hz i, he, div_pow]
  field_simp

/-- The paper's eventual per-member denominator statement. Denominators may
initially depend on the requested loss; no uniform choice is assumed. -/
def HasCoefficientContent (Fam : PolyFamily) (scale : Fam.ι → ℕ) (Λ : ℝ) : Prop :=
  ∀ ε > 0, ∃ R0 : ℕ, ∀ n, Fam.Adm n → R0 ≤ scale n →
    ∃ d, Clears (Fam.Q n) d ∧ Real.log (d : ℝ) ≤ (Λ + ε) * (scale n : ℝ) ^ 2

/-- Choosing the least positive coefficient denominator reconciles the paper's
quantifiers with the established global-denominator provider API. -/
theorem HasCoefficientContent.to_scaled (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ : ℝ} (hdegree : ∀ n, (Fam.Q n).natDegree ≤ Fam.deg n)
    (h : HasCoefficientContent Fam scale Λ) : HasScaledContent Fam scale Λ := by
  refine ⟨fun n => leastDenominator (Fam.Q n),
    fun n => (leastDenominator_clears (Fam.Q n)).1, ?_, ?_⟩
  · intro n hn p q hq
    exact integral_evaluation (Fam.Q n) (Fam.deg n) _ (hdegree n)
      (leastDenominator_clears (Fam.Q n)) p q hq
  · intro ε hε
    obtain ⟨R0, hR⟩ := h ε hε
    refine ⟨R0, ?_⟩
    intro n hn hr
    obtain ⟨d, hd, hlog⟩ := hR n hn hr
    have hpos : (0 : ℝ) < leastDenominator (Fam.Q n) := by
      exact_mod_cast (leastDenominator_clears (Fam.Q n)).1
    have hle : (leastDenominator (Fam.Q n) : ℝ) ≤ d := by
      exact_mod_cast leastDenominator_le (Fam.Q n) hd
    exact (Real.log_le_log hpos hle).trans hlog

/-- GMT with precisely eventual coefficient clearing, at full degree/scale generality. -/
theorem measure_of_coefficient_content_nv0 (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hdegree : ∀ n, (Fam.Q n).natDegree ≤ Fam.deg n)
    (hΛ : HasCoefficientContent Fam scale Λ) (hD : HasScaledDecay Fam scale D c)
    (hη : Λ < D) (hc : 0 < c) (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hnv : HasNV0 Fam scale) : Fam.MeasureLB (γ * c / (D - Λ)) :=
  measure_of_family_nv0 Fam scale
    (HasCoefficientContent.to_scaled Fam scale hdegree hΛ) hD hη hc hγ hK hdeg hnv

/-- Irrationality from the paper's eventual coefficient-clearing quantifiers. -/
theorem irrational_of_coefficient_content_nv0 (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hdegree : ∀ n, (Fam.Q n).natDegree ≤ Fam.deg n)
    (hΛ : HasCoefficientContent Fam scale Λ) (hD : HasScaledDecay Fam scale D c)
    (hη : Λ < D) (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hnv : HasNV0 Fam scale) : Irrational Fam.const :=
  irrational_of_family_nv0 Fam scale
    (HasCoefficientContent.to_scaled Fam scale hdegree hΛ) hD hη hγ hK hdeg hnv

end CatalanCore.Uniform


