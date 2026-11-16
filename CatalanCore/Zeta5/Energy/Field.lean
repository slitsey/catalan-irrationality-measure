module

public import CatalanCore.Zeta5.Energy.Config
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Energy.lean (`Vfield`), Apery/PotentialV.lean (`GVpot`, `hasDerivAt_GV`, `integral_log_add_sq`, `Vfield_eq`), Apery/EnergyFinal.lean (`sum_pairs_eq`) (Moritz Firsching); changes: module conversion, namespace CatalanCore.Zeta5.Energy, the closed form is extended to `t = 0` and given in the ledger's `arctan(A/√t)` and analytic-at-`y = 0` forms, `pointwise_bound` and `energy_ineq_final` are rebuilt for the measure `ν` (ZD08, ZD07) with the retained factor `√t/K`. -/

/-!
# The field `V` (ZD09), the pointwise bound (ZD08) and the configuration inequality (ZD07)

* `Vfield t = 2π√t + J₁(t) - 6 J_α(t)`, `J_A(t) = ∫₀^A log(t + u²) du`, α = 3/40 (ZD09), with
  `J_A(t) = A log(t + A²) - 2A + 2√t arctan(A/√t)` for all `t ≥ 0`
  (`integral_log_add_sq`) and `= A log(t + A²) - 2A + 2√t (π/2 - arctan(√t/A))` (`J_eq_analytic`);
* `CellHyp ν M₀` : the hypothesis the decay cells discharge: `2U - V ≤ M₀` on `[0, 4]` and
  `2U - V + √t/2 ≤ M₀` on `[4, ∞)`;
* `pointwise_bound` (ZD08) : `2U(t) - V(t) + √t/K ≤ M₀ + 2/K` for `K ≥ 2`, `t ≥ 0`;
* `config_ineq` (ZD07, ZD31) : the configuration inequality with the retained factor `e^{-√t}`
  (the term `∑ √tᵢ`): for pairwise distinct `tᵢ ≥ 0`,
  `2∑_{i<j} log|tᵢ - tⱼ| - K∑V(tᵢ) + ∑√tᵢ ≤ (λM₀ - I)K² + 2 h C_circ + 2 h log K + 2 h`.
-/

open MeasureTheory Set Real Filter Topology

namespace CatalanCore.Zeta5.Energy

/-- `J_A(t) = ∫₀^A log(t + u²) du`. -/
noncomputable def JA (A t : ℝ) : ℝ := ∫ u in (0 : ℝ)..A, Real.log (t + u ^ 2)

/-- **ZD09**: the external field of (6.1), `V(t) = 2π√t + J₁(t) - 6 J_α(t)`, `α = 3/40`. -/
noncomputable def Vfield (t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt t + (∫ u in (0 : ℝ)..1, Real.log (t + u ^ 2)) -
    6 * ∫ u in (0 : ℝ)..(3 / 40), Real.log (t + u ^ 2)

lemma Vfield_eq_J (t : ℝ) : Vfield t = 2 * Real.pi * Real.sqrt t + JA 1 t - 6 * JA (3 / 40) t := rfl

/-- Antiderivative of `u ↦ log (t + u²)`. -/
noncomputable def GVpot (t u : ℝ) : ℝ :=
  u * Real.log (t + u ^ 2) - 2 * u + 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t)

lemma hasDerivAt_GV {t : ℝ} (ht : 0 < t) (u : ℝ) : HasDerivAt (GVpot t) (Real.log (t + u ^ 2)) u := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : HasDerivAt (fun u : ℝ => u * Real.log (t + u ^ 2))
      (1 * Real.log (t + u ^ 2) + u * ((2 * u) / (t + u ^ 2))) u := by
    have hlog : HasDerivAt (fun u : ℝ => Real.log (t + u ^ 2)) ((2 * u) / (t + u ^ 2)) u := by
      have := ((hasDerivAt_pow 2 u).const_add t).log (by positivity)
      simpa using this
    exact (hasDerivAt_id u).mul hlog
  have h2 : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by simpa using (hasDerivAt_id u).const_mul 2
  have h3 : HasDerivAt (fun u : ℝ => 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t))
      (2 * Real.sqrt t * ((1 / (1 + (u / Real.sqrt t) ^ 2)) * (1 / Real.sqrt t))) u := by
    have := ((hasDerivAt_id u).div_const (Real.sqrt t)).arctan
    simpa using this.const_mul (2 * Real.sqrt t)
  have h := (h1.sub h2).add h3
  refine h.congr_deriv ?_
  have hne : t + u ^ 2 ≠ 0 := by positivity
  field_simp
  rw [hs2]
  ring

/-- **ZD09 closed form**: `J_A(t) = A log(t + A²) - 2A + 2√t arctan(A/√t)` for `t ≥ 0`. -/
lemma integral_log_add_sq {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, Real.log (t + u ^ 2) =
      c * Real.log (t + c ^ 2) - 2 * c + 2 * Real.sqrt t * Real.arctan (c / Real.sqrt t) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [Real.sqrt_zero, div_zero, Real.arctan_zero, mul_zero, add_zero, zero_add]
    have e : ∀ u : ℝ, Real.log (u ^ 2) = 2 * Real.log u := fun u => by
      rw [Real.log_pow]; push_cast; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_log]
    simp only [Real.log_zero, mul_zero, sub_zero]
    ring
  · have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c) (f := GVpot t)
      (f' := fun u => Real.log (t + u ^ 2)) (fun u _ => hasDerivAt_GV hpos u)
      ((Continuous.log (by fun_prop) (fun u => by positivity)).intervalIntegrable _ _)
    rw [this]
    simp [GVpot]

/-- The analytic-at-`y = 0` form `J_A(y²) = A log(y² + A²) - 2A + 2y(π/2 - arctan(y/A))`. -/
lemma J_eq_analytic {A : ℝ} (hA : 0 < A) {y : ℝ} (hy : 0 ≤ y) :
    JA A (y ^ 2) = A * Real.log (y ^ 2 + A ^ 2) - 2 * A + 2 * y * (π / 2 - Real.arctan (y / A)) := by
  unfold JA
  rw [integral_log_add_sq (by positivity), Real.sqrt_sq hy]
  rcases hy.eq_or_lt with h0 | hpos
  · subst h0; simp
  · rw [← Real.arctan_inv_of_pos (div_pos hpos hA)]
    simp [inv_div]

/-- **(A.5)**: the closed form of `V`. -/
theorem Vfield_eq {t : ℝ} (ht : 0 ≤ t) :
    Vfield t = Real.log (1 + t) - 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
      2 * Real.sqrt t * (Real.pi + Real.arctan (1 / Real.sqrt t) -
        6 * Real.arctan ((3 / 40) / Real.sqrt t)) := by
  unfold Vfield
  rw [integral_log_add_sq ht, integral_log_add_sq ht]
  ring_nf

/-! ### The cell hypothesis and the pointwise bound (ZD08) -/

/-- The pointwise inequality the decay cells must establish (`M₀` is the cells' bound):
`2U - V ≤ M₀` on `[0, 4]` and `2U - V + √t/2 ≤ M₀` on `[4, ∞)`. -/
def CellHyp (ν : Measure ℝ) (M₀ : ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 4, 2 * potU ν t - Vfield t ≤ M₀) ∧
    (∀ t : ℝ, 4 ≤ t → 2 * potU ν t - Vfield t + Real.sqrt t / 2 ≤ M₀)

/-- **ZD08**: `2U(t) - V(t) + √t/K ≤ M₀ + 2/K` for every `t ≥ 0` and `K ≥ 2`. -/
theorem pointwise_bound {ν : Measure ℝ} {M₀ : ℝ} (hc : CellHyp ν M₀) {K : ℝ} (hK : 2 ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    2 * potU ν t - Vfield t + Real.sqrt t / K ≤ M₀ + 2 / K := by
  have hK0 : 0 < K := by linarith
  rcases le_total t 4 with h | h
  · have h1 := hc.1 t ⟨ht, h⟩
    have hs : Real.sqrt t ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; linarith
    have : Real.sqrt t / K ≤ 2 / K := div_le_div_of_nonneg_right hs hK0.le
    linarith
  · have h1 := hc.2 t h
    have hs := Real.sqrt_nonneg t
    have : Real.sqrt t / K ≤ Real.sqrt t / 2 :=
      div_le_div_of_nonneg_left hs (by norm_num) hK
    have : (0 : ℝ) ≤ 2 / K := by positivity
    linarith

/-! ### The configuration inequality (ZD07) -/

/-- The double sum over all ordered pairs equals twice the sum over `i < j`. -/
lemma sum_pairs_eq {h : ℕ} (t : Fin h → ℝ) :
    ∑ i, ∑ i', Real.log |t i - t i'| = ∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i| := by
  have hsplit : ∀ i : Fin h, ∑ i', Real.log |t i - t i'| =
      ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| + ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    intro i
    have e1 : (Finset.univ : Finset (Fin h)).filter (fun x => x < i) = Finset.Iio i := by
      ext x; simp
    have e2 : (Finset.univ : Finset (Fin h)).filter (fun x => ¬ x < i) = Finset.Ici i := by
      ext x; simp [not_lt]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x < i), e1, e2,
      ← Finset.add_sum_Ioi_eq_sum_Ici, sub_self, abs_zero, Real.log_zero, zero_add]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hcomm : ∑ i, ∑ i' ∈ Finset.Iio i, Real.log |t i - t i'| =
      ∑ i, ∑ i' ∈ Finset.Ioi i, Real.log |t i - t i'| := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun i' => Finset.Ioi i')]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      rw [abs_sub_comm]
    · intro x y
      simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true]
  rw [hcomm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_sub_comm]; ring

/-- **ZD07 (with ZD31)**: the configuration inequality for a measure `ν` with the arcsine
majorant, any field `V` satisfying the pointwise bound, and the retained factor `∑ √tᵢ`:
for pairwise distinct `tᵢ ≥ 0`, `h = K ν(ℝ)`, `K ≥ 2`,

`2∑_{i<j} log|tᵢ - tⱼ| - K ∑ V(tᵢ) + ∑ √tᵢ ≤ (ν(ℝ) M₀ - I(ν)) K² + 2 h C_circ + 2 h log K + 2 h`

with `C_circ = 2√2 F/√b` and ε = K⁻². -/
theorem config_ineq {ν : Measure ℝ} [IsFiniteMeasure ν] {b F : ℝ} (hν : ArcMaj ν b F) {K : ℝ}
    (hK : 2 ≤ K) {h : ℕ} (hh : (h : ℝ) = K * ν.real univ) (V : ℝ → ℝ) {M₀ : ℝ}
    (hpt : ∀ x : ℝ, 0 ≤ x → 2 * potU ν x - V x + Real.sqrt x / K ≤ M₀ + 2 / K)
    (t : Fin h → ℝ) (ht0 : ∀ i, 0 ≤ t i) (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - K * ∑ i, V (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (ν.real univ * M₀ - energyI ν) * K ^ 2 + 2 * h * (2 * Real.sqrt 2 * F / Real.sqrt b) +
        2 * h * Real.log K + 2 * h := by
  have hK0 : 0 < K := by linarith
  have hε : 0 < (K ^ 2)⁻¹ := by positivity
  have hraw := energy_raw hν hK0 hh t hinj hε
  rw [sum_pairs_eq] at hraw
  have hlogε : Real.log (K ^ 2)⁻¹ = -2 * Real.log K := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  have hsqrt : Real.sqrt (K ^ 2)⁻¹ = K⁻¹ := by
    rw [← inv_pow, Real.sqrt_sq (by positivity)]
  rw [hlogε, hsqrt] at hraw
  set C : ℝ := 2 * Real.sqrt 2 * F / Real.sqrt b with hC
  have hpts : ∀ i, 2 * K * potU ν (t i) - K * V (t i) + Real.sqrt (t i) ≤ K * M₀ + 2 := by
    intro i
    have := mul_le_mul_of_nonneg_left (hpt (t i) (ht0 i)) hK0.le
    have e : K * (Real.sqrt (t i) / K) = Real.sqrt (t i) := by field_simp
    have e2 : K * (2 / K) = 2 := by field_simp
    nlinarith [this, e, e2]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpts i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum hraw
  have hlam : (h : ℝ) * (K * M₀) = ν.real univ * M₀ * K ^ 2 := by
    rw [hh]; ring
  have hKC : 2 * K * ((h : ℝ) * (C * K⁻¹)) = 2 * h * C := by
    field_simp
  rw [hlam] at hsum
  have hKC2 : 2 * K * ∑ i : Fin h, C * K⁻¹ = 2 * h * C := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hKC
  simp only [← Finset.mul_sum]
  nlinarith [hraw, hsum, hKC2]

end CatalanCore.Zeta5.Energy
