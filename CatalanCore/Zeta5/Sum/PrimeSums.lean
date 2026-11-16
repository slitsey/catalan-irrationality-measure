module

public import OAI.NumberTheory.Catalan.PrimeLimits.ContinuousWeightedPNT
public import OAI.NumberTheory.Catalan.PrimeLimits.ImportedPNTCoreBridge
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# ZC28: weighted prime sums and Chebyshev's bound

* `theta_le_linear` : `θ(y) ≤ log 4 · y` for `y ≥ 0` (Chebyshev, from Mathlib), in particular
  `θ(y) = O(y)`.
* `PiecewiseCont F c n` : `F` is piecewise continuous on `[c₀, cₙ]`: strictly increasing
  breakpoints `c₀ < … < cₙ`, and on each open cell `F` agrees with a function continuous on the
  closed cell (one-sided limits at the breakpoints; the values of `F` at the breakpoints are
  arbitrary).
* `weighted_prime_sum_tendsto` : for such `F` and `0 < c₀`,
  `R⁻¹ Σ_{c₀ R < p ≤ cₙ R} F(p/R) log p → ∫_{c₀}^{cₙ} F` as `R → ∞` (PNT, with
  `OAI.…weightedPrimeIntervalSum` the normalised sum). Natural-number form:
  `weighted_prime_sum_tendsto_nat` (`Σ_p φ(p/K) log p = K ∫ φ + o(K)`).
-/

set_option linter.deprecated false

open Filter Finset Set MeasureTheory
open scoped Topology

namespace CatalanCore.Zeta5.Sum

open OAI.Zeta5.Workers.W14

/-- Chebyshev: `θ(y) ≤ log 4 · y`. -/
theorem theta_le_linear {y : ℝ} (hy : 0 ≤ y) : Chebyshev.theta y ≤ Real.log 4 * y :=
  Chebyshev.theta_le_log4_mul_x hy

/-- The prime number theorem in the form used: `θ(R)/R → 1`. -/
theorem pnt_theta : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1) :=
  OAI.Zeta5.W12.ImportedPNTCoreBridge.theta_ratio_tendsto_one

/-- `F` is piecewise continuous on `[c 0, c n]`. -/
def PiecewiseCont (F : ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ i < n, c i < c (i + 1)) ∧
    ∀ i < n, ∃ G : ℝ → ℝ, ContinuousOn G (Icc (c i) (c (i + 1))) ∧
      ∀ x ∈ Ioo (c i) (c (i + 1)), F x = G x

/-- Two integrands that differ only at the right endpoint `b` change the weighted prime sum by at
most one term. -/
lemma wps_point {F F' : ℝ → ℝ} {a b R : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hR : 0 < R)
    (hbR : 1 ≤ b * R) (hFF : ∀ x ∈ Ioo a b, F x = F' x) :
    |weightedPrimeIntervalSum F a b R - weightedPrimeIntervalSum F' a b R| ≤
      |F b - F' b| * (Real.log (b * R) / R) := by
  unfold weightedPrimeIntervalSum
  rw [← sub_div, abs_div, abs_of_pos hR, ← Finset.sum_sub_distrib, div_le_iff₀ hR]
  set S := (Finset.Ioc ⌊a * R⌋₊ ⌊b * R⌋₊).filter Nat.Prime with hS
  have hmem : ∀ p ∈ S, a < (p : ℝ) / R ∧ (p : ℝ) / R ≤ b ∧ p.Prime := by
    intro p hp
    have := (mem_primeInterval_iff (mul_nonneg ha hR.le)
      (mul_le_mul_of_nonneg_right hab hR.le) p).mp hp
    exact ⟨(lt_div_iff₀ hR).mpr this.1, (div_le_iff₀ hR).mpr this.2.1, this.2.2⟩
  set d : ℕ → ℝ := fun p =>
    F ((p : ℝ) / R) * Real.log (p : ℝ) - F' ((p : ℝ) / R) * Real.log (p : ℝ) with hd
  set M : ℝ := |F b - F' b| * Real.log (b * R) with hM
  have hM0 : 0 ≤ M := mul_nonneg (abs_nonneg _) (Real.log_nonneg hbR)
  have hz : ∀ p ∈ S, d p ≠ 0 → (p : ℝ) / R = b := by
    intro p hp hne
    by_contra hpb
    apply hne
    have hm := hmem p hp
    have hlt : (p : ℝ) / R < b := lt_of_le_of_ne hm.2.1 hpb
    have := hFF _ ⟨hm.1, hlt⟩
    simp only [hd, this]; ring
  rw [← Finset.sum_filter_of_ne hz]
  set S' := S.filter (fun p : ℕ => (p : ℝ) / R = b) with hS'
  have hbd : ∀ p ∈ S', |d p| ≤ M := by
    intro p hp
    rw [hS', Finset.mem_filter] at hp
    have hpb : (p : ℝ) / R = b := hp.2
    have hpR : (p : ℝ) = b * R := by field_simp at hpb ⊢; linarith
    have : d p = (F b - F' b) * Real.log (p : ℝ) := by
      simp only [hd, hpb]; ring
    rw [this, abs_mul, hM, hpR, abs_of_nonneg (Real.log_nonneg hbR)]
  have hcard : S'.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    rw [hS', Finset.mem_filter] at hp hq
    have e1 : (p : ℝ) = q := by
      have := hp.2.trans hq.2.symm
      field_simp at this; exact this
    exact_mod_cast e1
  calc |∑ p ∈ S', d p| ≤ ∑ p ∈ S', |d p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ S'.card • M := Finset.sum_le_card_nsmul _ _ _ hbd
    _ ≤ M := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h | h
        · rw [h]; simp [hM0]
        · rw [h]; simp
    _ = |F b - F' b| * (Real.log (b * R) / R) * R := by rw [hM]; field_simp

lemma tendsto_log_mul_div {b : ℝ} (hb : 0 < b) :
    Tendsto (fun R : ℝ => Real.log (b * R) / R) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => b * R) atTop atTop := tendsto_id.const_mul_atTop hb
  have h2 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp h1
  have h3 := h2.const_mul b
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  simp only [Function.comp, id]
  field_simp

/-- One continuous cell (the value of `F` at the right endpoint is arbitrary). -/
lemma cell_tendsto {F G : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hG : ContinuousOn G (Icc a b)) (hFG : ∀ x ∈ Ioo a b, F x = G x) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) := by
  set F' : ℝ → ℝ := fun x => if x = b then G b else F x with hF'
  have hF'G : ∀ x ∈ Ioc a b, F' x = G x := by
    intro x hx
    by_cases h : x = b
    · simp [hF', h]
    · simp only [hF', if_neg h]; exact hFG x ⟨hx.1, lt_of_le_of_ne hx.2 h⟩
  have h1 := continuous_extension_weightedPrime_tendsto ha hab hG hF'G pnt_theta
  have heq : Set.EqOn F' F (Set.uIoo a b) := by
    intro x hx
    rw [Set.uIoo_of_le hab.le] at hx
    simp only [hF', if_neg (ne_of_lt hx.2)]
  have hint : (∫ x in a..b, F' x) = ∫ x in a..b, F x := intervalIntegral.integral_congr_uIoo heq
  rw [hint] at h1
  have hb : 0 < b := ha.trans hab
  have herr : Tendsto (fun R : ℝ => weightedPrimeIntervalSum F a b R -
      weightedPrimeIntervalSum F' a b R) atTop (𝓝 0) := by
    have hbd : Tendsto (fun R : ℝ => |F b - F' b| * (Real.log (b * R) / R)) atTop (𝓝 0) := by
      simpa using (tendsto_log_mul_div hb).const_mul |F b - F' b|
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [eventually_gt_atTop (1 / b)] with R hR
    have hR0 : 0 < R := lt_trans (by positivity) hR
    have hbR : 1 ≤ b * R := by
      have := (div_lt_iff₀ hb).1 hR
      linarith
    rw [Real.norm_eq_abs]
    exact wps_point ha.le hab.le hR0 hbR (fun x hx => by
      simp only [hF', if_neg (ne_of_lt hx.2)])
  have := h1.add herr
  simp only [add_zero] at this
  refine this.congr (fun R => ?_)
  ring

lemma c_mono {c : ℕ → ℝ} {n : ℕ} (hc : ∀ i < n, c i < c (i + 1)) : ∀ i ≤ n, c 0 ≤ c i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih =>
    intro hi
    exact (ih (by omega)).trans (hc i (by omega)).le

lemma piecewise_cell_integrable {F : ℝ → ℝ} {a b : ℝ} (hab : a < b) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc a b)) (hFG : ∀ x ∈ Ioo a b, F x = G x) :
    IntervalIntegrable F volume a b := by
  have hGi : IntervalIntegrable G volume a b :=
    (hG.mono (by rw [Set.uIcc_of_le hab.le])).intervalIntegrable
  exact hGi.congr_uIoo (by
    intro x hx
    rw [Set.uIoo_of_le hab.le] at hx
    exact (hFG x hx).symm)

/-- **ZC28.** For a piecewise continuous `F` on `[c₀, cₙ]`, `0 < c₀`:
`R⁻¹ Σ_{c₀R < p ≤ cₙR} F(p/R) log p → ∫_{c₀}^{cₙ} F`. -/
theorem weighted_prime_sum_tendsto {F : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ} (h0 : 0 < c 0)
    (hF : PiecewiseCont F c n) :
    IntervalIntegrable F volume (c 0) (c n) ∧
      Tendsto (weightedPrimeIntervalSum F (c 0) (c n)) atTop (𝓝 (∫ x in c 0..c n, F x)) := by
  obtain ⟨hc, hcell⟩ := hF
  induction n with
  | zero =>
    refine ⟨by rw [intervalIntegrable_iff]; simp, ?_⟩
    have e : weightedPrimeIntervalSum F (c 0) (c 0) = fun _ => 0 := by
      funext R; simp [weightedPrimeIntervalSum]
    rw [e]; simp
  | succ n ih =>
    obtain ⟨hI, hT⟩ := ih (fun i hi => hc i (by omega)) (fun i hi => hcell i (by omega))
    obtain ⟨G, hG, hFG⟩ := hcell n (by omega)
    have hcn : 0 < c n := lt_of_lt_of_le h0 (c_mono (fun i hi => hc i (by omega)) n le_rfl)
    have hlt : c n < c (n + 1) := hc n (by omega)
    have hI2 := piecewise_cell_integrable hlt hG hFG
    have hT2 := cell_tendsto hcn hlt hG hFG
    refine ⟨hI.trans hI2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hI hI2]
    refine (hT.add hT2).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact weightedPrimeIntervalSum_add_adjacent F
      (c_mono (fun i hi => hc i (by omega)) n le_rfl) hlt.le hR.le

/-- Natural-number form: `Σ_{c₀K < p ≤ cₙK} F(p/K) log p = K ∫ F + o(K)`. -/
theorem weighted_prime_sum_tendsto_nat {F : ℝ → ℝ} {c : ℕ → ℝ} {n : ℕ} (h0 : 0 < c 0)
    (hF : PiecewiseCont F c n) :
    Tendsto (fun K : ℕ => (∑ p ∈ Finset.Ioc ⌊c 0 * K⌋₊ ⌊c n * K⌋₊ with p.Prime,
        F ((p : ℝ) / K) * Real.log (p : ℝ)) / K) atTop (𝓝 (∫ x in c 0..c n, F x)) :=
  (weighted_prime_sum_tendsto h0 hF).2.comp tendsto_natCast_atTop_atTop

end CatalanCore.Zeta5.Sum
