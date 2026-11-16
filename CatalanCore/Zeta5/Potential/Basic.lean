module

public import CatalanMeasure.GenD.Signed.ArcsineDenominator

/-!
# Z5-POTENTIAL, part 1: Chebyshev series against the arcsine law

`chebF c N` is `f = Σ_{k ≤ N} c_k T_k`.  The arcsine law is the angle law `dθ/π` on `[0, π]`
(`CatalanMeasure.Signed.denMeasure` with the trivial trial).  This file proves the orthogonality
`∫ T_k T_j = δ_{kj}/2` (`1` for `k = j = 0`), the moments `∫ f T_k`, and termwise integration of
`f · Σ a_k T_{k+1}(cos θ)` against a summable series.  Generic in the coefficient vector `c`.
-/

@[expose] public section

open MeasureTheory Set Polynomial CatalanMeasure.Signed OAI.InternalCatalan

namespace CatalanCore.Zeta5.Potential

noncomputable section

/-- Coefficient form `f(x) = Σ_{k=0}^N c_k T_k(x)`. -/
def chebF (c : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), c k * (Chebyshev.T ℝ (k : ℤ)).eval x

theorem chebF_cos (c : ℕ → ℝ) (N : ℕ) (θ : ℝ) :
    chebF c N (Real.cos θ) = ∑ k ∈ Finset.range (N + 1), c k * Real.cos ((k : ℝ) * θ) := by
  unfold chebF
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Chebyshev.T_real_cos]
  simp

theorem continuous_chebF (c : ℕ → ℝ) (N : ℕ) : Continuous (chebF c N) := by
  unfold chebF
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (Polynomial.continuous _)

theorem abs_chebF_le (c : ℕ → ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |chebF c N x| ≤ ∑ k ∈ Finset.range (N + 1), |c k| := by
  unfold chebF
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (energy_chebyshev_abs_le_one k hx)

/-- The unit arcsine law in the angle `θ ∈ [0, π]` (density `1/π`). -/
abbrev arc : Measure ℝ := denMeasure (fun _ => 0) 0

instance : IsProbabilityMeasure arc := isProbabilityMeasure_denMeasure isTrial_arcsine

theorem integral_arc (g : ℝ → ℝ) :
    ∫ θ, g θ ∂arc = ∫ θ in (0 : ℝ)..Real.pi, (1 / Real.pi) * g θ := by
  rw [integral_denMeasure isTrial_arcsine]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp [denQ, chebP]

theorem cos_mem (θ : ℝ) : Real.cos θ ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

theorem integrable_arc_of_bound {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (h : ∀ θ, |g θ| ≤ C) :
    Integrable g arc :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (ae_of_all _ fun θ => by simpa [Real.norm_eq_abs] using h θ)

theorem integral_T_int (m : ℤ) (hm : m ≠ 0) :
    ∫ θ, (Chebyshev.T ℝ m).eval (Real.cos θ) ∂arc = 0 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by rintro rfl; simp at hm
    have := integral_cheb_denMeasure (b := fun _ => 0) (K := 0) isTrial_arcsine hn
    simpa using this
  · have hn : n ≠ 0 := by rintro rfl; simp at hm
    have := integral_cheb_denMeasure (b := fun _ => 0) (K := 0) isTrial_arcsine hn
    rw [Chebyshev.T_neg]
    simpa using this

theorem integral_T_T (k j : ℕ) :
    ∫ θ, (Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) * (Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) ∂arc =
      if k = j then (if k = 0 then 1 else 1 / 2) else 0 := by
  have key : ∀ θ, (Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) *
      (Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) =
      (1 / 2) * (Chebyshev.T ℝ ((k : ℤ) + j)).eval (Real.cos θ) +
        (1 / 2) * (Chebyshev.T ℝ ((k : ℤ) - j)).eval (Real.cos θ) := by
    intro θ
    have := Chebyshev.T_mul_T ℝ (k : ℤ) (j : ℤ)
    have h2 := congrArg (fun p => p.eval (Real.cos θ)) this
    simp only [eval_mul, eval_add, eval_ofNat] at h2
    linarith
  simp_rw [key]
  have i1 : ∀ m : ℤ, Integrable (fun θ => (Chebyshev.T ℝ m).eval (Real.cos θ)) arc := by
    intro m
    refine integrable_arc_of_bound (C := 1) ((Polynomial.continuous _).comp Real.continuous_cos)
      fun θ => ?_
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · exact energy_chebyshev_abs_le_one n (cos_mem θ)
    · rw [Chebyshev.T_neg]; exact energy_chebyshev_abs_le_one n (cos_mem θ)
  rw [integral_add ((i1 _).const_mul _) ((i1 _).const_mul _), integral_const_mul, integral_const_mul]
  by_cases hkj : k = j
  · subst hkj
    by_cases hk : k = 0
    · subst hk; norm_num
    · have h1 : ((k : ℤ) + k) ≠ 0 := by omega
      rw [integral_T_int _ h1]
      simp [hk]
  · have h1 : ((k : ℤ) + j) ≠ 0 := by omega
    have h2 : ((k : ℤ) - j) ≠ 0 := by omega
    rw [integral_T_int _ h1, integral_T_int _ h2]
    simp [hkj]


theorem integrable_T_cos (m : ℤ) : Integrable (fun θ => (Chebyshev.T ℝ m).eval (Real.cos θ)) arc := by
  refine integrable_arc_of_bound (C := 1) ((Polynomial.continuous _).comp Real.continuous_cos)
    fun θ => ?_
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact energy_chebyshev_abs_le_one n (cos_mem θ)
  · rw [Chebyshev.T_neg]; exact energy_chebyshev_abs_le_one n (cos_mem θ)

theorem integrable_aTT (a : ℝ) (j k : ℕ) :
    Integrable (fun θ => a * (Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) *
      (Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ)) arc := by
  refine integrable_arc_of_bound (C := |a|)
    (((continuous_const.mul ((Polynomial.continuous _).comp Real.continuous_cos)).mul
      ((Polynomial.continuous _).comp Real.continuous_cos))) fun θ => ?_
  have h1 := energy_chebyshev_abs_le_one j (cos_mem θ)
  have h2 := energy_chebyshev_abs_le_one k (cos_mem θ)
  rw [abs_mul, abs_mul]
  have h3 : |(Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ)| *
      |(Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ)| ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [mul_assoc]
  exact mul_le_of_le_one_right (abs_nonneg _) h3

theorem integral_chebF_mul_T (c : ℕ → ℝ) (N k : ℕ) :
    ∫ θ, chebF c N (Real.cos θ) * (Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) ∂arc =
      if k ≤ N then c k * (if k = 0 then 1 else 1 / 2) else 0 := by
  unfold chebF
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => ?_]
  · simp_rw [mul_assoc, integral_const_mul, integral_T_T]
    by_cases hk : k ≤ N
    · simp only [hk, ite_true]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · simp only [hk, ite_false]
      refine Finset.sum_eq_zero fun j hj => ?_
      have : j ≠ k := by
        have := Finset.mem_range.mp hj; omega
      simp [this]
  · exact integrable_aTT (c j) j k


theorem continuous_chebF_cos (c : ℕ → ℝ) (N : ℕ) : Continuous fun θ => chebF c N (Real.cos θ) :=
  (continuous_chebF c N).comp Real.continuous_cos

theorem integral_chebF (c : ℕ → ℝ) (N : ℕ) :
    ∫ θ, chebF c N (Real.cos θ) ∂arc = c 0 := by
  have := integral_chebF_mul_T c N 0
  simpa using this

/-- Termwise integration of `w · Σ a_k T_{k+1}(cos θ)` against the arcsine law. -/
theorem integral_chebF_mul_series (c : ℕ → ℝ) (N : ℕ) {a : ℕ → ℝ}
    (ha : Summable fun k => |a k|) {s : ℝ → ℝ}
    (hs : ∀ θ, HasSum (fun k : ℕ => a k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ))
      (s θ)) :
    ∫ θ, chebF c N (Real.cos θ) * s θ ∂arc = ∑ k ∈ Finset.range N, a k * c (k + 1) / 2 := by
  set W : ℝ := ∑ k ∈ Finset.range (N + 1), |c k| with hW
  set F : ℕ → ℝ → ℝ := fun k θ => chebF c N (Real.cos θ) *
    (a k * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) with hF
  have hFc : ∀ k, Continuous (F k) := fun k =>
    (continuous_chebF_cos c N).mul (continuous_const.mul ((Polynomial.continuous _).comp
      Real.continuous_cos))
  have hFb : ∀ k θ, ‖F k θ‖ ≤ W * |a k| := by
    intro k θ
    simp only [hF, Real.norm_eq_abs, abs_mul]
    have h1 := abs_chebF_le c N (cos_mem θ)
    have h2 := energy_chebyshev_abs_le_one (k + 1) (cos_mem θ)
    calc |chebF c N (Real.cos θ)| * (|a k| * |(Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)|)
        ≤ W * (|a k| * 1) := by
          gcongr
      _ = W * |a k| := by rw [mul_one]
  have hFint : ∀ k, Integrable (F k) arc := fun k =>
    Integrable.mono' (integrable_const (W * |a k|)) (hFc k).aestronglyMeasurable
      (ae_of_all _ (hFb k))
  have hFsum : Summable (fun k => ∫ θ, ‖F k θ‖ ∂arc) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun θ => norm_nonneg _)
      (fun k => ?_) (ha.mul_left W)
    calc ∫ θ, ‖F k θ‖ ∂arc ≤ ∫ _θ, W * |a k| ∂arc :=
          integral_mono (hFint k).norm (integrable_const _) (hFb k)
      _ = W * |a k| := by simp
  have htsum := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hmom : ∀ k : ℕ, ∫ θ, F k θ ∂arc =
      if k + 1 ≤ N then a k * c (k + 1) / 2 else 0 := by
    intro k
    have : ∀ θ, F k θ = a k * (chebF c N (Real.cos θ) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ)) := by
      intro θ; simp only [hF]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_chebF_mul_T]
    by_cases hk : k + 1 ≤ N
    · simp [hk]; ring
    · simp [hk]
  have hfin : HasSum (fun k => ∫ θ, F k θ ∂arc)
      (∑ k ∈ Finset.range N, a k * c (k + 1) / 2) := by
    have h1 : HasSum (fun k => ∫ θ, F k θ ∂arc) (∑ k ∈ Finset.range N, ∫ θ, F k θ ∂arc) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        simp only [Finset.mem_range, not_lt] at hk
        rw [hmom k]
        have hn : ¬ (k + 1 ≤ N) := by omega
        simp [hn])
    convert h1 using 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hy : i + 1 ≤ N := by simp at hi; omega
    rw [hmom i]
    simp [hy]
  have heq : (fun θ => ∑' k, F k θ) = fun θ => chebF c N (Real.cos θ) * s θ := by
    funext θ
    simp only [hF]
    rw [tsum_mul_left, (hs θ).tsum_eq]
  rw [← heq, ← htsum.tsum_eq, hfin.tsum_eq]



theorem integrable_chebF (c : ℕ → ℝ) (N : ℕ) :
    Integrable (fun θ => chebF c N (Real.cos θ)) arc :=
  integrable_arc_of_bound (continuous_chebF_cos c N)
    (fun θ => abs_chebF_le c N (cos_mem θ))


theorem integrable_chebF_T (c : ℕ → ℝ) (N k : ℕ) :
    Integrable (fun θ => chebF c N (Real.cos θ) * (Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ)) arc :=
  integrable_arc_of_bound (C := ∑ j ∈ Finset.range (N + 1), |c j|)
    ((continuous_chebF_cos c N).mul ((Polynomial.continuous _).comp Real.continuous_cos))
    fun θ => by
      rw [abs_mul]
      calc _ ≤ (∑ j ∈ Finset.range (N + 1), |c j|) * 1 :=
            mul_le_mul (abs_chebF_le c N (cos_mem θ)) (energy_chebyshev_abs_le_one k (cos_mem θ))
              (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        _ = _ := mul_one _

end

end CatalanCore.Zeta5.Potential
