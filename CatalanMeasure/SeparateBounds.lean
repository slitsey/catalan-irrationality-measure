module
public import CatalanMeasure.WeightedBounds
@[expose] public section
open Set Finset Real Filter Polynomial Matrix MeasureTheory
open scoped BigOperators Nat
namespace OAI.InternalCatalan
noncomputable def separateEnergyCost : ℝ := 573 / 100
theorem separate_quadratic_energy_le_linear {V U C Q t : ℝ}
    (hV : V ≤ U - 39845 / 8000000) (hC : C ≤ 739186 / 125000)
    (hQ : Q ≤ -(170907 / 100000)) (ht : 0 ≤ t) :
    V + t * C + t ^ 2 * Q ≤ U + t * (573 / 100) := by
  have htc := mul_le_mul_of_nonneg_left hC ht
  have htq := mul_le_mul_of_nonneg_left hQ (sq_nonneg t)
  nlinarith [sq_nonneg ((2 * (170907 / 100000 : ℝ)) * t - (739186 / 125000 - 573 / 100))]
theorem separate_case_one_eventually {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, p ≤ n N → ∀ x s : Fin p → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
        ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2)) →
      pinWeightedValue N 1 (((n N : ℝ) - p) / (n N : ℝ)) x s ≤
        -(229180925 / 100000000 : ℝ) + d + ((n N : ℝ) - p) / (n N : ℝ) * separateEnergyCost := by
  have hlam : 0 ≤ barrierLambda1 := barrier_lambdas.2.1
  have hp := barrier_trials_abs_summable.2.2.1
  have hv := barrier_trials_abs_summable.2.2.2
  have hKn : 1 * barrierTrialNormSq barrierP1 + barrierTrialNormSq barrierV1 / 2 ≤
      (9321 / 10000 : ℝ) := by
    linarith only [barrier_case1_norm_coarse_upper]
  obtain ⟨N₀, h₀⟩ := pin_weighted_dual_eventually (k := 1) (lam := barrierLambda1) (a := 0)
    (Bx := weightedCaseOneBx) (Bs := weightedCaseOneBs0) (Kn := 9321 / 10000)
    (Or.inl rfl) hlam le_rfl barrierP1 barrierV1 hp hv weighted_case_one_row_bound
    (by intro z hz; simpa using weighted_case_one_column0 z hz) hKn hd
  obtain ⟨N₁, h₁⟩ := pin_weighted_dual_eventually (k := 1) (lam := barrierLambda1) (a := 1)
    (Bx := weightedCaseOneBx) (Bs := weightedCaseOneBs1) (Kn := 9321 / 10000)
    (Or.inl rfl) hlam (by norm_num : (0 : ℝ) ≤ 1) barrierP1 barrierV1 hp hv weighted_case_one_row_bound
    (by intro z hz; simpa [weightedCaseOneBs1] using CatalanMeasure.WeightedCaseOne.column_bound z hz) hKn hd
  refine ⟨max (max N₀ N₁) 1, ?_⟩
  intro N hN p hpN x s hx hs hx0 hxi hsi hcase
  have hN0 : 0 < N := by omega
  have hn : (0 : ℝ) < n N := Nat.cast_pos.mpr (by unfold n; omega)
  have hpR : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hpN
  let t : ℝ := ((n N : ℝ) - p) / (n N : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hn.le
  have ht1 : t ≤ 1 := (div_le_one hn).mpr (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ (p : ℝ))])
  have hratio : (p : ℝ) / (n N : ℝ) = 1 - t := by dsimp [t]; field_simp <;> ring
  have h0 := h₀ N (by omega) p hpN x s hx hs hx0 hxi hsi (Or.inr hcase)
  have h1 := h₁ N (by omega) p hpN x s hx hs hx0 hxi hsi (Or.inr hcase)
  have hm := weighted_endpoint_mixture ht0 ht1 h0 h1
  rw [hratio] at hm
  have hlam_eq : barrierLambda1 * ((n N : ℝ) - p) / (6 * (n N : ℝ)) = barrierLambda1 * t / 6 := by
    dsimp [t]; field_simp <;> ring
  rw [hlam_eq] at hm
  have he : (1 - t) * (-(11 / 16 : ℝ) * Real.log 2 + 9321 / 10000 +
        (1 - t) * (weightedCaseOneBx + weightedCaseOneBs0) +
        (1 / 2 + 1) * (1 - (1 - t) ^ 2) * Real.log 2 + barrierLambda1 * t / 6 + d) +
      t * (-(11 / 16 : ℝ) * Real.log 2 + 9321 / 10000 +
        (1 - t) * (weightedCaseOneBx + weightedCaseOneBs1) +
        (1 / 2 + 1) * (1 - (1 - t) ^ 2) * Real.log 2 + barrierLambda1 * t / 6 + d) =
      (-(11 / 16 : ℝ) * Real.log 2 + 9321 / 10000 + weightedCaseOneBx + weightedCaseOneBs0) +
        t * (3 * Real.log 2 - (weightedCaseOneBx + weightedCaseOneBs0) +
          (weightedCaseOneBs1 - weightedCaseOneBs0) + barrierLambda1 / 6) +
        t ^ 2 * (-(3 / 2 : ℝ) * Real.log 2 - (weightedCaseOneBs1 - weightedCaseOneBs0)) + d := by ring
  rw [he] at hm
  have hV : -(11 / 16 : ℝ) * Real.log 2 + 9321 / 10000 + weightedCaseOneBx + weightedCaseOneBs0 ≤
      -(229180925 / 100000000 : ℝ) - 39845 / 8000000 := by
    unfold weightedCaseOneBx weightedCaseOneBs0
    linarith only [barrier_one_coarse_total_sharp_lt]
  have hc := separate_quadratic_energy_le_linear hV
    weighted_case_one_linear_constant weighted_case_one_quadratic_constant ht0
  change pinWeightedValue N 1 t x s ≤ -(229180925 / 100000000 : ℝ) + d + t * separateEnergyCost
  unfold separateEnergyCost
  linarith



end OAI.InternalCatalan
