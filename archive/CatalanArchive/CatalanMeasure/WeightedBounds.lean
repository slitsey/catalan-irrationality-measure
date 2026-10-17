module

public import CatalanMeasure.DualTwo
public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Sup
public import CatalanArchive.CatalanMeasure.WeightedCaseOne
public import CatalanMeasure.WeightedEnergy

@[expose] public section

open Set Real CatalanMeasure.Cert
open scoped BigOperators

namespace OAI.InternalCatalan

noncomputable def weightedP2 : ℕ → ℝ := trialSeq CatalanMeasure.WeightedDualTwo.Pc CatalanMeasure.WeightedDualTwo.P
noncomputable def weightedV2 : ℕ → ℝ := trialSeq CatalanMeasure.WeightedDualTwo.Vc CatalanMeasure.WeightedDualTwo.V
noncomputable def weightedBx2 : ℝ := -9498627 / 10000000
noncomputable def weightedBs2 : ℝ := -12145624 / 10000000
noncomputable def weightedNorm0 : ℝ := 2 * (33361987 / 500000000) + (1292855037 / 1000000000) / 2
noncomputable def weightedNorm1 : ℝ := 2 * (713397 / 10000000) + (13114478 / 10000000) / 2
noncomputable def weightedEnergyCost : ℝ := 5817 / 1000

theorem weightedP2_summable : Summable (fun j => |weightedP2 j|) :=
  (trialSeq_summable (by decide +kernel)).1

theorem weightedV2_summable : Summable (fun j => |weightedV2 j|) :=
  (trialSeq_summable (by decide +kernel)).1

theorem weighted_row_bound : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 →
    realEnergyRowTrialField 2 0 weightedP2 weightedV2 z ≤ weightedBx2 := by
  intro z hz hz0
  have h := CatalanMeasure.WeightedDualTwo.row_sup z (by
    rcases lt_or_gt_of_ne hz0 with h | h
    · exact Or.inl ⟨hz.1, h⟩
    · exact Or.inr ⟨h, hz.2⟩)
  rw [CatalanMeasure.WeightedDualTwo.MX_eq] at h
  exact h

theorem weighted_col_bound : ∀ z ∈ Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField weightedV2 z + Real.log (1 + z) ≤ weightedBs2 := by
  intro z hz
  have h := CatalanMeasure.WeightedDualTwo.col_sup z hz
  rw [CatalanMeasure.WeightedDualTwo.MY_eq] at h
  have hval : (-1518203 / 1250000 : ℝ) = weightedBs2 := by norm_num [weightedBs2]
  rw [hval] at h
  exact h

theorem weighted_norm0_bound : 2 * barrierTrialNormSq dualP2 + barrierTrialNormSq dualV2 / 2 ≤ weightedNorm0 := by
  have hp := CatalanMeasure.Dual.normP_le
  have hv := CatalanMeasure.Dual.normV_le
  rw [CatalanMeasure.Dual.NP_eq] at hp
  rw [CatalanMeasure.Dual.NV_eq] at hv
  unfold dualP2 dualV2 weightedNorm0
  linarith

theorem weighted_norm1_bound : 2 * barrierTrialNormSq weightedP2 + barrierTrialNormSq weightedV2 / 2 ≤ weightedNorm1 := by
  have hp := CatalanMeasure.WeightedDualTwo.normP_le
  have hv := CatalanMeasure.WeightedDualTwo.normV_le
  rw [CatalanMeasure.WeightedDualTwo.NP_eq] at hp
  rw [CatalanMeasure.WeightedDualTwo.NV_eq] at hv
  unfold weightedP2 weightedV2 weightedNorm1
  linarith

theorem weighted_case_two_linear_constant :
    weightedNorm1 - weightedNorm0 + weightedBx2 + weightedBs2 - 2 * (dualBx + dualBs) +
      4 * Real.log 2 ≤ weightedEnergyCost := by
  have hlog := Real.log_two_lt_d9
  unfold weightedNorm1 weightedNorm0 weightedBx2 weightedBs2 dualBx dualBs weightedEnergyCost
  norm_num at hlog ⊢
  linarith

theorem weighted_case_two_quadratic_constant :
    dualBx + dualBs - (weightedBx2 + weightedBs2) - 2 * Real.log 2 ≤ 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold dualBx dualBs weightedBx2 weightedBs2
  norm_num
  linarith

theorem weighted_case_two_eventually {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, p ≤ n N → ∀ x s : Fin p → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      pinWeightedValue N 2 (((n N : ℝ) - p) / (n N : ℝ)) x s ≤
        -(229180925 / 100000000 : ℝ) + d + ((n N : ℝ) - p) / (n N : ℝ) * weightedEnergyCost := by
  obtain ⟨N₀, h₀⟩ := pin_weighted_dual_eventually (k := 2) (lam := 0) (a := 0)
    (Bx := dualBx) (Bs := dualBs) (Kn := weightedNorm0) (Or.inr rfl) le_rfl le_rfl
    dualP2 dualV2 dualP2_summable dualV2_summable dual_row_bound
    (by intro z hz; simpa using dual_col_bound z hz) weighted_norm0_bound hd
  obtain ⟨N₁, h₁⟩ := pin_weighted_dual_eventually (k := 2) (lam := 0) (a := 1)
    (Bx := weightedBx2) (Bs := weightedBs2) (Kn := weightedNorm1) (Or.inr rfl) le_rfl (by norm_num)
    weightedP2 weightedV2 weightedP2_summable weightedV2_summable weighted_row_bound
    (by intro z hz; simpa using weighted_col_bound z hz) weighted_norm1_bound hd
  refine ⟨max (max N₀ N₁) 1, ?_⟩
  intro N hN p hp x s hx hs hx0 hxi hsi
  have hN0 : 0 < N := by omega
  have hn : (0 : ℝ) < n N := Nat.cast_pos.mpr (by unfold n; omega)
  have hpR : (p : ℝ) ≤ (n N : ℝ) := by exact_mod_cast hp
  let t : ℝ := ((n N : ℝ) - p) / (n N : ℝ)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hn.le
  have ht1 : t ≤ 1 := (div_le_one hn).mpr (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ (p : ℝ))])
  have hratio : (p : ℝ) / (n N : ℝ) = 1 - t := by dsimp [t]; field_simp <;> ring
  have h0 := h₀ N (by omega) p hp x s hx hs hx0 hxi hsi (Or.inl rfl)
  have h1 := h₁ N (by omega) p hp x s hx hs hx0 hxi hsi (Or.inl rfl)
  have hm := weighted_endpoint_mixture ht0 ht1 h0 h1
  rw [hratio] at hm
  have he : (1 - t) * (-(11 / 16 : ℝ) * Real.log 2 + weightedNorm0 +
        (1 - t) * (dualBx + dualBs) + (2 / 2 + 1) * (1 - (1 - t) ^ 2) * Real.log 2 +
        0 * ((n N : ℝ) - p) / (6 * (n N : ℝ)) + d) +
      t * (-(11 / 16 : ℝ) * Real.log 2 + weightedNorm1 +
        (1 - t) * (weightedBx2 + weightedBs2) + (2 / 2 + 1) * (1 - (1 - t) ^ 2) * Real.log 2 +
        0 * ((n N : ℝ) - p) / (6 * (n N : ℝ)) + d) =
      (-(11 / 16 : ℝ) * Real.log 2 + weightedNorm0 + dualBx + dualBs) +
        t * (weightedNorm1 - weightedNorm0 + weightedBx2 + weightedBs2 -
          2 * (dualBx + dualBs) + 4 * Real.log 2) +
        t ^ 2 * (dualBx + dualBs - (weightedBx2 + weightedBs2) - 2 * Real.log 2) + d := by ring
  rw [he] at hm
  have hV : -(11 / 16 : ℝ) * Real.log 2 + weightedNorm0 + dualBx + dualBs ≤
      -(229180925 / 100000000 : ℝ) := by
    unfold weightedNorm0
    linarith only [dual_total_lt.le]
  have hc := CatalanMeasure.quadratic_energy_le_linear hV
    weighted_case_two_linear_constant weighted_case_two_quadratic_constant ht0
  change pinWeightedValue N 2 t x s ≤ -(229180925 / 100000000 : ℝ) + d + t * weightedEnergyCost
  unfold weightedEnergyCost
  linarith

noncomputable def weightedCaseOneBx : ℝ := -13244 / 10000 + 24 / 1000000
noncomputable def weightedCaseOneBs0 : ℝ := -14280 / 10000 + 24 / 1000000
noncomputable def weightedCaseOneBs1 : ℝ := -7586255 / 10000000

theorem weighted_case_one_row_bound : ∀ z ∈ Ico (-1 : ℝ) 1, z ≠ 0 →
    realEnergyRowTrialField 1 barrierLambda1 barrierP1 barrierV1 z ≤ weightedCaseOneBx := by
  intro z hz hz0
  simpa [realEnergyRowTrialField, barrierCase1X, weightedCaseOneBx] using
    barrierCase1X_global_upper ⟨hz.1, hz.2, hz0⟩

theorem weighted_case_one_column0 : ∀ z ∈ Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField barrierV1 z ≤ weightedCaseOneBs0 := by
  intro z hz
  simpa only [realEnergyColumnTrialField, barrierCase1Y, weightedCaseOneBs0] using
    barrierCase1Y_global_upper hz

theorem weighted_case_one_linear_constant :
    3 * Real.log 2 - (weightedCaseOneBx + weightedCaseOneBs0) +
      (weightedCaseOneBs1 - weightedCaseOneBs0) + barrierLambda1 / 6 ≤ 739186 / 125000 := by
  have hlog := Real.log_two_lt_d9
  unfold weightedCaseOneBx weightedCaseOneBs0 weightedCaseOneBs1 barrierLambda1
  norm_num at hlog ⊢
  linarith

theorem weighted_case_one_quadratic_constant :
    -(3 / 2 : ℝ) * Real.log 2 - (weightedCaseOneBs1 - weightedCaseOneBs0) ≤ -(170907 / 100000) := by
  have hlog := Real.log_two_gt_d9
  unfold weightedCaseOneBs0 weightedCaseOneBs1
  norm_num at hlog ⊢
  linarith

theorem weighted_case_one_eventually {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ p : ℕ, p ≤ n N → ∀ x s : Fin p → ℝ,
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      (((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
        ∑ i : Fin p, (1 - x i ^ 2) / (1 + x i ^ 2)) →
      pinWeightedValue N 1 (((n N : ℝ) - p) / (n N : ℝ)) x s ≤
        -(229180925 / 100000000 : ℝ) + d + ((n N : ℝ) - p) / (n N : ℝ) * weightedEnergyCost := by
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
  have hc := CatalanMeasure.case_one_quadratic_energy_le_linear hV
    weighted_case_one_linear_constant weighted_case_one_quadratic_constant ht0
  change pinWeightedValue N 1 t x s ≤ -(229180925 / 100000000 : ℝ) + d + t * weightedEnergyCost
  unfold weightedEnergyCost
  linarith

end OAI.InternalCatalan
