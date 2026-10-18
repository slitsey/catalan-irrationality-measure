module

public import CatalanLambda.Decay.ThmNPoint

@[expose] public section

/-!
# Mirror constant: the unscaled energy bound with points at distance `1/4` from the origin side

Same as `energy_A0`, with the hypothesis `3/8 ≤ -Re z` replaced by `1/4 ≤ -Re z` (the nearest atom
of the mirror is `-1/4`) and the loss `log(1 + 8h/3)` replaced by `log(1 + 4h)`.
-/

open Finset

namespace CatalanLambda.Mirror

open CatalanLambda.Decay

theorem energy_A0B {h k K : ℕ} (hh : 0 < h) {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (m : Fin K → ℝ)
    (hm : ∑ i, m i = 1) (s : Fin k → Fin h) (hs : Function.Injective s)
    (z : Fin k → ℂ) (hzi : Function.Injective z) (hz : ∀ l, 1 / 4 ≤ -(z l).re) :
    2 * h * (∑ l, (Usig ρ c m (z l / h) - Utau (z l / h))
        + ∑ b, rmask s b * (Usig ρ c m (nodeC h b) - Utau (nodeC h b)))
      - (h : ℝ) ^ 2 * Irho ρ c m + h * Real.log ρ + (3 / 2) * (h : ℝ) ^ 2 - 2 * h * Real.log h
      - 3 * h - 1 / 2 - 2 * k * Real.log (1 + 4 * h) + 2 * k * Real.log h
    ≤ -Real.log (‖cexpr z (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set σ : Fin k → ℂ := fun l => z l / h with hσ
  set τ : Fin h → ℂ := fun b => nodeC h b with hτ
  set r : Fin h → ℝ := rmask s with hr
  have hzσ : ∀ l, z l = (h : ℂ) * σ l := fun l => by simp only [hσ]; field_simp
  have hσre : ∀ l, (σ l).re = (z l).re / h := fun l => by
    simp only [hσ, Complex.div_natCast_re]
  have hσneg : ∀ l, 1 / (4 * h) ≤ -(σ l).re := fun l => by
    rw [hσre, neg_div', div_le_div_iff₀ (by positivity) hh']
    have := hz l
    nlinarith
  have hσneg' : ∀ l, (σ l).re < 0 := fun l => by
    have := hσneg l
    have : 0 < 1 / (4 * (h : ℝ)) := by positivity
    linarith
  have hσi : Function.Injective σ := by
    intro a b hab
    apply hzi
    rw [hzσ a, hzσ b, hab]
  have hτi : Function.Injective τ := nodeC_inj hh
  have hστ : ∀ l b, σ l ≠ τ b := by
    intro l b e
    have := congrArg Complex.re e
    have h1 := hσneg' l
    have h2 := nodeC_re_nonneg h b
    simp only [hτ] at this
    linarith
  have hpi : Function.Injective (Sum.elim σ τ) := by
    intro x y hxy
    rcases x with l | b <;> rcases y with l' | b'
    · simp only [Sum.elim_inl] at hxy; rw [hσi hxy]
    · simp only [Sum.elim_inl, Sum.elim_inr] at hxy; exact absurd hxy (hστ _ _)
    · simp only [Sum.elim_inl, Sum.elim_inr] at hxy; exact absurd hxy.symm (hστ _ _)
    · simp only [Sum.elim_inr] at hxy; rw [hτi hxy]
  have hrs : ∑ b, r b = (h : ℝ) - k := by
    have := sum_mask s hs (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_sub_distrib] at this
    simp only [hr]
    linarith
  have hB := energy_B hh hρ c m hm σ τ r (rmask_cases s) hrs hpi
  -- unscaled energy
  have hy : Function.Injective (fun i => (((s i : Fin h) : ℕ) : ℂ)) := by
    intro a b hab
    have hab' : (((s a : Fin h) : ℕ) : ℂ) = (((s b : Fin h) : ℕ) : ℂ) := hab
    have : ((s a : Fin h) : ℕ) = ((s b : Fin h) : ℕ) := by exact_mod_cast hab'
    exact hs (Fin.ext this)
  have hzy : ∀ l i, z l ≠ (((s i : Fin h) : ℕ) : ℂ) := by
    intro l i e
    have := congrArg Complex.re e
    have h1 := hz l
    simp only [Complex.natCast_re] at this
    have : (0 : ℝ) ≤ (((s i : Fin h) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hU := neg_log_cexpr_sq z (fun i => (((s i : Fin h) : ℕ) : ℂ)) hzi hy hzy
  -- scaling of the three sums
  have hnode : ∀ i, (((s i : Fin h) : ℕ) : ℂ) = (h : ℂ) * τ (s i) := fun i =>
    nat_eq_h_mul_nodeC hh _
  have hlogh : (0 : ℝ) < h := hh'
  have S1 : ∑ l, ∑ l', elog (z l) (z l')
      = ∑ l, ∑ l', elog (σ l) (σ l') - k * (k - 1) * Real.log h := by
    have : ∀ l l', elog (z l) (z l') = elog (σ l) (σ l') - (if l = l' then 0 else Real.log h) := by
      intro l l'
      rw [hzσ l, hzσ l']
      have := elog_scale (c := h) hh' (σ l) (σ l')
      simp only [Complex.ofReal_natCast] at this
      rw [this]
      congr 2
      simp only [hσi.eq_iff]
    simp_rw [this, Finset.sum_sub_distrib]
    rw [sum_offdiag_const]
  have S2 : ∑ i, ∑ i', elog (((s i : Fin h) : ℕ) : ℂ) (((s i' : Fin h) : ℕ) : ℂ)
      = ∑ i, ∑ i', elog (τ (s i)) (τ (s i')) - k * (k - 1) * Real.log h := by
    have : ∀ i i', elog (((s i : Fin h) : ℕ) : ℂ) (((s i' : Fin h) : ℕ) : ℂ)
        = elog (τ (s i)) (τ (s i')) - (if i = i' then 0 else Real.log h) := by
      intro i i'
      rw [hnode i, hnode i']
      have := elog_scale (c := h) hh' (τ (s i)) (τ (s i'))
      simp only [Complex.ofReal_natCast] at this
      rw [this]
      have hiff : τ (s i) = τ (s i') ↔ i = i' := ⟨fun e => hs (hτi e), fun e => by rw [e]⟩
      simp only [hiff]
    simp_rw [this, Finset.sum_sub_distrib]
    rw [sum_offdiag_const]
  have S3 : ∑ l, ∑ i, elog (z l) (((s i : Fin h) : ℕ) : ℂ)
      = ∑ l, ∑ i, elog (σ l) (τ (s i)) - k * k * Real.log h := by
    have : ∀ l i, elog (z l) (((s i : Fin h) : ℕ) : ℂ) = elog (σ l) (τ (s i)) - Real.log h := by
      intro l i
      rw [hzσ l, hnode i]
      have := elog_scale (c := h) hh' (σ l) (τ (s i))
      simp only [Complex.ofReal_natCast] at this
      rw [this, if_neg (hστ _ _)]
    simp_rw [this, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hD := Hsc_decomp σ τ s hs
  -- the three bounds
  have bFN : ∑ l, ∑ b, elog (σ l) (τ b) ≤ h * ∑ l, Utau (σ l) + k * Real.log (1 + 4 * h) := by
    have : ∀ l, ∑ b, elog (σ l) (τ b) ≤ h * Utau (σ l) + Real.log (1 + 4 * h) := by
      intro l
      have h1 := riemann_node_sum hh (hσneg' l)
      have h2 : ∑ b : Fin h, elog (σ l) (τ b) = ∑ b ∈ Finset.range h, elog (σ l) (nodeC h b) :=
        fin_sum_range (fun b => elog (σ l) (nodeC h b))
      have h3 : Real.log (1 + 1 / ‖σ l‖) ≤ Real.log (1 + 4 * h) := by
        have hn : 1 / (4 * (h : ℝ)) ≤ ‖σ l‖ := by
          calc 1 / (4 * (h : ℝ)) ≤ -(σ l).re := hσneg l
            _ ≤ |(σ l).re| := neg_le_abs _
            _ ≤ ‖σ l‖ := Complex.abs_re_le_norm _
        have hpos : 0 < ‖σ l‖ := lt_of_lt_of_le (by positivity) hn
        apply Real.log_le_log (by positivity)
        have : 1 / ‖σ l‖ ≤ 4 * h := by
          rw [div_le_iff₀ hpos]
          have := mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 4 * h by positivity)
          have e : 4 * (h : ℝ) * (1 / (4 * h)) = 1 := by field_simp
          nlinarith
        linarith
      linarith
    calc ∑ l, ∑ b, elog (σ l) (τ b) ≤ ∑ l, (h * Utau (σ l) + Real.log (1 + 4 * h)) :=
          Finset.sum_le_sum (fun l _ => this l)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]; simp
  have bRN : ∑ b, ∑ b', r b * elog (τ b) (τ b') ≤ h * ∑ b, r b * Utau (τ b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [← Finset.mul_sum]
    have h1 : ∑ b' : Fin h, elog (τ b) (τ b') ≤ h * Utau (τ b) := by
      have := node_sum_le hh b b.2
      rw [fin_sum_range (fun b' => elog (nodeC h b) (nodeC h b'))]
      exact this
    have h0 : 0 ≤ r b := by rcases rmask_cases s b with e | e <;> rw [hr, e] <;> norm_num
    nlinarith
  have bNN := NN_ge hh
  have eNN : ∑ b : Fin h, ∑ b' : Fin h, elog (τ b) (τ b')
      = ∑ a ∈ Finset.range h, ∑ b ∈ Finset.range h, elog (nodeC h a) (nodeC h b) := by
    calc _ = ∑ a : Fin h, ∑ b ∈ Finset.range h, elog (nodeC h a) (nodeC h b) :=
          Finset.sum_congr rfl (fun a _ => fin_sum_range (fun b => elog (nodeC h a) (nodeC h b)))
      _ = _ := fin_sum_range (fun a => ∑ b ∈ Finset.range h, elog (nodeC h a) (nodeC h b))
  have e1 : ∑ l, (Usig ρ c m (z l / h) - Utau (z l / h))
      = ∑ l, Usig ρ c m (σ l) - ∑ l, Utau (σ l) := Finset.sum_sub_distrib _ _
  have e2 : ∑ b, r b * (Usig ρ c m (nodeC h b) - Utau (nodeC h b))
      = ∑ b, r b * Usig ρ c m (τ b) - ∑ b, r b * Utau (τ b) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => by simp only [hτ]; ring)
  rw [e1, e2]
  rw [← hr, eNN] at hD
  nlinarith [hU, S1, S2, S3, hD, hB, bFN, bRN, bNN]

end CatalanLambda.Mirror
