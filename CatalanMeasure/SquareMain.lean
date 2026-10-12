module
public import CatalanMeasure.SeparateLemma6
public import CatalanMeasure.SquareNonvanishing
public import CatalanMeasure.SquarePNTWindow
@[expose] public section
open Real Filter Polynomial
open scoped Topology BigOperators Nat
/-! The square-denominator prime window reduces the PNT bound to 7181. -/
namespace OAI.InternalCatalan

theorem measureIntPoly_square_hypotheses {ρ η : ℝ} (hη : η < 2304 * measureGap)
    (hpert : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε))) :
    ∃ P₀ : ℕ,
      (∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
        aeval ((a : ℝ) / b) (measureIntPoly p) ≠ 0) ∧
      (∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ, |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (measureIntPoly p)| ≤ Real.exp (-(η * (p : ℝ) ^ 2))) := by
  obtain ⟨P₀, -, hsmall⟩ := measureIntPoly_hypotheses hη hpert
  refine ⟨max P₀ (fixedDeterminantPrimeCutoff + 1), ?_, ?_⟩
  · intro p hp hprime a b hb hpb
    have : Fact p.Prime := ⟨hprime⟩
    have hcut : fixedDeterminantPrimeCutoff < p := by omega
    have hp0 : 0 < p := hprime.pos
    rw [aeval_measureIntPoly hp0]
    have hx : ((a : ℝ) / b) = (((a : ℚ) / b : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    rw [hx, aeval_ratCast_eq, eval_deltaPoly]
    have hdet := determinantRat_div_ne_zero_of_not_square_dvd hcut a hb hpb
    have hfac : (((44 * p) ! : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hM : (denomBound p : ℝ) ≠ 0 := by exact_mod_cast denomBound_ne_zero p
    have hdetR : ((determinantRat ((a : ℚ) / b) p : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hdet
    exact mul_ne_zero (mul_ne_zero hfac hM) hdetR
  · intro p hp
    exact hsmall p (le_trans (le_max_left _ _) hp)

theorem catalan_irrationalityMeasure_of_perturbation_square_pnt {ρ η ε c : ℝ}
    (hρ : 0 < ρ) (hη0 : 0 < η) (hη : η < 2304 * measureGap) (hε : 0 < ε) (hc : 1 < c)
    (hpert : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((1 + ε) * ρ * max (((44 : ℕ) : ℝ) / η) (c / (2 * ε)))) <
        |catalan - a / b| := by
  obtain ⟨P₀, hnz, hsmall⟩ := measureIntPoly_square_hypotheses hη hpert
  exact CatalanMeasure.irrationality_measure_of_polynomials_square_pnt
    catalan 44 hη0 hρ hε hc measureIntPoly P₀ measureIntPoly_natDegree_le hnz hsmall

theorem square_catalan_irrationalityMeasure_pnt {η ε c : ℝ} (hη0 : 0 < η)
    (hη : η < 2304 * measureGap) (hε : 0 < ε) (hc : 1 < c) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((1 + ε) * separateRho * max (((44 : ℕ) : ℝ) / η) (c / (2 * ε)))) <
        |catalan - a / b| :=
  catalan_irrationalityMeasure_of_perturbation_square_pnt
    (by norm_num [separateRho]) hη0 hη hε hc separate_perturbation

theorem catalan_irrationalityMeasure_7181 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(7181 : ℝ)) < |catalan - a / b| := by
  have hε : (0 : ℝ) < 10001 / (2 * 191031) := by norm_num
  have hc : (1 : ℝ) < 10001 / 10000 := by norm_num
  filter_upwards [square_catalan_irrationalityMeasure_pnt measureEta_pos measureEta_lt hε hc,
    eventually_ge_atTop 1] with b hb hb1 a
  refine lt_of_le_of_lt ?_ (hb a)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1)
  have hX := measureEta_ratio_le
  have hmax : max (((44 : ℕ) : ℝ) / measureEta)
      ((10001 / 10000) / (2 * (10001 / (2 * 191031)))) = 191031 / 10000 := by
    rw [max_eq_right (by norm_num at hX ⊢; linarith)]
    norm_num
  rw [hmax]
  unfold separateRho
  norm_num

end OAI.InternalCatalan
