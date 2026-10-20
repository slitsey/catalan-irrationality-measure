module

public import CatalanLambda.Decay.ThmNAsymp
public import CatalanLambda.Decay.LambdaCatalan
public import CatalanArchive.CatalanLambda.GrowthFinal
public import CatalanArchive.CatalanLambda.Main

@[expose] public section

/-!
# Separation core: a nonvanishing `P_h(p/q)` very close to `λ` forces `θ h ≤ log q`.
-/

open Filter

namespace CatalanLambda.Measure

open CatalanLambda.Decay

lemma det_cast (h : ℕ) (r : ℚ) :
    (((r : ℝ)) • (1 : Matrix (Fin h) (Fin h) ℝ) + (CatalanLambda.M0 h).map (Rat.cast : ℚ → ℝ)).det
      = ((CatalanLambda.P h r : ℚ) : ℝ) := by
  unfold CatalanLambda.P
  have := RingHom.map_det (Rat.castHom ℝ)
    (r • (1 : Matrix (Fin h) (Fin h) ℚ) + CatalanLambda.M0 h)
  change _ = (Rat.castHom ℝ) _
  rw [this]
  congr 1
  ext a b
  by_cases hab : a = b <;> simp [hab]

/-- **Separation core.**  If `0 < θ < D_cert - 313/105`, then for all large `h`, whenever
`P_h(p/q) ≠ 0` and `|λ - p/q| ≤ exp(-c_cert h)`, we get `θ h ≤ log q`. -/
theorem sep_core {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) {θ : ℝ} (_hθ0 : 0 < θ) (hθ : θ < (F.Dcert : ℝ) - 313 / 105) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∀ p q : ℤ, 0 < q → CatalanLambda.P h ((p : ℚ) / q) ≠ 0 →
      |lamS - (p : ℝ) / q| ≤ Real.exp (-(F.ccert : ℝ) * h) → θ * h ≤ Real.log q := by
  set e : ℝ := ((F.Dcert : ℝ) - 313 / 105 - θ) / 3 with he
  have he0 : 0 < e := by rw [he]; linarith
  obtain ⟨h₂, H2⟩ := window_liminf_P F he0
  obtain ⟨h₁, H1⟩ := eventually_atTop.1 (CatalanLambda.log_Dden_le_eventually he0)
  refine ⟨max (max h₁ h₂) 1, fun h hh p q hq hP hclose => ?_⟩
  have hh1 : h₁ ≤ h := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hh
  have hh2 : h₂ ≤ h := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hh
  have hhpos : (0 : ℝ) < h := by
    have : 1 ≤ h := le_trans (le_max_right _ _) hh
    exact_mod_cast this
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- upper bound
  have hup := H2 h hh2 ((p : ℝ) / q - lamS) (by rw [abs_sub_comm]; exact hclose)
  have hrat : lamS + ((p : ℝ) / q - lamS) = (((p : ℚ) / q : ℚ) : ℝ) := by push_cast; ring
  rw [hrat, det_cast] at hup
  -- lower bound
  obtain ⟨z, hz⟩ := CatalanLambda.integrality h p q hq
  have hDpos : (0 : ℝ) < (CatalanLambda.Dden h : ℝ) := by
    exact_mod_cast CatalanLambda.Dden_pos h
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    have h1 : ((q : ℚ) ^ h * (CatalanLambda.Dden h : ℚ)) ≠ 0 := by
      have := CatalanLambda.Dden_pos h
      positivity
    have : CatalanLambda.P h ((p : ℚ) / q) = 0 := by
      rcases mul_eq_zero.1 (hz.trans (by simp)) with h2 | h2
      · exact absurd h2 h1
      · exact h2
    exact hP this
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast this
  have hzR : (q : ℝ) ^ h * (CatalanLambda.Dden h : ℝ) * (CatalanLambda.P h ((p : ℚ) / q) : ℝ)
      = z := by
    have := congrArg (Rat.cast : ℚ → ℝ) hz
    push_cast at this
    exact this
  have hA : (0 : ℝ) < (q : ℝ) ^ h * (CatalanLambda.Dden h : ℝ) := by positivity
  have h1le : (1 : ℝ) ≤ (q : ℝ) ^ h * (CatalanLambda.Dden h : ℝ) *
      Real.exp (-((F.Dcert : ℝ) - e) * (h : ℝ) ^ 2) := by
    calc (1 : ℝ) ≤ |(z : ℝ)| := hz1
      _ = (q : ℝ) ^ h * (CatalanLambda.Dden h : ℝ) * |(CatalanLambda.P h ((p : ℚ) / q) : ℝ)| := by
          rw [← hzR, abs_mul, abs_of_pos hA]
      _ ≤ _ := by gcongr
  have hlog := Real.log_le_log one_pos h1le
  rw [Real.log_one, Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_mul (by positivity) hDpos.ne',
    Real.log_pow, Real.log_exp] at hlog
  have hD := H1 h hh1
  have hmain : (θ + e) * (h : ℝ) ^ 2 ≤ (h : ℝ) * Real.log q := by
    have : e = ((F.Dcert : ℝ) - 313 / 105 - θ) / 3 := he
    nlinarith
  have hfin : (θ + e) * (h : ℝ) ≤ Real.log q := by
    by_contra hcon
    push Not at hcon
    nlinarith
  nlinarith

end CatalanLambda.Measure
