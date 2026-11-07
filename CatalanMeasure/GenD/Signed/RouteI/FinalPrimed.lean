module
public import CatalanMeasure.GenD.Final
public import CatalanMeasure.GenD.Signed.DesignConst

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD
open Filter Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

/-! The built final assembly, with only the primed payment criterion changed. -/
structure DesignData' (P : Parameters) where
  /-- Target exponent `μ`, a rational number. -/
  μ : ℚ
  Z : Normalizer P
  w : ℝ
  ρ : ℝ
  η : ℝ
  κ : ℝ
  δ : ℝ
  pay : PayW' w ((P.n0 - P.g0 : ℕ) : ℝ) ρ η κ δ (μ : ℝ)
  /-- Growth of the denominator: `log D_N ≤ (gD + ε) N²`. -/
  gD : ℝ
  D_growth : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Real.log (Z.D N) ≤ (gD + ε) * (N : ℝ) ^ 2
  /-- Smallness of `Δ_N` near Catalan's constant (the certificate layer). -/
  tΔ : ℝ
  delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
    |x - catalan| ≤ Real.exp (-(ρ * (N : ℝ))) →
      |aeval x (Parametric.deltaPoly P N)| ≤ Real.exp (-((tΔ - ε) * (N : ℝ) ^ 2))
  /-- The payments leave room for the denominator growth. -/
  eta_le : η < tΔ - gD
  /-- Arithmetic nonvanishing at `a / b` for `p ∤ b` (base-matrix certificate). -/
  nonvanishing : ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
    aeval ((a : ℝ) / b) (Parametric.deltaPoly P p) ≠ 0

/-- **The design-generic measure theorem.** -/
theorem measure_of_design' (P : Parameters) (D : DesignData' P) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(D.μ : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨hB, hη, hρ, hw0, hκ, hδ, hδ3, hcross, hwin, hlin, hpay⟩ := D.pay
  have hadm := D.Z.adm
  have hd0 : 0 < P.n0 - P.g0 := by have := hadm.2.2.2.2; omega
  -- smallness of `Q_N`
  set e : ℝ := (D.tΔ - D.gD - D.η) / 4 with he
  have hepos : 0 < e := by have := D.eta_le; rw [he]; linarith
  have hsm : ∀ᶠ N : ℕ in atTop, D.Z.N0 ≤ N ∧ ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(D.ρ * (N : ℝ))) →
        |aeval x (D.Z.Q N)| ≤ Real.exp (-(D.η * (N : ℝ) ^ 2)) := by
    filter_upwards [factorial_mul_le_exp (P.n0 - P.g0) hd0 hepos, D.D_growth e hepos,
      D.delta_small e hepos, eventually_ge_atTop D.Z.N0] with N hfac hD hΔ hN0
    refine ⟨hN0, fun x hx => ?_⟩
    rw [D.Z.aeval_Q hN0, abs_mul, abs_mul]
    have hf0 : (0 : ℝ) ≤ ((Nat.factorial (P.n N - P.g N) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hD0 : (0 : ℝ) < (D.Z.D N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (D.Z.D_ne N)
    rw [abs_of_nonneg hf0, abs_of_pos hD0]
    have hnm : P.n N - P.g N = (P.n0 - P.g0) * N := by
      simp only [Parameters.n, Parameters.g]; rw [Nat.sub_mul]
    rw [hnm]
    have hDle : (D.Z.D N : ℝ) ≤ Real.exp ((D.gD + e) * (N : ℝ) ^ 2) := by
      rw [← Real.exp_log hD0]; exact Real.exp_le_exp.mpr hD
    calc (((Nat.factorial ((P.n0 - P.g0) * N) : ℕ)) : ℝ) * (D.Z.D N : ℝ) * |aeval x (Parametric.deltaPoly P N)|
        ≤ Real.exp (e * (N : ℝ) ^ 2) * Real.exp ((D.gD + e) * (N : ℝ) ^ 2) *
            Real.exp (-((D.tΔ - e) * (N : ℝ) ^ 2)) := by
          gcongr
          exact hΔ x hx
      _ = Real.exp (-(D.η * (N : ℝ) ^ 2) - e * (N : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1
          have h4 : D.tΔ = 4 * e + D.gD + D.η := by rw [he]; ring
          rw [h4]; ring
      _ ≤ Real.exp (-(D.η * (N : ℝ) ^ 2)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hepos.le (sq_nonneg (N : ℝ))])
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hsm
  obtain ⟨N1, hN1⟩ := D.nonvanishing
  have key := irrationality_measure_of_recycled_polynomials_window' catalan (P.n0 - P.g0)
    (η := D.η) (ρ := D.ρ) (κ := D.κ) (δ := D.δ) (w := D.w) hη hρ hw0 hκ hδ hδ3 hcross hwin hlin
    (by exact_mod_cast hpay) D.Z.Q (max N1 N2)
    (fun p => by
      refine (D.Z.Q_natDegree_le p).trans (le_of_eq ?_)
      simp only [Parameters.n, Parameters.g]; rw [Nat.sub_mul])
    (fun p hp hprime a b hb hpb => by
      have hN0 : D.Z.N0 ≤ p := (hN2 p ((le_max_right _ _).trans hp)).1
      rw [D.Z.aeval_Q hN0]
      have hΔ := hN1 p ((le_max_left _ _).trans hp) hprime a b hb hpb
      have hf : ((Nat.factorial (P.n p - P.g p) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      have hD : (D.Z.D p : ℝ) ≠ 0 := by exact_mod_cast D.Z.D_ne p
      exact mul_ne_zero (mul_ne_zero hf hD) hΔ)
    (fun p hp hprime q hq hpq hq2p i _ => by
      have : Fact q.Prime := ⟨hq⟩
      have hN0 : D.Z.N0 ≤ p := (hN2 p ((le_max_right _ _).trans hp)).1
      exact D.Z.Q_coeff_prime_pow_dvd hN0 hpq hq2p i)
    (fun p hp hprime x hx => (hN2 p ((le_max_right _ _).trans hp)).2 x hx)
  rwa [hB] at key

end


end CatalanMeasure.GenD

namespace CatalanMeasure.GenD.Signed.Generic
open CatalanMeasure.GenD Filter OAI.InternalCatalan
noncomputable section

theorem catalan_irrationalityMeasure_of_design' (dc : DesignConst)
    (D : DesignData' dc.toParameters) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(D.μ : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2*j+1 : ℕ) : ℝ)^2) - a/b| := by
  simpa [catalan] using measure_of_design' dc.toParameters D

end
end CatalanMeasure.GenD.Signed.Generic

#print axioms CatalanMeasure.GenD.measure_of_design'
#print axioms CatalanMeasure.GenD.Signed.Generic.catalan_irrationalityMeasure_of_design'
