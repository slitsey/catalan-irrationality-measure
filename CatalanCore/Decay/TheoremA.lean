module

public import CatalanCore.Decay.ComplexContour
public import CatalanCore.Zeta5.Energy.Stirling

@[expose] public section

/-!
# The abstract assembly of Theorem A (Lai decay, LD09)

Generic in the weight space `(X, m)`, the weight `w`, the point map `z` and the dual measure `σ`
(`BallMaj`, mass `Cm`).  From the Heine bound (`heine_complex_bound`) and a bound of the weight
integral `∫ ‖w‖ exp(2n · potC σ (z/n)) dm ≤ exp (n ℓ + L log n + c₀)` (Lemma W and `W_σ ≤ ℓ`
supply it), the Hankel determinant of order `M = n · Cm` satisfies

`‖det‖ / ∏_{i<M} (i!)² ≤ exp (n² (κ(Cm) - energyC σ + Cm ℓ) + R n)`,  `κ(Cm) = Cm² (3/2 - log Cm)`,
`R n = Cm (3 + L) n log n + (2 Cm log Cm + Cm c₀) n + 2 Cm A`  (`theoremA_abstract`).

Here `-energyC σ = I(σ)` is the paper's energy, so the exponent is the paper's `-D n²` with
`D = -κ - I(σ) - Cm ℓ`.
-/

open MeasureTheory Set Real Filter Topology Finset CatalanCore.Decay.ComplexEnergy
  CatalanCore.Decay.ComplexContour

namespace CatalanCore.Decay.TheoremA

/-- An antiderivative of `x log x`. -/
noncomputable def Gx (x : ℝ) : ℝ := x ^ 2 / 2 * Real.log x - x ^ 2 / 4

lemma hasDerivAt_Gx {x : ℝ} (hx : 0 < x) : HasDerivAt Gx (x * Real.log x) x := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * x / 2) x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h4 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (2 * x / 4) x := by
    simpa using (hasDerivAt_pow 2 x).div_const 4
  have key : HasDerivAt (fun x : ℝ => x ^ 2 / 2 * Real.log x - x ^ 2 / 4)
      (2 * x / 2 * Real.log x + x ^ 2 / 2 * x⁻¹ - 2 * x / 4) x :=
    (h3.mul (Real.hasDerivAt_log hx.ne')).sub h4
  have hx0 : x ≠ 0 := hx.ne'
  have e : 2 * x / 2 * Real.log x + x ^ 2 / 2 * x⁻¹ - 2 * x / 4 = x * Real.log x := by
    field_simp; ring
  rw [e] at key
  exact key

lemma integral_x_log' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, x * Real.log x = Gx b - Gx a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_Gx ?_) ?_
  · rw [Set.uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_id.mul (ContinuousOn.log continuousOn_id ?_)
    intro x hx
    exact (lt_of_lt_of_le ha hx.1).ne'

lemma monotoneOn_x_log' : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  exact mul_le_mul hxy (Real.log_le_log (by linarith) hxy) hlog (by linarith)

lemma sum_range_cast' (m : ℕ) : ∑ k ∈ range m, (k : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `∑_{i<M} log i! ≥ ½ M² log M - ¾ M² - M log M` for `M ≥ 2`. -/
theorem sum_log_factorial_ge {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) ^ 2 / 2 * Real.log M - 3 / 4 * (M : ℝ) ^ 2 - M * Real.log M ≤
      ∑ i ∈ range M, Real.log (i.factorial) := by
  -- step 1: `log i! ≥ i log i - i`
  have hstep1 : ∑ i ∈ range M, ((i : ℝ) * Real.log i - i) ≤ ∑ i ∈ range M, Real.log (i.factorial) :=
    Finset.sum_le_sum fun i _ => CatalanCore.Zeta5.Energy.log_factorial_ge i
  have hsplit : ∑ i ∈ range M, ((i : ℝ) * Real.log i - i) =
      ∑ i ∈ range M, ((i : ℝ) * Real.log i) - (M : ℝ) * ((M : ℝ) - 1) / 2 := by
    rw [Finset.sum_sub_distrib, sum_range_cast']
  -- step 2: sum versus integral for `i log i` (monotone on `[1, ∞)`)
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Icc 1 (1 + ((M - 2 : ℕ) : ℝ))) :=
    monotoneOn_x_log'.mono fun x hx => hx.1
  have hcmp := hmono.integral_le_sum
  have hcast : (1 : ℝ) + ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast, integral_x_log' one_pos (by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith)] at hcmp
  have hsum : ∑ i ∈ range M, ((i : ℝ) * Real.log i) =
      ∑ i ∈ range (M - 2), (1 + ((i + 1 : ℕ) : ℝ)) * Real.log (1 + ((i + 1 : ℕ) : ℝ)) := by
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, Real.log_one,
      mul_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [hsum] at hsplit
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hG1 : Gx 1 = -1 / 4 := by unfold Gx; norm_num
  have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hlogratio : Real.log ((M : ℝ) - 1) ≥ Real.log M - 1 / ((M : ℝ) - 1) := by
    have h1 : Real.log ((M : ℝ) - 1) = Real.log M + Real.log (((M : ℝ) - 1) / M) := by
      rw [← Real.log_mul hMpos.ne' (div_pos hM1 hMpos).ne']
      congr 1; field_simp
    have h2 : Real.log (((M : ℝ) - 1) / M) = - Real.log ((M : ℝ) / (M - 1)) := by
      rw [← Real.log_inv]; congr 1; rw [inv_div]
    have h3 : Real.log ((M : ℝ) / (M - 1)) ≤ (M : ℝ) / (M - 1) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hMpos hM1)
    have h4 : (M : ℝ) / (M - 1) - 1 = 1 / ((M : ℝ) - 1) := by
      have : (M : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    linarith
  have hGM : Gx ((M : ℝ) - 1) ≥ (M : ℝ) ^ 2 / 2 * Real.log M - M * Real.log M -
      ((M : ℝ) - 1) / 2 - ((M : ℝ) - 1) ^ 2 / 4 := by
    unfold Gx
    have hpos : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have e2 : ((M : ℝ) - 1) ^ 2 * (1 / ((M : ℝ) - 1)) = (M : ℝ) - 1 := by
      field_simp
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlogratio.le (sq_nonneg ((M : ℝ) - 1))]
  have hf1 : (0 : ℝ) ≤ 1 * Real.log 1 := by simp
  nlinarith [hstep1, hsplit, hcmp, hGM, hG1]

/-- **Theorem A, abstract assembly** (LD09).  See the module docstring. -/
theorem theoremA_abstract {X : Type*} [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    {σ : Measure ℂ} [IsFiniteMeasure σ] {b A : ℝ} (hσ : BallMaj σ b A)
    (w z : X → ℂ) {Cm : ℝ} (hCm : σ.real univ = Cm) (hCm0 : 0 < Cm)
    {n : ℕ} (hn : 2 ≤ n) {M : ℕ} (hM : (M : ℝ) = n * Cm) (hM2 : 2 ≤ M)
    (hint : ∀ i j : Fin M, Integrable (fun x => w x * z x ^ (i : ℕ) * z x ^ (j : ℕ)) m)
    (hG : Integrable (fun x => ‖w x‖ * Real.exp (2 * n * potC σ (z x / n))) m)
    {ℓ L c₀ : ℝ}
    (hW : ∫ x, ‖w x‖ * Real.exp (2 * n * potC σ (z x / n)) ∂m ≤
      Real.exp (n * ℓ + L * Real.log n + c₀)) :
    ‖(Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ ((i : ℕ) + (j : ℕ)) ∂m).det‖ /
        ∏ i ∈ range M, ((i.factorial : ℝ)) ^ 2 ≤
      Real.exp ((n : ℝ) ^ 2 * (Cm ^ 2 * (3 / 2 - Real.log Cm) - energyC σ + Cm * ℓ) +
        (Cm * (3 + L) * n * Real.log n + (2 * Cm * Real.log Cm + Cm * c₀) * n + 2 * Cm * A)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hMs : (M : ℝ) = n * σ.real univ := by rw [hCm]; exact hM
  have hε : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
  have hheine := heine_complex_bound m hσ w z hn0 hMs hε hint hG
  set Gint : ℝ := ∫ x, ‖w x‖ * Real.exp (2 * n * potC σ (z x / n)) ∂m with hGint
  have hG0 : 0 ≤ Gint := integral_nonneg fun x => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hGM : Gint ^ M ≤ Real.exp (n * ℓ + L * Real.log n + c₀) ^ M := pow_le_pow_left₀ hG0 hW M
  rw [← Real.exp_nat_mul] at hGM
  have hfac : (1 : ℝ) / (M.factorial : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero M)
  -- the product of squared factorials
  have hprod : ∏ i ∈ range M, ((i.factorial : ℝ)) ^ 2 =
      Real.exp (2 * ∑ i ∈ range M, Real.log (i.factorial)) := by
    have hp : ∏ i ∈ range M, (i.factorial : ℝ) = Real.exp (∑ i ∈ range M, Real.log (i.factorial)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => (Real.exp_log (by positivity)).symm
    rw [Finset.prod_pow, hp, ← Real.exp_nat_mul]
    norm_num
  have hlb := sum_log_factorial_ge hM2
  have hbound : ‖(Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ ((i : ℕ) + (j : ℕ)) ∂m).det‖ ≤
      Real.exp (boundConst σ A n M ((n : ℝ) ^ 2)⁻¹ + M * (n * ℓ + L * Real.log n + c₀)) := by
    refine hheine.trans ?_
    rw [Real.exp_add]
    calc 1 / (M.factorial : ℝ) * (Real.exp (boundConst σ A n M ((n : ℝ) ^ 2)⁻¹) * Gint ^ M)
        ≤ 1 * (Real.exp (boundConst σ A n M ((n : ℝ) ^ 2)⁻¹) * Real.exp (M * (n * ℓ + L * Real.log n + c₀))) := by
          refine mul_le_mul hfac (mul_le_mul_of_nonneg_left hGM (Real.exp_pos _).le) ?_ (by norm_num)
          positivity
      _ = _ := by ring
  rw [hprod, div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  -- the exponent
  have hlogM : Real.log M = Real.log n + Real.log Cm := by
    rw [hM, Real.log_mul hn0.ne' hCm0.ne']
  have hlogε : Real.log (((n : ℝ) ^ 2)⁻¹) = -2 * Real.log n := by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring
  unfold boundConst
  rw [hlogε]
  have hcancel : 2 * (n : ℝ) * M * (A * ((n : ℝ) ^ 2)⁻¹) = 2 * Cm * A := by
    rw [hM]; field_simp
  rw [hcancel]
  have hS : 2 * ((M : ℝ) ^ 2 / 2 * Real.log M - 3 / 4 * (M : ℝ) ^ 2 - M * Real.log M) ≤
      2 * ∑ i ∈ range M, Real.log (i.factorial) := by linarith
  have hM' : (M : ℝ) = n * Cm := hM
  have key : (M : ℝ) * ((M : ℝ) - 1) * Real.log n - M * (-2 * Real.log n) + 2 * Cm * A -
      (n : ℝ) ^ 2 * energyC σ + M * (n * ℓ + L * Real.log n + c₀) -
      2 * ((M : ℝ) ^ 2 / 2 * Real.log M - 3 / 4 * (M : ℝ) ^ 2 - M * Real.log M) =
      (n : ℝ) ^ 2 * (Cm ^ 2 * (3 / 2 - Real.log Cm) - energyC σ + Cm * ℓ) +
        (Cm * (3 + L) * n * Real.log n + (2 * Cm * Real.log Cm + Cm * c₀) * n + 2 * Cm * A) := by
    rw [hlogM, hM']
    ring
  linarith [key, hS]

/-! ### The `ε`-form -/

/-- Every `c₁ n log n + c₂ n + c₃` is eventually below `ε n²`. -/
lemma eventually_remainder_le (c1 c2 c3 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, c1 * n * Real.log n + c2 * n + c3 ≤ ε * (n : ℝ) ^ 2 := by
  have hlog : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hδpos : 0 < ε / (3 * (|c1| + 1)) := by positivity
  have h1 := hlog.def hδpos
  have h2 : ∀ᶠ n : ℕ in atTop, 3 * |c2| / ε ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈3 * |c2| / ε⌉₊] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h3 : ∀ᶠ n : ℕ in atTop, 3 * |c3| / ε ≤ (n : ℝ) ∧ (1 : ℝ) ≤ n := by
    filter_upwards [eventually_ge_atTop ⌈3 * |c3| / ε⌉₊, eventually_ge_atTop 1] with n hn hn1
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hn), by exact_mod_cast hn1⟩
  filter_upwards [h1, h2, h3] with n hn1 hn2 ⟨hn3, hn4⟩
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn4
  rw [Real.norm_of_nonneg hlogn0, Real.norm_of_nonneg hn0] at hn1
  have e1 : c1 * n * Real.log n ≤ ε / 3 * (n : ℝ) ^ 2 := by
    have : c1 * n * Real.log n ≤ |c1| * n * (ε / (3 * (|c1| + 1)) * n) :=
      calc c1 * n * Real.log n ≤ |c1| * n * Real.log n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hn0) hlogn0
        _ ≤ _ := mul_le_mul_of_nonneg_left hn1 (by positivity)
    refine this.trans ?_
    have hr : |c1| * (ε / (3 * (|c1| + 1))) ≤ ε / 3 := by
      have : |c1| * (ε / (3 * (|c1| + 1))) = ε / 3 * (|c1| / (|c1| + 1)) := by
        field_simp
      rw [this]
      have : |c1| / (|c1| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith [hε]
    calc |c1| * n * (ε / (3 * (|c1| + 1)) * n) = (|c1| * (ε / (3 * (|c1| + 1)))) * (n : ℝ) ^ 2 := by ring
      _ ≤ ε / 3 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hr (by positivity)
  have e2 : c2 * n ≤ ε / 3 * (n : ℝ) ^ 2 := by
    have : 3 * |c2| ≤ ε * n := by
      rw [div_le_iff₀ hε] at hn2; linarith
    nlinarith [le_abs_self c2, abs_nonneg c2]
  have e3 : c3 ≤ ε / 3 * (n : ℝ) ^ 2 := by
    have : 3 * |c3| ≤ ε * n := by
      rw [div_le_iff₀ hε] at hn3; linarith
    nlinarith [le_abs_self c3, abs_nonneg c3]
  linarith

universe u

/-- **Theorem A, `ε`-form** (LD09, generic): with `D = -(κ(Cm) - energyC σ + Cm ℓ)`, for every `ε > 0`
there is `R₀` (depending only on `Cm, A, ℓ, L, c₀, ε`) such that for all weight spaces, all
`n ≥ R₀` and `M = n Cm` satisfying the hypotheses, `‖det‖ / ∏ (i!)² ≤ exp (-(D - ε) n²)`. -/
theorem theoremA_eventually {σ : Measure ℂ} [IsFiniteMeasure σ] {b A : ℝ} (hσ : BallMaj σ b A)
    {Cm : ℝ} (hCm : σ.real univ = Cm) (hCm0 : 0 < Cm) (ℓ L c₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ {X : Type u} [MeasurableSpace X] (m : Measure X) [SigmaFinite m] (w z : X → ℂ)
      {n M : ℕ}, R₀ ≤ n → (M : ℝ) = n * Cm →
      (∀ i j : Fin M, Integrable (fun x => w x * z x ^ (i : ℕ) * z x ^ (j : ℕ)) m) →
      Integrable (fun x => ‖w x‖ * Real.exp (2 * n * potC σ (z x / n))) m →
      (∫ x, ‖w x‖ * Real.exp (2 * n * potC σ (z x / n)) ∂m ≤
        Real.exp (n * ℓ + L * Real.log n + c₀)) →
      ‖(Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ ((i : ℕ) + (j : ℕ)) ∂m).det‖ /
          ∏ i ∈ range M, ((i.factorial : ℝ)) ^ 2 ≤
        Real.exp (-(-(Cm ^ 2 * (3 / 2 - Real.log Cm) - energyC σ + Cm * ℓ) - ε) * (n : ℝ) ^ 2) := by
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp
    (eventually_remainder_le (Cm * (3 + L)) (2 * Cm * Real.log Cm + Cm * c₀) (2 * Cm * A) hε)
  refine ⟨max R₁ (max 2 ⌈2 / Cm⌉₊), ?_⟩
  intro X _ m _ w z n M hn hM hint hG hW
  have hn1 : R₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn3 : ⌈2 / Cm⌉₊ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hM2 : 2 ≤ M := by
    have h1 : 2 / Cm ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn3)
    have h2 : (2 : ℝ) ≤ n * Cm := by rwa [div_le_iff₀ hCm0] at h1
    have : (2 : ℝ) ≤ M := by rw [hM]; exact h2
    exact_mod_cast this
  have h := theoremA_abstract m hσ w z hCm hCm0 hn2 hM hM2 hint hG hW
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have := hR₁ n hn1
  nlinarith [this]

end CatalanCore.Decay.TheoremA
