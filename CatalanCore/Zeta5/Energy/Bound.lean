module

public import CatalanCore.Zeta5.Energy.Field
public import CatalanCore.Zeta5.Energy.Weights
public import CatalanCore.Zeta5.Energy.Stirling

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/EnergyBound.lean and Apery/RealBound.lean (Moritz Firsching); changes: module conversion, namespace CatalanCore.Zeta5.Energy with `open Apery`; the sixteen-atom data `M0`, `Irho`, `energy_ineq` are replaced by the design data `Design ρ b Φ M₀` and `energy_ineq_n` (from `config_ineq`), the constants of `Aconst`, `log_Δ_le'` and `real_bound` change accordingly (retained factor `√t/K`, regularisation error `2 h C_circ`). -/

/-!
# The energy bound (6.14) and the real bound (Proposition 6.3) (ZD26, ZD27, ZD28, ZD30, ZD31)

Design data (`Design ρ b Φ M₀`): a finite measure `ρ` on `ℝ` of total mass `λ = 37/40`, with the
arcsine majorant `ArcMaj ρ b Φ` and the cell hypothesis `CellHyp ρ M₀` (`2U - V ≤ M₀`).  Then, for
`K = 40 n`, `h = 37 n`, `N_p = 3 n`:

* `integrand_le` (ZD26) : the pointwise bound of the integrand of (6.10), which combines
  `w_le'` (ZD24), the sum-to-integral comparison (ZD25) and `energy_ineq_n` (ZD07/ZD31);
* `log_Δ_le'` (ZD28) : `log Δ_K(ξ) ≤ 2h(h + 6N_p - K) log K + (λM₀ - I(ρ))K² + 18 h log K
  + (41 + 2 C_circ) h`, with `∫ (1 + 2πy)^5 e^{-y/K} dy ≤ (2π)^5·32·121·K^6` (ZD27);
* `real_bound` (ZD30) : `F_K(ξ) > 0` and `log F_K(ξ) ≤ (C* + λM₀ - I(ρ)) K² + 24 K log K
  + (47 + 2 C_circ) K`.
-/

open Filter Topology Set MeasureTheory Finset Polynomial Apery

namespace CatalanCore.Zeta5.Energy

/-- The design data of the decay chain: the comparison measure `ρ` (of mass `37/40`), the arcsine
majorant (ZD04/ZD05 hypothesis) and the cell inequality `2U - V ≤ M₀`. -/
structure Design (ρ : Measure ℝ) (b Φ M₀ : ℝ) : Prop where
  arc : ArcMaj ρ b Φ
  mass : ρ.real univ = 37 / 40
  cell : CellHyp ρ M₀

/-- The circle constant `C_circ = 2√2 Φ/√b` of ZD05. -/
noncomputable def circC (b Φ : ℝ) : ℝ := 2 * Real.sqrt 2 * Φ / Real.sqrt b

lemma circC_nonneg {b Φ : ℝ} (hΦ : 0 ≤ Φ) : 0 ≤ circC b Φ := by
  unfold circC; positivity

variable {ρ : Measure ℝ} [IsFiniteMeasure ρ] {b Φ M₀ : ℝ}

/-- **(6.9)** for the design data: the configuration inequality with `h = 37 n` points. -/
theorem energy_ineq_n (D : Design ρ b Φ M₀) (n : ℕ) (hn : 0 < n) (t : Fin (37 * n) → ℝ)
    (ht : ∀ i, 0 < t i) (hinj : Function.Injective t) :
    (∑ i, ∑ j ∈ Finset.Ioi i, 2 * Real.log |t j - t i|) - Kr n * ∑ i, Vfield (t i) +
        ∑ i, Real.sqrt (t i) ≤
      (lam * M₀ - energyI ρ) * Kr n ^ 2 + 2 * (37 * n) * circC b Φ +
        2 * (37 * n) * Real.log (Kr n) + 2 * (37 * n) := by
  have hK : (2 : ℝ) ≤ Kr n := by
    simp only [Kr]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hh : ((37 * n : ℕ) : ℝ) = Kr n * ρ.real univ := by
    rw [D.mass]; simp only [Kr]; push_cast; ring
  have := config_ineq D.arc hK hh Vfield (fun x hx => pointwise_bound D.cell hK hx) t
    (fun i => (ht i).le) hinj
  rw [D.mass] at this
  push_cast at this ⊢
  unfold circC
  linarith

/-- Reindexing `∑_{j ∈ Icc 1 m} f j = ∑_{j < m} f (j + 1)`. -/
lemma sum_Icc_eq_sum_range' (m : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 m, f j = ∑ j ∈ Finset.range m, f (j + 1) := by
  have e1 : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e1, Finset.sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm]

lemma aeval_D_eq (m : ℕ) (s : ℝ) : aeval s (D m) = ∏ j ∈ Icc 1 m, (s + (j : ℝ) ^ 2) := by
  simp only [D, map_prod, map_add, aeval_X, aeval_C, eq_ratCast, Rat.cast_pow, Rat.cast_natCast]

lemma sum_Ioi_card_mul_two (h : ℕ) : (∑ i : Fin h, (Finset.Ioi i).card) * 2 = h * (h - 1) := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i) h, Finset.sum_range_reflect (fun i => i) h,
    Finset.sum_range_id_mul_two]

lemma sum_Ioi_const (h : ℕ) (c : ℝ) :
    ∑ i : Fin h, ∑ _j ∈ Finset.Ioi i, c = (h : ℝ) * ((h : ℝ) - 1) / 2 * c := by
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
  have := sum_Ioi_card_mul_two h
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have hcast : ((∑ i : Fin h, (Finset.Ioi i).card : ℕ) : ℝ) = (h : ℝ) * ((h : ℝ) - 1) / 2 := by
    have h2 : (((∑ i : Fin h, (Finset.Ioi i).card) * 2 : ℕ) : ℝ) = ((h * (h - 1) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub (by omega : 1 ≤ h)] at h2 ⊢
    linarith
  rw [← hcast]
  push_cast
  ring

/-- `log D_m(y²) = 2m log K + ∑_{j<m} log(t + ((j+1)/K)²)` with `t = (y/K)²`. -/
lemma log_aeval_D (m : ℕ) {K y : ℝ} (hK : 0 < K) (hy : 0 < y) :
    Real.log (aeval (y ^ 2) (D m)) =
      2 * m * Real.log K + ∑ j ∈ range m, Real.log ((y / K) ^ 2 + (((j : ℝ) + 1) / K) ^ 2) := by
  rw [aeval_D_eq, Real.log_prod (fun j _ => by positivity), sum_Icc_eq_sum_range']
  have : ∀ j : ℕ, Real.log (y ^ 2 + ((j + 1 : ℕ) : ℝ) ^ 2) =
      2 * Real.log K + Real.log ((y / K) ^ 2 + (((j : ℝ) + 1) / K) ^ 2) := by
    intro j
    have e : y ^ 2 + ((j + 1 : ℕ) : ℝ) ^ 2 = K ^ 2 * ((y / K) ^ 2 + (((j : ℝ) + 1) / K) ^ 2) := by
      push_cast; field_simp
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The constant `A_n` in the pointwise bound. -/
noncomputable def Aconst (ρ : Measure ℝ) (b Φ M₀ : ℝ) (n : ℕ) : ℝ :=
  2 * (37 * n) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) +
    (lam * M₀ - energyI ρ) * Kr n ^ 2 + 12 * (37 * n) * Real.log (Kr n) +
    (12 * Real.log 2 + 14 + 2 * circC b Φ) * (37 * n)

/-- The one-dimensional factor `(1 + 2πy)^5 e^{-y/K}`. -/
noncomputable def gK (n : ℕ) (y : ℝ) : ℝ := (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / Kr n * y))

/-- **Pointwise bound** for the integrand of (6.10), for positive pairwise distinct `y`. -/
theorem integrand_le (D : Design ρ b Φ M₀) (n : ℕ) (hn : 0 < n) (y : Fin (37 * n) → ℝ) (hy : ∀ i, 0 < y i)
    (hinj : Function.Injective y) :
    (Matrix.vandermonde fun j => y j ^ 2).det ^ 2 * ∏ j, Apery.ν n (y j) ≤
      Real.exp (Aconst ρ b Φ M₀ n) * ∏ i, gK n (y i) := by
  set K : ℝ := Kr n with hKdef
  have hK : 0 < K := by simp only [hKdef, Kr]; positivity
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK1 : 1 ≤ K := by
    simp only [hKdef, Kr]
    linarith
  set t : Fin (37 * n) → ℝ := fun i => (y i / K) ^ 2 with htdef
  have ht : ∀ i, 0 < t i := fun i => by
    simp only [htdef]; have := hy i; positivity
  have htinj : Function.Injective t := by
    intro i j hij
    simp only [htdef] at hij
    have := (pow_left_inj₀ (div_pos (hy i) hK).le (div_pos (hy j) hK).le two_ne_zero).mp hij
    exact hinj ((div_left_inj' hK.ne').mp this)
  -- positivity of both sides
  have hdet : (Matrix.vandermonde fun j => y j ^ 2).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact hinj ((pow_left_inj₀ (hy i).le (hy j).le two_ne_zero).mp hij)
  have hν : ∀ j, 0 < ν n (y j) := fun j => ν_pos n (hy j)
  have hL : 0 < (Matrix.vandermonde fun j => y j ^ 2).det ^ 2 * ∏ j, Apery.ν n (y j) :=
    mul_pos (by positivity) (Finset.prod_pos fun j _ => hν j)
  have hg : ∀ i, 0 < gK n (y i) := fun i => by unfold gK; have := hy i; positivity
  have hR : 0 < Real.exp (Aconst ρ b Φ M₀ n) * ∏ i, gK n (y i) :=
    mul_pos (Real.exp_pos _) (Finset.prod_pos fun i _ => hg i)
  rw [← Real.log_le_log_iff hL hR]
  -- log of the left-hand side
  have hne : ∀ i j : Fin (37 * n), j ∈ Finset.Ioi i → y j ^ 2 - y i ^ 2 ≠ 0 := by
    intro i j hj h0
    have : y j ^ 2 = y i ^ 2 := by linarith
    exact (Finset.mem_Ioi.mp hj).ne' (hinj ((pow_left_inj₀ (hy j).le (hy i).le two_ne_zero).mp this))
  have hdet2 : Real.log ((Matrix.vandermonde fun j => y j ^ 2).det ^ 2) =
      ∑ i, ∑ j ∈ Finset.Ioi i, (4 * Real.log K + 2 * Real.log |t j - t i|) := by
    rw [Matrix.det_vandermonde]
    simp only [← Finset.prod_pow]
    rw [Real.log_prod (fun i _ =>
      (Finset.prod_pos fun j hj => lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hne i j hj)))).ne')]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_prod (fun j hj => pow_ne_zero 2 (hne i j hj))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have e : y j ^ 2 - y i ^ 2 = K ^ 2 * (t j - t i) := by
      simp only [htdef]; field_simp
    have hne' : t j - t i ≠ 0 := by
      intro h0; apply hne i j hj; rw [e, h0, mul_zero]
    rw [Real.log_pow, e, ← Real.log_abs, abs_mul, Real.log_mul (by positivity)
      (abs_pos.mpr hne').ne', abs_of_pos (by positivity : (0:ℝ) < K ^ 2), Real.log_pow]
    push_cast; ring
  -- log of each weight
  have hν_le : ∀ i, Real.log (ν n (y i)) ≤
      (12 * (3 * n) - 2 * (40 * n)) * Real.log K - K * Vfield (t i) + 12 * Real.log (2 * K) + 12 +
        5 * Real.log (1 + 2 * Real.pi * y i) := by
    intro i
    have hyi := hy i
    have hDN := aeval_D_pos (3 * n) (t := y i ^ 2) (by positivity)
    have hDK := aeval_D_pos (40 * n) (t := y i ^ 2) (by positivity)
    have hw := w_pos hyi
    unfold ν
    rw [Real.log_mul (by positivity) hw.ne', Real.log_div (by positivity) hDK.ne', Real.log_pow,
      log_aeval_D _ hK hyi, log_aeval_D _ hK hyi]
    -- comparison lemmas
    have hN : ((3 * n : ℕ) : ℝ) / K = 3 / 40 := by
      simp only [hKdef, Kr]; push_cast; field_simp
    have hKK : ((40 * n : ℕ) : ℝ) / K = 1 := by
      simp only [hKdef, Kr]; push_cast; field_simp
    have h1 := sum_log_le_integral (ht i) hK1 (m := 3 * n) (by omega)
      (by simp only [hKdef, Kr]; push_cast; linarith [(by exact_mod_cast hn : (1:ℝ) ≤ n)])
    have h2 := integral_le_sum_log (ht i) hK (40 * n)
    rw [hN] at h1
    rw [hKK] at h2
    -- the weight
    have hw' : Real.log (w (y i)) ≤ 5 * Real.log (1 + 2 * Real.pi * y i) - 2 * Real.pi * y i := by
      calc Real.log (w (y i)) ≤ Real.log (1 / Real.pi * (1 + 2 * Real.pi * y i) ^ 5 *
            Real.exp (-(2 * Real.pi * y i))) := Real.log_le_log hw (w_le' hyi)
        _ = Real.log (1 / Real.pi) + 5 * Real.log (1 + 2 * Real.pi * y i) - 2 * Real.pi * y i := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
              Real.log_exp, Real.log_pow]
            push_cast; ring
        _ ≤ 5 * Real.log (1 + 2 * Real.pi * y i) - 2 * Real.pi * y i := by
            have : Real.log (1 / Real.pi) ≤ 0 := by
              rw [one_div, Real.log_inv]; linarith [Real.log_nonneg (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)]
            linarith
    -- `√t = y/K`
    have hsqrt : Real.sqrt (t i) = y i / K := by
      simp only [htdef]; exact Real.sqrt_sq (by positivity)
    have hV : K * Vfield (t i) = 2 * Real.pi * y i + K * (∫ u in (0:ℝ)..1, Real.log (t i + u ^ 2)) -
        6 * (K * ∫ u in (0:ℝ)..(3 / 40), Real.log (t i + u ^ 2)) := by
      unfold Vfield; rw [hsqrt]; field_simp
    push_cast at h1 h2 ⊢
    rw [hV]
    nlinarith [h1, h2, hw']
  -- assemble
  rw [Real.log_mul (by positivity) (Finset.prod_pos fun j _ => hν j).ne', hdet2,
    Real.log_prod (fun j _ => (hν j).ne'), Real.log_mul (Real.exp_pos _).ne'
    (Finset.prod_pos fun i _ => hg i).ne', Real.log_exp, Real.log_prod (fun i _ => (hg i).ne')]
  have hE := energy_ineq_n D n hn t ht htinj
  have hsqrt : ∀ i, Real.sqrt (t i) = y i / K := fun i => by
    simp only [htdef]; exact Real.sqrt_sq (div_pos (hy i) hK).le
  simp_rw [hsqrt] at hE
  have hgi : ∀ i, Real.log (gK n (y i)) = 5 * Real.log (1 + 2 * Real.pi * y i) - y i / K := by
    intro i
    unfold gK
    rw [Real.log_mul (by have := hy i; positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
    push_cast; ring
  simp_rw [hgi]
  simp only [Finset.sum_add_distrib, sum_Ioi_const]
  have hsum_le := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hν_le i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum_le
  have hlog2K : Real.log (2 * K) = Real.log 2 + Real.log K := Real.log_mul two_ne_zero hK.ne'
  rw [hlog2K] at hsum_le
  unfold Aconst
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [← Finset.mul_sum] at hE
  rw [← hKdef] at *
  push_cast at *
  linarith [hE, hsum_le]



lemma integrableOn_gK (n : ℕ) (hn : 0 < n) : IntegrableOn (gK n) (Ioi 0) := by
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  have hr : 0 < 1 / Kr n := by positivity
  have hg : IntegrableOn (fun y : ℝ => (2 * Real.pi) ^ 5 * 32 * (y ^ 0 * Real.exp (-(1 / Kr n * y))) +
      (2 * Real.pi) ^ 5 * 32 * (y ^ 5 * Real.exp (-(1 / Kr n * y)))) (Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul 0 hr).const_mul _).add ((integrableOn_pow_mul_exp_neg_mul 5 hr).const_mul _)
  have hcont : Continuous (gK n) := by unfold gK; fun_prop
  refine hg.mono' hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_of_nonneg (by unfold gK; positivity)]
  unfold gK
  have h1 : (1 + 2 * Real.pi * y) ^ 5 ≤ (2 * Real.pi) ^ 5 * (1 + y) ^ 5 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_gt_three]) 5
  have h2 : (1 + y) ^ 5 ≤ 32 * (1 + y ^ 5) := by
    rcases le_or_gt y 1 with h | h
    · have : (1 + y) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have : 0 ≤ y ^ 5 := by positivity
      nlinarith
    · have : (1 + y) ^ 5 ≤ (2 * y) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
      have : 0 ≤ y ^ 5 := by positivity
      nlinarith
  have he : 0 ≤ Real.exp (-(1 / Kr n * y)) := (Real.exp_pos _).le
  calc (1 + 2 * Real.pi * y) ^ 5 * Real.exp (-(1 / Kr n * y))
      ≤ (2 * Real.pi) ^ 5 * (32 * (1 + y ^ 5)) * Real.exp (-(1 / Kr n * y)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = _ := by simp only [pow_zero, one_mul]; ring

/-- `log ((2π)^5 · 32 · 121) ≤ 18`. -/
lemma log_C_le : Real.log ((2 * Real.pi) ^ 5 * 32 * 121) ≤ 18 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h18 : Real.exp 18 = Real.exp 1 ^ 18 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h18]
  have hpow : (2.7182818283 : ℝ) ^ 18 ≤ Real.exp 1 ^ 18 := pow_le_pow_left₀ (by norm_num) he.le 18
  have h2pi : (2 * Real.pi) ^ 5 ≤ 6.3 ^ 5 := pow_le_pow_left₀ (by positivity) (by linarith) 5
  calc (2 * Real.pi) ^ 5 * 32 * 121 ≤ 6.3 ^ 5 * 32 * 121 := by gcongr
    _ ≤ (2.7182818283 : ℝ) ^ 18 := by norm_num
    _ ≤ Real.exp 1 ^ 18 := hpow

/-- **(6.14)** (with the linear term `165 h`): the energy bound for `Δ_K(ζ(5))`, from the
configuration inequality `energy_ineq`. -/
theorem log_Δ_le' (D : Design ρ b Φ M₀) (n : ℕ) (hn : 0 < n) :
    Real.log (aeval zeta5 (Δ n)) ≤
      2 * (37 * n) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) +
        (lam * M₀ - energyI ρ) * Kr n ^ 2 + 18 * (37 * n) * Real.log (Kr n) +
          (41 + 2 * circC b Φ) * (37 * n) := by
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK1 : 1 ≤ Kr n := by simp only [Kr]; linarith
  have hlogK : 0 ≤ Real.log (Kr n) := Real.log_nonneg hK1
  have hΔ := Δ_pos n hn
  rw [Δ_eq_integral] at hΔ ⊢
  set I := ∫ x : Fin (37 * n) → ℝ, (Matrix.vandermonde fun j => x j ^ 2).det ^ 2 * ∏ j, ν n (x j)
    ∂(Measure.pi fun _ : Fin (37 * n) => μpos) with hI
  have hfac : (0 : ℝ) < ((37 * n).factorial : ℝ) := by positivity
  have hIpos : 0 < I := by
    by_contra hneg
    push Not at hneg
    have : (1 / ((37 * n).factorial : ℝ)) * I ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hgint := integrableOn_gK n hn
  have hg0 : 0 ≤ ∫ y in Ioi 0, gK n y :=
    setIntegral_nonneg measurableSet_Ioi fun y hy => by
      have : (0 : ℝ) < y := hy
      unfold gK; positivity
  have hg1 : ∫ y in Ioi 0, gK n y ≤ (2 * Real.pi) ^ 5 * 32 * 121 * Kr n ^ 6 :=
    integral_one_add_pow_mul_exp hK1
  -- the integral bound
  have hbound : I ≤ Real.exp (Aconst ρ b Φ M₀ n) * (∫ y in Ioi 0, gK n y) ^ (37 * n) := by
    calc I ≤ ∫ x : Fin (37 * n) → ℝ, Real.exp (Aconst ρ b Φ M₀ n) * ∏ i, gK n (x i)
          ∂(Measure.pi fun _ : Fin (37 * n) => μpos) := by
          refine integral_mono_of_nonneg ?_ ((Integrable.fintype_prod fun _ => hgint).const_mul _) ?_
          · filter_upwards [ae_pos_injective (37 * n)] with x hx
            exact mul_nonneg (sq_nonneg _) (Finset.prod_pos fun j _ => ν_pos n (hx.1 j)).le
          · filter_upwards [ae_pos_injective (37 * n)] with x hx
            exact integrand_le D n hn x hx.1 hx.2
      _ = Real.exp (Aconst ρ b Φ M₀ n) * (∫ y in Ioi 0, gK n y) ^ (37 * n) := by
          rw [integral_const_mul, integral_fintype_prod_eq_prod (fun _ => gK n), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
  have hlog1 : Real.log (1 / ((37 * n).factorial : ℝ) * I) ≤ Real.log I := by
    rw [Real.log_mul (by positivity) hIpos.ne']
    have : Real.log (1 / ((37 * n).factorial : ℝ)) ≤ 0 := by
      rw [one_div, Real.log_inv]
      linarith [Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _) :
        (1 : ℝ) ≤ ((37 * n).factorial : ℝ))]
    linarith
  have hlog2 : Real.log 2 ≤ 0.7 := by have := Real.log_two_lt_d9; linarith
  have hsqrt2 : Real.sqrt 2 ≤ 1.5 := by
    rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hC := log_C_le
  have hCpos : (0 : ℝ) < (2 * Real.pi) ^ 5 * 32 * 121 := by positivity
  calc Real.log (1 / ((37 * n).factorial : ℝ) * I) ≤ Real.log I := hlog1
    _ ≤ Real.log (Real.exp (Aconst ρ b Φ M₀ n) * ((2 * Real.pi) ^ 5 * 32 * 121 * Kr n ^ 6) ^ (37 * n)) := by
        refine Real.log_le_log hIpos (hbound.trans ?_)
        gcongr
    _ = Aconst ρ b Φ M₀ n + (37 * n) * (Real.log ((2 * Real.pi) ^ 5 * 32 * 121) + 6 * Real.log (Kr n)) := by
        rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow,
          Real.log_mul hCpos.ne' (by positivity), Real.log_pow]
        push_cast; ring
    _ ≤ _ := by
        unfold Aconst
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 37 * n) hlogK]


/-- **ZD30, Proposition 6.3**: `F_K(ξ) > 0` and
`log F_K(ξ) ≤ (C* + λM₀ - I(ρ)) K² + 24 K log K + (47 + 2 C_circ) K`, i.e. with
`D := I(ρ) - λM₀ - C*`, `log F_K(ξ) ≤ -D K² + O(K log K)`. -/
theorem real_bound (D : Design ρ b Φ M₀) (n : ℕ) (hn : 0 < n) :
    0 < aeval zeta5 (F n) ∧
      Real.log (aeval zeta5 (F n)) ≤
        (Cstar + lam * M₀ - energyI ρ) * Kr n ^ 2 + 24 * Kr n * Real.log (Kr n) +
          (47 + 2 * circC b Φ) * Kr n := by
  have hS : (0 : ℝ) < S n := by exact_mod_cast S_pos n
  have hΔ := Δ_pos n hn
  have hF : aeval zeta5 (F n) = (S n : ℝ) * aeval zeta5 (Δ n) := by
    simp [F, aeval_C]
  refine ⟨by rw [hF]; positivity, ?_⟩
  rw [hF, Real.log_mul hS.ne' hΔ.ne']
  have h1 := log_Δ_le' D n hn
  have h2 := log_S_le n hn
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  have hlogK : 0 ≤ Real.log (Kr n) :=
    Real.log_nonneg (by simp only [Kr]; norm_cast; omega)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC : 0 ≤ circC b Φ := circC_nonneg D.arc.F_nonneg
  have e1 : (37 * (n : ℝ)) * Real.log (Kr n) ≤ Kr n * Real.log (Kr n) :=
    mul_le_mul_of_nonneg_right (by simp only [Kr]; linarith) hlogK
  have e2 : (37 * (n : ℝ)) * (47 + 2 * circC b Φ) ≤ Kr n * (47 + 2 * circC b Φ) :=
    mul_le_mul_of_nonneg_right (by simp only [Kr]; linarith) (by positivity)
  have hcancel : 2 * (37 * (n : ℝ)) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) +
      (2 * lam - 12 * alph * lam - 2 * lam ^ 2) * Kr n ^ 2 = 0 := by
    simp only [Kr, lam, alph]; ring
  have e3 : (2 * lam - 12 * alph * lam - 2 * lam ^ 2) * Kr n ^ 2 * Real.log (Kr n) +
      2 * (37 * (n : ℝ)) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) = 0 := by
    have := congrArg (· * Real.log (Kr n)) hcancel
    simp only [zero_mul] at this
    linarith
  nlinarith [h1, h2, e1, e2, e3]

/-- ZD28 in the ledger constants: if `C_circ ≤ 59` then
`log Δ_K(ξ) ≤ 2h(h + 6N_p - K) log K + (λM₀ - I(ρ))K² + 18 h log K + 160 h`. -/
theorem log_Δ_le_160 (D : Design ρ b Φ M₀) (hC : circC b Φ ≤ 59) (n : ℕ) (hn : 0 < n) :
    Real.log (aeval zeta5 (Δ n)) ≤
      2 * (37 * n) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) +
        (lam * M₀ - energyI ρ) * Kr n ^ 2 + 18 * (37 * n) * Real.log (Kr n) + 160 * (37 * n) := by
  have h := log_Δ_le' D n hn
  have hn' : (0 : ℝ) ≤ 37 * n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hC hn']

/-- ZD30 in the ledger constants: if `C_circ ≤ 76`, with `D := I(ρ) - λM₀ - C*`,
`log F_K(ξ) ≤ -D K² + 24 K log K + 200 K`. -/
theorem real_bound_200 (D : Design ρ b Φ M₀) (hC : circC b Φ ≤ 76) (n : ℕ) (hn : 0 < n) :
    0 < aeval zeta5 (F n) ∧
      Real.log (aeval zeta5 (F n)) ≤
        -(energyI ρ - lam * M₀ - Cstar) * Kr n ^ 2 + 24 * Kr n * Real.log (Kr n) + 200 * Kr n := by
  obtain ⟨hpos, hle⟩ := real_bound D n hn
  refine ⟨hpos, ?_⟩
  have hK : 0 < Kr n := by simp only [Kr]; positivity
  nlinarith [mul_le_mul_of_nonneg_right hC hK.le]

end CatalanCore.Zeta5.Energy
