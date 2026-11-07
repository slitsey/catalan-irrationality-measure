module

public import CatalanMeasure.GenD.Analytic.NodalKeyhole
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Tactic

/-!
# Interval nodes (ledger G04, G05, G07, G29)

GP Theorem 4.1, Corollary 4.2, Proposition 4.4 and section 4.1, with the audit repairs R4 and R7.
Everything is generic: `q` intervals `[lo_c, hi_c]` (`ι`), node counts `K_c`, the pair rule with
`d₀` pairs and the node map `Fin (d₀ * N) → ℝ`, `ζ`, `δ`, `D`, `C₀`, `w` are parameters.  No
numerical value and no import of the literals module; the 106 intervals and the contour constants are data
for `IntervalNodesData` and the hcirc certificate.

* `lagrange_basis_le` (G04): `|l_a(z)| ≤ K_c 2^(q-1) exp(Λ(z) - Λ(t_a))`, `Λ = Σ_c K_c G_c`,
  for every `z : ℂ`.  The proof does not use the Bernstein-Walsh theorem: `T_K(x_j) = 0`
  gives `l_j = T_K(w) / (T_K'(x_j) (w - x_j))`, the divided difference of `T_K` is a product of
  two geometric sums in `u`, `w = (u + u⁻¹)/2`, and `|T_K(v)| ≥ ½ exp(K G(v))` on real `|v| ≥ 1`
  is `cosh`.
* `lagrange_basis_le_L`, `quadBasis_tauI_le` (G05): `|l_a(z)| ≤ C N exp(N (L(z) - L(t_a)))`.
* `hweights_of_cardinal_L`, `hweights_tauI` (G07): `hweights^{ζ,δ}` of
  `weighted_atom_point_zeta_of_signed` from (hcirc) and (hseg); `hseg` only on `ζ ≤ |x| < 1`
  (audit repair R7), the endpoints `x = ±1` by continuity (`real_bound_extend`).
* `tauI`, `tauI_injective`, `tauI_mem`, `tauI_ne_zero`, `tauI_support` (G29): `hinj`, `hmem`,
  `hzero`, `hsupport` of `delta_small_nodes`.
-/

@[expose] public section
namespace CatalanMeasure.GenD.Signed.RouteI
open Polynomial Finset Set Polynomial.Chebyshev CatalanMeasure.GenD.Analytic CatalanMeasure
noncomputable section

/-! ## Real arguments of `ellipseLog` -/

theorem ellipseH_ofReal (y : ℝ) : ellipseH (y : ℂ) = (|y - 1| + |y + 1|) / 2 := by
  unfold ellipseH
  have h1 : ‖(y : ℂ) - 1‖ = |y - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(y : ℂ) + 1‖ = |y + 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]

theorem ellipseLog_ofReal_of_abs_le_one {y : ℝ} (h : |y| ≤ 1) : ellipseLog (y : ℂ) = 0 := by
  have h' := abs_le.mp h
  have : ellipseH (y : ℂ) = 1 := by
    rw [ellipseH_ofReal, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    ring
  unfold ellipseLog
  rw [this]
  simp

theorem ellipseH_ofReal_of_one_le_abs {y : ℝ} (h : 1 ≤ |y|) : ellipseH (y : ℂ) = |y| := by
  rw [ellipseH_ofReal]
  rcases le_abs'.mp h with h | h
  · rw [abs_of_nonpos (by linarith : y ≤ 0), abs_of_nonpos (by linarith : y - 1 ≤ 0),
      abs_of_nonpos (by linarith : y + 1 ≤ 0)]
    linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ y), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

theorem ellipseLog_nonneg (v : ℂ) : 0 ≤ ellipseLog v :=
  Real.arcosh_nonneg (ellipseH_ge_one v)

/-- Fact 2: lower bound of `T_K` at real points outside `[-1,1]`. -/
theorem half_exp_le_norm_T_ofReal (K : ℕ) {y : ℝ} (hy : 1 ≤ |y|) :
    (1 / 2) * Real.exp ((K : ℝ) * ellipseLog (y : ℂ)) ≤
      ‖(Chebyshev.T ℂ (K : ℤ)).eval (y : ℂ)‖ := by
  rw [← Chebyshev.complex_ofReal_eval_T, Complex.norm_real, Real.norm_eq_abs]
  have hlog : ellipseLog (y : ℂ) = Real.arcosh |y| := by
    unfold ellipseLog; rw [ellipseH_ofReal_of_one_le_abs hy]
  rw [hlog]
  have hcosh : (Chebyshev.T ℝ (K : ℤ)).eval |y| = Real.cosh ((K : ℝ) * Real.arcosh |y|) := by
    have := Chebyshev.T_real_cosh (Real.arcosh |y|) (K : ℤ)
    rw [Real.cosh_arcosh hy] at this
    rw [this]; push_cast; rfl
  have habs : |(Chebyshev.T ℝ (K : ℤ)).eval y| = (Chebyshev.T ℝ (K : ℤ)).eval |y| := by
    rcases le_abs'.mp hy with h | h
    · rw [abs_of_nonpos (by linarith : y ≤ 0)]
      have h' := Chebyshev.T_eval_neg (R := ℝ) (K : ℤ) (-y)
      rw [neg_neg] at h'
      rw [h', abs_mul]
      have : |((K : ℤ).negOnePow : ℝ)| = 1 := by
        rcases Int.units_eq_one_or ((K : ℤ).negOnePow) with h | h <;> simp [h]
      rw [this, one_mul]
      exact abs_of_nonneg (by
        have := Chebyshev.one_le_eval_T_real (K : ℤ) (x := -y) (by linarith)
        linarith)
    · rw [abs_of_nonneg (by linarith : 0 ≤ y)]
      exact abs_of_nonneg (by
        have := Chebyshev.one_le_eval_T_real (K : ℤ) (x := y) (by linarith)
        linarith)
  rw [habs, hcosh, Real.cosh_eq]
  have : 0 < Real.exp (-((K : ℝ) * Real.arcosh |y|)) := Real.exp_pos _
  linarith

theorem cosh_def' (z : ℂ) : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 := rfl

theorem cos_eq_exp_inv (θ : ℂ) :
    Complex.cos θ = (Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹) / 2 := by
  rw [← Complex.cosh_mul_I, cosh_def', ← Complex.exp_neg]


/-! ## Chebyshev polynomials in the variable `u + u⁻¹` and Fact 3 -/

theorem T_eval_inv_add (K : ℕ) {u : ℂ} (hu : u ≠ 0) :
    (Chebyshev.T ℂ (K : ℤ)).eval ((u + u⁻¹) / 2) = (u ^ K + (u⁻¹) ^ K) / 2 := by
  obtain ⟨θ, rfl⟩ : ∃ θ, Complex.exp θ = u := ⟨Complex.log u, Complex.exp_log hu⟩
  have h := Chebyshev.T_complex_cosh θ (K : ℤ)
  have e1 : Complex.cosh θ = (Complex.exp θ + (Complex.exp θ)⁻¹) / 2 := by
    rw [cosh_def', Complex.exp_neg]
  have e2 : Complex.cosh (((K : ℤ) : ℂ) * θ) =
      ((Complex.exp θ) ^ K + ((Complex.exp θ)⁻¹) ^ K) / 2 := by
    rw [cosh_def', Complex.exp_neg]
    push_cast
    rw [Complex.exp_nat_mul, inv_pow]
  rw [e1] at h
  rw [h, e2]

theorem cheb_divdiff {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (K : ℕ) :
    (Chebyshev.T ℂ (K : ℤ)).eval ((u + u⁻¹) / 2) - (Chebyshev.T ℂ (K : ℤ)).eval ((v + v⁻¹) / 2) =
      ((u + u⁻¹) / 2 - (v + v⁻¹) / 2) *
        ((∑ a ∈ range K, u ^ a * v ^ (K - 1 - a)) * ∑ b ∈ range K, ((u * v)⁻¹) ^ b) := by
  rw [T_eval_inv_add K hu, T_eval_inv_add K hv]
  have h1 := geom_sum₂_mul u v K
  have h2 := geom_sum_mul ((u * v)⁻¹) K
  have k1 : u ^ K * (u⁻¹) ^ K = 1 := by rw [← mul_pow, mul_inv_cancel₀ hu, one_pow]
  have k2 : v ^ K * (v⁻¹) ^ K = 1 := by rw [← mul_pow, mul_inv_cancel₀ hv, one_pow]
  have hr : ((u * v)⁻¹) ^ K = (u⁻¹) ^ K * (v⁻¹) ^ K := by rw [mul_inv, mul_pow]
  rw [hr] at h2
  set S1 := ∑ a ∈ range K, u ^ a * v ^ (K - 1 - a)
  set S2 := ∑ b ∈ range K, ((u * v)⁻¹) ^ b
  have hd : (u + u⁻¹) / 2 - (v + v⁻¹) / 2 = (u - v) * (1 - (u * v)⁻¹) / 2 := by
    field_simp
    ring
  rw [hd]
  have : (u ^ K + (u⁻¹) ^ K) / 2 - (v ^ K + (v⁻¹) ^ K) / 2 =
      (S1 * (u - v)) * (1 - (u⁻¹) ^ K * (v⁻¹) ^ K) / 2 := by
    rw [h1]
    linear_combination (1 / 2 : ℂ) * (v⁻¹) ^ K * k1 - (1 / 2 : ℂ) * (u⁻¹) ^ K * k2
  rw [this]
  have h2' : (1 - (u⁻¹) ^ K * (v⁻¹) ^ K) = S2 * (1 - (u * v)⁻¹) := by
    linear_combination h2
  rw [h2']
  ring

/-- Existence of `u` with `|u| = exp G(w)`. -/
theorem exists_inv_add (w : ℂ) :
    ∃ u : ℂ, u ≠ 0 ∧ (u + u⁻¹) / 2 = w ∧ ‖u‖ = Real.exp (ellipseLog w) := by
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective w
  have hcos : Complex.cos θ = (Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))⁻¹) / 2 := by
    rw [← Complex.cosh_mul_I, cosh_def', ← Complex.exp_neg]
  have hH : ellipseLog (Complex.cos θ) = |θ.im| := by
    unfold ellipseLog ellipseH
    rw [← Complex.cosh_mul_I]
    have := norm_cosh_sub_one_add (θ * Complex.I)
    have hre : (θ * Complex.I).re = -θ.im := by simp
    rw [hre, Real.cosh_neg] at this
    rw [show (‖Complex.cosh (θ * Complex.I) - 1‖ + ‖Complex.cosh (θ * Complex.I) + 1‖) / 2 =
      Real.cosh θ.im by linarith, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg _)]
  rw [hH]
  have hn : ‖Complex.exp (θ * Complex.I)‖ = Real.exp (-θ.im) := by
    rw [Complex.norm_exp]; simp
  rcases le_or_gt θ.im 0 with h | h
  · refine ⟨Complex.exp (θ * Complex.I), Complex.exp_ne_zero _, hcos.symm, ?_⟩
    rw [hn, abs_of_nonpos h]
  · refine ⟨(Complex.exp (θ * Complex.I))⁻¹, inv_ne_zero (Complex.exp_ne_zero _), ?_, ?_⟩
    · rw [hcos, inv_inv, add_comm]
    · rw [norm_inv, hn, abs_of_pos h, ← Real.exp_neg, neg_neg]

theorem T_eval_eq_prod {J : ℕ} (hJ : 0 < J) (y : ℂ) :
    (Chebyshev.T ℂ (J : ℤ)).eval y = 2 ^ (J - 1) * ∏ c : Fin J, (y - ((chebX J c : ℝ) : ℂ)) := by
  have hT : Chebyshev.T ℂ (J : ℤ) = Polynomial.C ((2 : ℂ) ^ (J - 1)) *
      ∏ c : Fin J, (X - Polynomial.C ((chebX J c : ℝ) : ℂ)) := by
    rw [← Chebyshev.map_T (algebraMap ℝ ℂ), T_eq_nodal hJ, Polynomial.map_mul,
      Polynomial.map_prod]
    simp
  rw [hT, eval_mul, eval_C, eval_prod]
  simp

theorem cheb_den_ge' {J : ℕ} (a : Fin J) :
    (J : ℝ) / 2 ^ (J - 1) ≤ |∏ c ∈ univ.erase a, (chebX J a - chebX J c)| := by
  have h := chebNode_den_ge a
  have hcard : (univ.erase a).card = J - 1 := by simp
  have hc : ∀ c, chebNode J a - chebNode J c = (chebX J a - chebX J c) / 2 := by
    intro c; simp only [chebNode]; ring
  rw [prod_congr rfl (fun c _ => hc c), prod_div_distrib, prod_const, hcard,
    abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (J - 1))] at h
  have hp : (0 : ℝ) < 2 ^ (J - 1) := by positivity
  calc (J : ℝ) / 2 ^ (J - 1) = ((J : ℝ) / (2 ^ (J - 1) * 2 ^ (J - 1))) * 2 ^ (J - 1) := by
        field_simp
    _ ≤ (|∏ c ∈ univ.erase a, (chebX J a - chebX J c)| / 2 ^ (J - 1)) * 2 ^ (J - 1) := by
        gcongr
    _ = _ := by field_simp

/-- Fact 3: the Lagrange basis of the Chebyshev nodes, for every complex argument. -/
theorem norm_lagrange_cheb_le {K : ℕ} (j : Fin K) (y : ℂ) :
    ‖∏ k ∈ univ.erase j, ((y - ((chebX K k : ℝ) : ℂ)) /
        (((chebX K j : ℝ) : ℂ) - ((chebX K k : ℝ) : ℂ)))‖ ≤
      K * Real.exp (((K : ℝ) - 1) * ellipseLog y) := by
  have hK : 0 < K := by have := j.isLt; omega
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hxinj : ∀ k, k ≠ j → ((chebX K j : ℝ) : ℂ) - ((chebX K k : ℝ) : ℂ) ≠ 0 := by
    intro k hk h
    apply hk
    apply chebX_injective K
    have := sub_eq_zero.mp h
    exact_mod_cast this.symm
  by_cases hyj : y = ((chebX K j : ℝ) : ℂ)
  · have : ∏ k ∈ univ.erase j, ((y - ((chebX K k : ℝ) : ℂ)) /
        (((chebX K j : ℝ) : ℂ) - ((chebX K k : ℝ) : ℂ))) = 1 := by
      apply prod_eq_one
      intro k hk
      rw [hyj]
      exact div_self (hxinj k (mem_erase.mp hk).1)
    rw [this, norm_one]
    have h2 : 1 ≤ Real.exp (((K : ℝ) - 1) * ellipseLog y) :=
      Real.one_le_exp (mul_nonneg (by linarith) (ellipseLog_nonneg y))
    nlinarith
  · obtain ⟨u, hu0, hu, hun⟩ := exists_inv_add y
    set v : ℂ := Complex.exp (((chebAngle K j : ℝ) : ℂ) * Complex.I) with hv
    have hv0 : v ≠ 0 := Complex.exp_ne_zero _
    have hvn : ‖v‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hvx : (v + v⁻¹) / 2 = ((chebX K j : ℝ) : ℂ) := by
      rw [hv, ← cos_eq_exp_inv, chebX, Complex.ofReal_cos]
    have hu1 : 1 ≤ ‖u‖ := by rw [hun]; exact Real.one_le_exp (ellipseLog_nonneg y)
    have hdd := cheb_divdiff hu0 hv0 K
    rw [hu, hvx] at hdd
    have hT0 : (Chebyshev.T ℂ (K : ℤ)).eval ((chebX K j : ℝ) : ℂ) = 0 := by
      rw [T_eval_eq_prod hK]
      rw [prod_eq_zero (mem_univ j) (sub_self _), mul_zero]
    rw [hT0, sub_zero] at hdd
    set S1 := ∑ a ∈ range K, u ^ a * v ^ (K - 1 - a) with hS1
    set S2 := ∑ b ∈ range K, ((u * v)⁻¹) ^ b with hS2
    have hne : y - ((chebX K j : ℝ) : ℂ) ≠ 0 := sub_ne_zero.mpr hyj
    set N := ∏ k ∈ univ.erase j, (y - ((chebX K k : ℝ) : ℂ)) with hN
    have hP : ∏ c : Fin K, (y - ((chebX K c : ℝ) : ℂ)) = (y - ((chebX K j : ℝ) : ℂ)) * N := by
      rw [hN]; exact (mul_prod_erase _ (fun c => y - ((chebX K c : ℝ) : ℂ)) (mem_univ j)).symm
    have hNeq : (2 : ℂ) ^ (K - 1) * N = S1 * S2 := by
      apply mul_left_cancel₀ hne
      rw [T_eval_eq_prod hK, hP] at hdd
      linear_combination hdd
    have hS1n : ‖S1‖ ≤ K * ‖u‖ ^ (K - 1) := by
      calc ‖S1‖ ≤ ∑ a ∈ range K, ‖u ^ a * v ^ (K - 1 - a)‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ range K, ‖u‖ ^ (K - 1) := by
          apply sum_le_sum
          intro a ha
          rw [norm_mul, norm_pow, norm_pow, hvn, one_pow, mul_one]
          exact pow_le_pow_right₀ hu1 (by have := mem_range.mp ha; omega)
        _ = K * ‖u‖ ^ (K - 1) := by simp
    have hS2n : ‖S2‖ ≤ K := by
      calc ‖S2‖ ≤ ∑ b ∈ range K, ‖((u * v)⁻¹) ^ b‖ := norm_sum_le _ _
        _ ≤ ∑ b ∈ range K, (1 : ℝ) := by
          apply sum_le_sum
          intro b _
          rw [norm_pow, norm_inv, norm_mul, hvn, mul_one]
          exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
        _ = K := by simp
    have hNn : ‖N‖ * 2 ^ (K - 1) ≤ K * ‖u‖ ^ (K - 1) * K := by
      have := congrArg norm hNeq
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat] at this
      calc ‖N‖ * 2 ^ (K - 1) = 2 ^ (K - 1) * ‖N‖ := by ring
        _ = ‖S1‖ * ‖S2‖ := this
        _ ≤ (K * ‖u‖ ^ (K - 1)) * K := by gcongr
    -- the denominator
    set D := ∏ k ∈ univ.erase j, (((chebX K j : ℝ) : ℂ) - ((chebX K k : ℝ) : ℂ)) with hD
    have hDr : ‖D‖ = |∏ k ∈ univ.erase j, (chebX K j - chebX K k)| := by
      have : D = (((∏ k ∈ univ.erase j, (chebX K j - chebX K k) : ℝ)) : ℂ) := by
        rw [hD]; push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hDge := cheb_den_ge' j
    rw [← hDr] at hDge
    have hp : (0 : ℝ) < 2 ^ (K - 1) := by positivity
    have hDpos : 0 < ‖D‖ := lt_of_lt_of_le (by positivity) hDge
    rw [prod_div_distrib, norm_div]
    change ‖N‖ / ‖D‖ ≤ _
    rw [div_le_iff₀ hDpos]
    have hexp : ‖u‖ ^ (K - 1) = Real.exp (((K : ℝ) - 1) * ellipseLog y) := by
      rw [hun, ← Real.exp_nat_mul]
      congr 1
      rw [Nat.cast_sub hK, Nat.cast_one]
    rw [← hexp]
    have hpos : 0 ≤ ‖u‖ ^ (K - 1) := by positivity
    have h3 : (K : ℝ) / 2 ^ (K - 1) ≤ ‖D‖ := hDge
    calc ‖N‖ = (‖N‖ * 2 ^ (K - 1)) / 2 ^ (K - 1) := by field_simp
      _ ≤ (K * ‖u‖ ^ (K - 1) * K) / 2 ^ (K - 1) := by gcongr
      _ = (K * ‖u‖ ^ (K - 1)) * ((K : ℝ) / 2 ^ (K - 1)) := by ring
      _ ≤ (K * ‖u‖ ^ (K - 1)) * ‖D‖ := by gcongr

/-! ## Interval nodes (GP §4.1, Theorem 4.1) -/

/-- Affine coordinate of the interval `[lo, hi]`: `ℓ(z) = (2z - lo - hi)/(hi - lo)`. -/
def ivlCoord (lo hi : ℝ) (z : ℂ) : ℂ := (2 * z - ((lo + hi : ℝ) : ℂ)) / ((hi - lo : ℝ) : ℂ)

/-- The Green function of the interval, `G ∘ ℓ`, with `G = ellipseLog`. -/
def ivlGreen (lo hi : ℝ) (z : ℂ) : ℝ := ellipseLog (ivlCoord lo hi z)

/-- The `j`-th Chebyshev node of `[lo, hi]` among `K`. -/
def ivlNode (lo hi : ℝ) (K : ℕ) (j : Fin K) : ℝ := (lo + hi) / 2 + (hi - lo) / 2 * chebX K j

theorem ivlCoord_sub {lo hi : ℝ} (hlt : lo < hi) (z : ℂ) (x : ℝ) :
    z - (((lo + hi) / 2 + (hi - lo) / 2 * x : ℝ) : ℂ) =
      (((hi - lo) / 2 : ℝ) : ℂ) * (ivlCoord lo hi z - (x : ℂ)) := by
  have h : ((hi - lo : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr hlt).ne'
  unfold ivlCoord
  push_cast at h ⊢
  field_simp
  ring

theorem ivlCoord_node {lo hi : ℝ} (hlt : lo < hi) (x : ℝ) :
    ivlCoord lo hi (((lo + hi) / 2 + (hi - lo) / 2 * x : ℝ) : ℂ) = (x : ℂ) := by
  have h : ((hi - lo : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr hlt).ne'
  unfold ivlCoord
  push_cast at h ⊢
  field_simp
  ring

theorem ivlCoord_ofReal (lo hi t : ℝ) :
    ivlCoord lo hi (t : ℂ) = (((2 * t - (lo + hi)) / (hi - lo) : ℝ) : ℂ) := by
  unfold ivlCoord
  push_cast
  rfl

theorem ivlNode_mem {lo hi : ℝ} (hlt : lo < hi) (K : ℕ) (j : Fin K) :
    ivlNode lo hi K j ∈ Ioo lo hi := by
  have hx := chebX_mem j
  unfold ivlNode
  constructor <;> nlinarith [hx.1, hx.2, sub_pos.mpr hlt]

theorem ivlNode_injective {lo hi : ℝ} (hlt : lo < hi) (K : ℕ) :
    Function.Injective (ivlNode lo hi K) := by
  intro i j hij
  apply chebX_injective K
  unfold ivlNode at hij
  have : (hi - lo) / 2 * chebX K i = (hi - lo) / 2 * chebX K j := by linarith
  exact mul_left_cancel₀ (by linarith : (hi - lo) / 2 ≠ 0) this

theorem abs_ivlCoord_ge_one {lo hi t : ℝ} (hlt : lo < hi) (ht : t ∉ Ioo lo hi) :
    1 ≤ |(2 * t - (lo + hi)) / (hi - lo)| := by
  have hp : 0 < hi - lo := sub_pos.mpr hlt
  rw [abs_div, abs_of_pos hp, le_div_iff₀ hp, one_mul]
  by_cases h1 : t ≤ lo
  · rw [abs_of_nonpos (by linarith)]; linarith
  · have h2 : hi ≤ t := by
      by_contra h2
      exact ht ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩
    rw [abs_of_nonneg (by linarith)]; linarith

theorem abs_ivlCoord_le_one {lo hi t : ℝ} (hlt : lo < hi) (ht : t ∈ Ioo lo hi) :
    |(2 * t - (lo + hi)) / (hi - lo)| ≤ 1 := by
  have hp : 0 < hi - lo := sub_pos.mpr hlt
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nodes of a system of intervals, indexed by `Σ c, Fin (K c)`. -/
def nodeSys (lo hi : ι → ℝ) (K : ι → ℕ) : (Σ c, Fin (K c)) → ℝ :=
  fun s => ivlNode (lo s.1) (hi s.1) (K s.1) s.2

/-- `Λ(z) = Σ_c K_c G_c(z)`. -/
def ivlLam (lo hi : ι → ℝ) (K : ι → ℕ) (z : ℂ) : ℝ :=
  ∑ c, (K c : ℝ) * ivlGreen (lo c) (hi c) z

/-- The ratio of two nodal products of one interval, at a point of `|ℓ| ≥ 1`. -/
theorem norm_nodal_ratio_le {lo hi : ℝ} (hlt : lo < hi) (K : ℕ) (z : ℂ) {t : ℝ}
    (ht : t ∉ Ioo lo hi) :
    ‖∏ j : Fin K, ((z - ((ivlNode lo hi K j : ℝ) : ℂ)) /
        ((t : ℂ) - ((ivlNode lo hi K j : ℝ) : ℂ)))‖ ≤
      2 * Real.exp ((K : ℝ) * (ivlGreen lo hi z - ivlGreen lo hi (t : ℂ))) := by
  have hh : (((hi - lo) / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith : (hi - lo) / 2 ≠ 0)
  have hfac : ∀ j : Fin K, (z - ((ivlNode lo hi K j : ℝ) : ℂ)) /
        ((t : ℂ) - ((ivlNode lo hi K j : ℝ) : ℂ)) =
      (ivlCoord lo hi z - (chebX K j : ℂ)) / (ivlCoord lo hi (t : ℂ) - (chebX K j : ℂ)) := by
    intro j
    unfold ivlNode
    rw [ivlCoord_sub hlt, ivlCoord_sub hlt]
    exact mul_div_mul_left _ _ hh
  have hy2 : 1 ≤ |(2 * t - (lo + hi)) / (hi - lo)| := abs_ivlCoord_ge_one hlt ht
  set y1 := ivlCoord lo hi z
  set y2 : ℝ := (2 * t - (lo + hi)) / (hi - lo) with hy2def
  have hy2c : ivlCoord lo hi (t : ℂ) = (y2 : ℂ) := ivlCoord_ofReal lo hi t
  simp_rw [hfac, hy2c]
  rw [prod_div_distrib]
  have hlow := half_exp_le_norm_T_ofReal K hy2
  have hup := norm_T_eval_le_exp_ellipseLog K y1
  have hGt : ivlGreen lo hi (t : ℂ) = ellipseLog (y2 : ℂ) := by
    unfold ivlGreen; rw [hy2c]
  rw [hGt]
  have hpos : 0 < (1 / 2 : ℝ) * Real.exp ((K : ℝ) * ellipseLog (y2 : ℂ)) := by positivity
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp
  have e1 := T_eval_eq_prod hK y1
  have e2 := T_eval_eq_prod hK (y2 : ℂ)
  have h2pow : (2 : ℂ) ^ (K - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hT2 : (Chebyshev.T ℂ (K : ℤ)).eval (y2 : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    linarith
  have hratio : (∏ j : Fin K, (y1 - (chebX K j : ℂ))) / ∏ j : Fin K, ((y2 : ℂ) - (chebX K j : ℂ)) =
      (Chebyshev.T ℂ (K : ℤ)).eval y1 / (Chebyshev.T ℂ (K : ℤ)).eval (y2 : ℂ) := by
    rw [e1, e2]
    rw [mul_div_mul_left _ _ h2pow]
  rw [hratio, norm_div, div_le_iff₀ (lt_of_lt_of_le hpos hlow)]
  calc ‖(Chebyshev.T ℂ (K : ℤ)).eval y1‖ ≤ Real.exp ((K : ℝ) * ellipseLog y1) := hup
    _ = 2 * Real.exp ((K : ℝ) * (ellipseLog y1 - ellipseLog (y2 : ℂ))) *
          ((1 / 2) * Real.exp ((K : ℝ) * ellipseLog (y2 : ℂ))) := by
        rw [mul_sub, Real.exp_sub]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

theorem eval_basis_univ {α : Type*} [Fintype α] [DecidableEq α] (τ : α → ℝ) (a : α) (z : ℂ) :
    ((Lagrange.basis (univ : Finset α) τ a).map (algebraMap ℝ ℂ)).eval z =
      ∏ k ∈ univ.erase a, ((z - (τ k : ℂ)) / ((τ a : ℂ) - (τ k : ℂ))) := by
  unfold Lagrange.basis
  rw [Polynomial.map_prod, eval_prod]
  apply prod_congr rfl
  intro k _
  simp only [Lagrange.basisDivisor, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub,
    Polynomial.map_X, eval_mul, eval_C, eval_sub, eval_X]
  push_cast
  rw [div_eq_inv_mul]
  simp

theorem sigma_prod_bound (lo hi : ι → ℝ) (K : ι → ℕ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c')))
    (c0 : ι) (j0 : Fin (K c0)) (z : ℂ) :
    ‖∏ k ∈ univ.erase (⟨c0, j0⟩ : Σ c, Fin (K c)),
        ((z - ((nodeSys lo hi K k : ℝ) : ℂ)) /
          (((nodeSys lo hi K ⟨c0, j0⟩ : ℝ) : ℂ) - ((nodeSys lo hi K k : ℝ) : ℂ)))‖ ≤
      (K c0 : ℝ) * 2 ^ (Fintype.card ι - 1) *
        Real.exp (ivlLam lo hi K z - ivlLam lo hi K ((nodeSys lo hi K ⟨c0, j0⟩ : ℝ) : ℂ)) := by
  set t : ℝ := nodeSys lo hi K ⟨c0, j0⟩ with ht
  have htmem : t ∈ Ioo (lo c0) (hi c0) := ivlNode_mem (hlt c0) _ _
  let f : (Σ c, Fin (K c)) → ℂ := fun k =>
    (z - ((nodeSys lo hi K k : ℝ) : ℂ)) / ((t : ℂ) - ((nodeSys lo hi K k : ℝ) : ℂ))
  let g : (Σ c, Fin (K c)) → ℂ := fun k => if k = ⟨c0, j0⟩ then 1 else f k
  have h1 : ∏ k ∈ univ.erase (⟨c0, j0⟩ : Σ c, Fin (K c)), f k = ∏ k, g k := by
    rw [← prod_erase univ (f := g) (a := (⟨c0, j0⟩ : Σ c, Fin (K c))) (by simp [g])]
    apply prod_congr rfl
    intro k hk
    simp [g, (mem_erase.mp hk).1]
  change ‖∏ k ∈ univ.erase (⟨c0, j0⟩ : Σ c, Fin (K c)), f k‖ ≤ _
  rw [h1, Fintype.prod_sigma, ← mul_prod_erase univ _ (mem_univ c0), norm_mul,
    norm_prod (univ.erase c0) (fun c => ∏ j : Fin (K c), g ⟨c, j⟩)]
  -- the own interval
  have hG0 : ivlGreen (lo c0) (hi c0) (t : ℂ) = 0 := by
    unfold ivlGreen
    rw [ivlCoord_ofReal]
    exact ellipseLog_ofReal_of_abs_le_one (abs_ivlCoord_le_one (hlt c0) htmem)
  have hown : ‖∏ j : Fin (K c0), g ⟨c0, j⟩‖ ≤
      (K c0 : ℝ) * Real.exp ((K c0 : ℝ) * ivlGreen (lo c0) (hi c0) z) := by
    have hh : (((hi c0 - lo c0) / 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [hlt c0] : (hi c0 - lo c0) / 2 ≠ 0)
    have e1 : ∏ j : Fin (K c0), g ⟨c0, j⟩ =
        ∏ j ∈ univ.erase j0, ((ivlCoord (lo c0) (hi c0) z - (chebX (K c0) j : ℂ)) /
          ((chebX (K c0) j0 : ℂ) - (chebX (K c0) j : ℂ))) := by
      rw [← prod_erase univ (f := fun j : Fin (K c0) => g ⟨c0, j⟩) (a := j0) (by simp [g])]
      apply prod_congr rfl
      intro j hj
      have hjj : j ≠ j0 := (mem_erase.mp hj).1
      have hne : (⟨c0, j⟩ : Σ c, Fin (K c)) ≠ ⟨c0, j0⟩ := by
        intro h; exact hjj (by simpa using h)
      simp only [g, if_neg hne, f, nodeSys, ht, ivlNode]
      rw [ivlCoord_sub (hlt c0), show ((lo c0 + hi c0) / 2 + (hi c0 - lo c0) / 2 * chebX (K c0) j0 : ℝ) =
        (lo c0 + hi c0) / 2 + (hi c0 - lo c0) / 2 * chebX (K c0) j0 from rfl]
      have := ivlCoord_sub (hlt c0) (((lo c0 + hi c0) / 2 + (hi c0 - lo c0) / 2 * chebX (K c0) j0 : ℝ) : ℂ)
        (chebX (K c0) j)
      rw [this, ivlCoord_node (hlt c0)]
      exact mul_div_mul_left _ _ hh
    rw [e1]
    have h3 := norm_lagrange_cheb_le j0 (ivlCoord (lo c0) (hi c0) z)
    refine h3.trans ?_
    have hK : (0 : ℝ) ≤ K c0 := Nat.cast_nonneg _
    have hG := ellipseLog_nonneg (ivlCoord (lo c0) (hi c0) z)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
    unfold ivlGreen
    nlinarith [hG]
  have hoth : ∀ c ∈ univ.erase c0, ‖∏ j : Fin (K c), g ⟨c, j⟩‖ ≤
      2 * Real.exp ((K c : ℝ) * (ivlGreen (lo c) (hi c) z - ivlGreen (lo c) (hi c) (t : ℂ))) := by
    intro c hc
    have hcc : c ≠ c0 := (mem_erase.mp hc).1
    have htn : t ∉ Ioo (lo c) (hi c) := fun h =>
      Set.disjoint_left.mp (hdisj c0 c hcc.symm) htmem h
    have e1 : ∏ j : Fin (K c), g ⟨c, j⟩ = ∏ j : Fin (K c),
        ((z - ((ivlNode (lo c) (hi c) (K c) j : ℝ) : ℂ)) /
          ((t : ℂ) - ((ivlNode (lo c) (hi c) (K c) j : ℝ) : ℂ))) := by
      apply prod_congr rfl
      intro j _
      have hne : (⟨c, j⟩ : Σ c, Fin (K c)) ≠ ⟨c0, j0⟩ := by
        intro h; exact hcc (by simpa using congrArg Sigma.fst h)
      simp only [g, if_neg hne, f, nodeSys]
    rw [e1]
    exact norm_nodal_ratio_le (hlt c) (K c) z htn
  have hprod : ∏ c ∈ univ.erase c0, ‖∏ j : Fin (K c), g ⟨c, j⟩‖ ≤
      ∏ c ∈ univ.erase c0, (2 * Real.exp ((K c : ℝ) *
        (ivlGreen (lo c) (hi c) z - ivlGreen (lo c) (hi c) (t : ℂ)))) :=
    prod_le_prod₀ (fun c _ => norm_nonneg _) hoth
  have hexp : ∏ c ∈ univ.erase c0, (2 * Real.exp ((K c : ℝ) *
        (ivlGreen (lo c) (hi c) z - ivlGreen (lo c) (hi c) (t : ℂ)))) =
      2 ^ (Fintype.card ι - 1) * Real.exp (∑ c ∈ univ.erase c0, (K c : ℝ) *
        (ivlGreen (lo c) (hi c) z - ivlGreen (lo c) (hi c) (t : ℂ))) := by
    rw [prod_mul_distrib, prod_const, Real.exp_sum, card_erase_of_mem (mem_univ c0), card_univ]
  have hΛ : ivlLam lo hi K z - ivlLam lo hi K (t : ℂ) =
      (K c0 : ℝ) * ivlGreen (lo c0) (hi c0) z + ∑ c ∈ univ.erase c0, (K c : ℝ) *
        (ivlGreen (lo c) (hi c) z - ivlGreen (lo c) (hi c) (t : ℂ)) := by
    unfold ivlLam
    rw [← add_sum_erase univ _ (mem_univ c0), ← add_sum_erase univ _ (mem_univ c0), hG0]
    simp only [mul_sub, sum_sub_distrib]
    ring
  rw [hΛ, Real.exp_add]
  calc ‖∏ j : Fin (K c0), g ⟨c0, j⟩‖ * ∏ c ∈ univ.erase c0, ‖∏ j : Fin (K c), g ⟨c, j⟩‖
      ≤ ((K c0 : ℝ) * Real.exp ((K c0 : ℝ) * ivlGreen (lo c0) (hi c0) z)) *
          (2 ^ (Fintype.card ι - 1) * Real.exp (∑ c ∈ univ.erase c0, (K c : ℝ) *
            (ivlGreen (lo c) (hi c) z - ivlGreen (lo c) (hi c) (t : ℂ)))) := by
        rw [← hexp]
        exact mul_le_mul hown hprod (prod_nonneg fun c _ => norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **G04** (GP Theorem 4.1, Bernstein-Walsh free): the Lagrange basis of the interval nodes. -/
theorem lagrange_basis_le {α : Type*} [Fintype α] [DecidableEq α]
    (lo hi : ι → ℝ) (K : ι → ℕ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c')))
    (e : α ≃ Σ c, Fin (K c)) (τ : α → ℝ) (hτ : ∀ a, τ a = nodeSys lo hi K (e a))
    (a : α) (z : ℂ) :
    ‖((Lagrange.basis (univ : Finset α) τ a).map (algebraMap ℝ ℂ)).eval z‖ ≤
      (K (e a).1 : ℝ) * 2 ^ (Fintype.card ι - 1) *
        Real.exp (ivlLam lo hi K z - ivlLam lo hi K ((τ a : ℝ) : ℂ)) := by
  rw [eval_basis_univ]
  have hprod : ∏ k ∈ univ.erase a, ((z - (τ k : ℂ)) / ((τ a : ℂ) - (τ k : ℂ))) =
      ∏ s ∈ univ.erase (e a), ((z - ((nodeSys lo hi K s : ℝ) : ℂ)) /
        (((nodeSys lo hi K (e a) : ℝ) : ℂ) - ((nodeSys lo hi K s : ℝ) : ℂ))) := by
    apply Finset.prod_equiv e
    · intro i
      simp [e.injective.ne_iff]
    · intro i _
      rw [hτ i, hτ a]
  rw [hprod, hτ a]
  obtain ⟨c0, j0⟩ := e a
  exact sigma_prod_bound lo hi K hlt hdisj c0 j0 z

/-! ## G05: the weighted-atom form (GP Corollary 4.2) -/

/-- `L(z) = ½ Σ_c (G_c(z) + log(w_c / 4))`, `w_c = hi_c - lo_c`. -/
def ivlL (lo hi : ι → ℝ) (z : ℂ) : ℝ :=
  (1 / 2) * ∑ c, (ivlGreen (lo c) (hi c) z + Real.log ((hi c - lo c) / 4))

theorem continuous_ivlGreen (lo hi : ℝ) : Continuous (ivlGreen lo hi) := by
  unfold ivlGreen ivlCoord
  exact continuous_ellipseLog.comp (by fun_prop)

theorem ivlGreen_nonneg (lo hi : ℝ) (z : ℂ) : 0 ≤ ivlGreen lo hi z := ellipseLog_nonneg _

theorem exists_bound_sum_green (lo hi : ι → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ∑ c, ivlGreen (lo c) (hi c) w ≤ B := by
  have hc : Continuous (fun w : ℂ => ∑ c, ivlGreen (lo c) (hi c) w) :=
    continuous_finsetSum _ fun c _ => continuous_ivlGreen (lo c) (hi c)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hc.continuousOn
  refine ⟨max 0 B, le_max_left _ _, fun w hw => ?_⟩
  exact (hB (Set.mem_image_of_mem _ (by simpa using hw))).trans (le_max_right _ _)

theorem lagrange_basis_le_L (lo hi : ι → ℝ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c'))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (K : ι → ℕ), (∀ c, 2 * K c ≤ N + 1 ∧ N ≤ 2 * K c + 1) →
      ∀ (α : Type) [Fintype α] [DecidableEq α] (e : α ≃ Σ c, Fin (K c)) (τ : α → ℝ),
        (∀ a, τ a = nodeSys lo hi K (e a)) → (∀ a, |τ a| ≤ 1) → ∀ (a : α) (z : ℂ), ‖z‖ ≤ 1 →
        ‖((Lagrange.basis (univ : Finset α) τ a).map (algebraMap ℝ ℂ)).eval z‖ ≤
          C * N * Real.exp ((N : ℝ) * (ivlL lo hi z - ivlL lo hi ((τ a : ℝ) : ℂ))) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_sum_green lo hi
  refine ⟨2 ^ (Fintype.card ι - 1) * Real.exp B, by positivity, ?_⟩
  intro N K hK α _ _ e τ hτ hτ1 a z hz
  have h4 := lagrange_basis_le lo hi K hlt hdisj e τ hτ a z
  refine h4.trans ?_
  set t : ℝ := τ a with ht
  have htB : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hτ1 a
  have hSz := hB z hz
  have hSt := hB (t : ℂ) htB
  have hKup : ∀ c, (K c : ℝ) ≤ (N : ℝ) / 2 + 1 / 2 := by
    intro c; have := (hK c).1; have : (2 * K c : ℝ) ≤ N + 1 := by exact_mod_cast this
    linarith
  have hKlo : ∀ c, (N : ℝ) / 2 - 1 / 2 ≤ K c := by
    intro c; have := (hK c).2; have : (N : ℝ) ≤ 2 * K c + 1 := by exact_mod_cast this
    linarith
  have hΛ1 : ivlLam lo hi K z ≤ ((N : ℝ) / 2 + 1 / 2) * ∑ c, ivlGreen (lo c) (hi c) z := by
    unfold ivlLam
    rw [mul_sum]
    exact sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_right (hKup c) (ivlGreen_nonneg _ _ _)
  have hΛ2 : ((N : ℝ) / 2 - 1 / 2) * ∑ c, ivlGreen (lo c) (hi c) (t : ℂ) ≤
      ivlLam lo hi K (t : ℂ) := by
    unfold ivlLam
    rw [mul_sum]
    exact sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_right (hKlo c) (ivlGreen_nonneg _ _ _)
  have hL : (N : ℝ) * (ivlL lo hi z - ivlL lo hi (t : ℂ)) =
      ((N : ℝ) / 2) * (∑ c, ivlGreen (lo c) (hi c) z - ∑ c, ivlGreen (lo c) (hi c) (t : ℂ)) := by
    unfold ivlL
    rw [sum_add_distrib, sum_add_distrib]
    ring
  have hexp : ivlLam lo hi K z - ivlLam lo hi K (t : ℂ) ≤
      (N : ℝ) * (ivlL lo hi z - ivlL lo hi (t : ℂ)) + B := by
    rw [hL]
    nlinarith
  have hKN : (K (e a).1 : ℝ) ≤ N := by
    have := (hK (e a).1).1
    have : K (e a).1 ≤ N := by omega
    exact_mod_cast this
  calc (K (e a).1 : ℝ) * 2 ^ (Fintype.card ι - 1) * Real.exp (ivlLam lo hi K z - ivlLam lo hi K (t : ℂ))
      ≤ (N : ℝ) * 2 ^ (Fintype.card ι - 1) *
          Real.exp ((N : ℝ) * (ivlL lo hi z - ivlL lo hi (t : ℂ)) + B) := by
        gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-! ## G29: the pair rule and the `Fin (d₀ * N)` node map -/

theorem mem_Icc_of_abs_ivlCoord_le_one {lo hi t : ℝ} (hlt : lo < hi)
    (h : |(2 * t - (lo + hi)) / (hi - lo)| ≤ 1) : t ∈ Icc lo hi := by
  have hp : 0 < hi - lo := sub_pos.mpr hlt
  rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem nodeSys_injective (lo hi : ι → ℝ) (K : ι → ℕ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c'))) :
    Function.Injective (nodeSys lo hi K) := by
  rintro ⟨c, j⟩ ⟨c', j'⟩ h
  by_cases hcc : c = c'
  · subst hcc
    have := ivlNode_injective (hlt c) (K c) h
    exact congrArg (Sigma.mk c) this
  · exfalso
    have hm := ivlNode_mem (hlt c') (K c') j'
    rw [← show ivlNode (lo c) (hi c) (K c) j = ivlNode (lo c') (hi c') (K c') j' from h] at hm
    exact Set.disjoint_left.mp (hdisj c c' hcc) (ivlNode_mem (hlt c) _ _) hm

/-- Pair rule: the intervals `(i, 0)` and `(i, 1)` get `⌈N/2⌉` and `⌊N/2⌋` nodes. -/
def pairK {d₀ : ℕ} (N : ℕ) (c : Fin d₀ × Fin 2) : ℕ := if c.2 = 0 then (N + 1) / 2 else N / 2

theorem pairK_spec {d₀ : ℕ} (N : ℕ) (c : Fin d₀ × Fin 2) :
    2 * pairK N c ≤ N + 1 ∧ N ≤ 2 * pairK N c + 1 := by
  unfold pairK
  split_ifs <;> omega

theorem card_pair_sigma (d₀ N : ℕ) :
    Fintype.card (Σ c : Fin d₀ × Fin 2, Fin (pairK N c)) = d₀ * N := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have : ∀ i : Fin d₀, pairK N (i, 0) + pairK N (i, 1) = N := by
    intro i; unfold pairK; simp; omega
  simp [this]

/-- A fixed bijection `Fin (d₀ * N) ≃ Σ c, Fin (K_c)` (the node indexing is immaterial). -/
def pairEquiv (d₀ N : ℕ) : Fin (d₀ * N) ≃ Σ c : Fin d₀ × Fin 2, Fin (pairK N c) :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_pair_sigma])

/-- The node family `τ_N : Fin (d₀ * N) → ℝ`. -/
def tauI {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (N : ℕ) : Fin (d₀ * N) → ℝ :=
  fun a => nodeSys lo hi (pairK N) (pairEquiv d₀ N a)

theorem tauI_injective {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c'))) (N : ℕ) :
    Function.Injective (tauI lo hi N) :=
  (nodeSys_injective lo hi (pairK N) hlt hdisj).comp (pairEquiv d₀ N).injective

theorem tauI_mem_Ioo {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (N : ℕ) (a : Fin (d₀ * N)) :
    tauI lo hi N a ∈ Ioo (lo (pairEquiv d₀ N a).1) (hi (pairEquiv d₀ N a).1) :=
  ivlNode_mem (hlt _) _ _

theorem tauI_mem {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (hlo : ∀ c, -1 ≤ lo c) (hhi : ∀ c, hi c ≤ 1) (N : ℕ) (a : Fin (d₀ * N)) :
    tauI lo hi N a ∈ Ioo (-1 : ℝ) 1 := by
  have h := tauI_mem_Ioo lo hi hlt N a
  exact ⟨lt_of_le_of_lt (hlo _) h.1, lt_of_lt_of_le h.2 (hhi _)⟩

theorem tauI_ne_zero {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (hzero : ∀ c, 0 ∉ Ioo (lo c) (hi c)) (N : ℕ) (a : Fin (d₀ * N)) :
    tauI lo hi N a ≠ 0 := fun h =>
  hzero _ (h ▸ tauI_mem_Ioo lo hi hlt N a)

theorem tauI_support {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (Gt : ℝ → Prop) (hG : ∀ c, ∀ t ∈ Ioo (lo c) (hi c), Gt t) (N : ℕ) (a : Fin (d₀ * N)) :
    Gt (tauI lo hi N a) :=
  hG _ _ (tauI_mem_Ioo lo hi hlt N a)

/-- **G05 for the pair-rule nodes**: `|l_a(z)| ≤ C N exp(N (L(z) - L(τ_a)))` on `|z| ≤ 1`,
for the Lagrange basis of `tauI`, with `C` independent of `N` and `a`. -/
theorem quadBasis_tauI_le {d₀ : ℕ} (lo hi : Fin d₀ × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c')))
    (hlo : ∀ c, -1 ≤ lo c) (hhi : ∀ c, hi c ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin (d₀ * N)) (z : ℂ), ‖z‖ ≤ 1 →
      ‖((OAI.InternalCatalan.quadBasis (tauI lo hi N) a).map (algebraMap ℝ ℂ)).eval z‖ ≤
        C * N * Real.exp ((N : ℝ) * (ivlL lo hi z - ivlL lo hi ((tauI lo hi N a : ℝ) : ℂ))) := by
  obtain ⟨C, hC, h⟩ := lagrange_basis_le_L lo hi hlt hdisj
  refine ⟨C, hC, fun N a z hz => ?_⟩
  exact h N (pairK N) (pairK_spec N) (Fin (d₀ * N)) (pairEquiv d₀ N) (tauI lo hi N)
    (fun _ => rfl) (fun a => abs_le.mpr ⟨(tauI_mem lo hi hlt hlo hhi N a).1.le,
      (tauI_mem lo hi hlt hlo hhi N a).2.le⟩) a z hz

/-! ## G07: the weight side (GP Proposition 4.4, audit repair R7) -/

section Weights

open Filter OAI.InternalCatalan CatalanMeasure.Parametric
open scoped Topology

/-- A real-line bound proved on `r ≤ |x| < 1` and on `|x| = r` extends to `|x| = 1`, by
continuity of the polynomial (audit repair R7: no hypothesis is needed at `x = ±1`). -/
theorem real_bound_extend (Q : ℝ[X]) {r B : ℝ} {e : ℕ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (h : ∀ x : ℝ, r ≤ |x| → (|x| < 1 ∨ |x| = r) → |Q.eval x| ≤ B * |x| ^ e) :
    ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 → |Q.eval x| ≤ B * |x| ^ e := by
  intro x hx hx1
  rcases lt_or_eq_of_le hx1 with hlt | heq
  · exact h x hx (Or.inl hlt)
  rcases lt_or_eq_of_le hr1 with hr | hr
  · -- r < 1: closure of `[r, 1)`
    have hxs : |x| = 1 := heq
    have hcl : IsClosed {s : ℝ | |Q.eval (s * x)| ≤ B * |s * x| ^ e} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : Set.Ico r 1 ⊆ {s : ℝ | |Q.eval (s * x)| ≤ B * |s * x| ^ e} := by
      intro s hs
      have hs0 : 0 < s := hr0.trans_le hs.1
      have habs : |s * x| = s := by rw [abs_mul, hxs, mul_one, abs_of_pos hs0]
      show |Q.eval (s * x)| ≤ B * |s * x| ^ e
      exact h (s * x) (by rw [habs]; exact hs.1) (Or.inl (by rw [habs]; exact hs.2))
    have h1 : (1 : ℝ) ∈ closure (Set.Ico r 1) := by
      rw [closure_Ico hr.ne]; exact ⟨hr.le, le_rfl⟩
    have := (closure_minimal hsub hcl) h1
    simpa [hxs] using this
  · exact h x hx (Or.inr (by rw [heq, hr]))

theorem nodal_weight_joint_le_open (P : Parameters) (hg : P.g0 ≤ P.n0)
    {N : ℕ} {τ : Fin ((P.n0 - P.g0) * N) → ℝ} (hτ : Function.Injective τ)
    (k : ℕ) (i : Fin ((P.n0 - P.g0) * N)) (g : ℂ → ℝ) {r B F : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hHQ : 0 < P.h N + P.q N)
    (hcard : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ ≤
        B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z))
    (hcirc : ∀ z : ℂ, ‖z‖ = r → CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g z ≤ F)
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| < 1 →
      CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g (x : ℂ) ≤ F) :
    |(rowCommonFactor P N).eval (τ i)| * |restrictedWeight P N k τ i| ≤
      4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) * (B * Real.exp F) := by
  have hpoint : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ 1 →
      CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g z ≤ F →
      ‖((((rowCommonFactor P N * quadBasis τ i) * (X - 1) ^ (P.q N)).map
        (algebraMap ℝ ℂ))).eval z‖ ≤ B * Real.exp F * ‖z‖ ^ (P.b N + k + P.q N) := by
    intro z hz0 hz1 hphi
    exact (CatalanMeasure.GenD.Analytic.filtered_basis_le_scaled_phi_all P N k _ g hB hz0.ne' hHQ
      (hcard z hz1)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphi) hB) (by positivity))
  let Q : ℝ[X] := (rowCommonFactor P N * quadBasis τ i) * (X - 1) ^ (P.q N)
  have hreal : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 →
      CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g (x : ℂ) ≤ F →
      |Q.eval x| ≤ B * Real.exp F * |x| ^ (P.b N + k + P.q N) := by
    intro x hx hx1 hphi
    have hx0 : 0 < |x| := hr0.trans_le hx
    have ht := hpoint (x : ℂ) (by simpa using hx0) (by simpa using hx1) hphi
    have he : (Q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
      rw [Polynomial.eval_map, show (x : ℂ) = algebraMap ℝ ℂ x from rfl,
        Polynomial.eval₂_at_apply]
      rfl
    change ‖(Q.map (algebraMap ℝ ℂ)).eval (x : ℂ)‖ ≤ _ at ht
    rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at ht
    exact ht
  have hext := real_bound_extend Q hr0 hr1 (B := B * Real.exp F) (e := P.b N + k + P.q N)
    (fun x hx hx' => by
      have hx1 : |x| ≤ 1 := by
        rcases hx' with h | h
        · exact h.le
        · rw [h]; exact hr1
      refine hreal x hx hx1 ?_
      rcases hx' with h | h
      · exact hseg x hx h
      · apply hcirc
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact h)
  have hfun := CatalanMeasure.GenD.Signed.Keyhole.polynomialFunctional_keyhole_le P N k
    (quadBasis τ i) (CatalanMeasure.GenD.Analytic.general_common_basis_coeff_zero P hg N hτ i)
    hr0 hr1
    (fun z hz => by simpa only [hz] using hpoint z (by rwa [hz]) (hz.trans_le hr1) (hcirc z hz))
    hext
  exact (CatalanMeasure.GenD.Analytic.restrictedWeight_joint_le_functional P N k τ i).trans
    (by simpa only [max_self] using hfun)

end Weights

section Weights2

open Filter OAI.InternalCatalan CatalanMeasure.Parametric
open scoped Topology

/-- **G07** (GP Proposition 4.4, with the repair R7 of the audit).  Let `P` be admissible,
`ζ ∈ (0,1)`, and `L : ℂ → ℝ` a function for which the nodes `τ_N` have cardinal bound
`|l_a(z)| ≤ C N exp(N (L(z) - L(τ_a)))` on `|z| ≤ 1` (G05 gives this for the interval nodes with
`L = ivlL`).  If

* (hcirc) `(h₀+q₀) log|1-z| + L(z) ≤ D` on `|z| = ζ`,
* (hseg) `(h₀+q₀) log|1-x| + L(x) - 2g₀ log ζ ≤ D` for real `ζ ≤ |x| < 1`,
* `-L(τ_a) ≤ C₀ + δ(τ_a)` at every node (any function `δ`),

then for every `w > C₀ + D - (n₀ - 2g₀) log ζ` and every `Cw > 0`, eventually in `N`,
`|common(τ_a)| |w_k(τ_a)| β_ζ(p,m,k) ≤ Cw N exp((w + δ(τ_a)) N)`, which is exactly the hypothesis
`hweights` of `weighted_atom_point_zeta_of_signed`.  The statement holds for every
`0 < ζ < 1` (the paper's `ζ ∈ [3/5, 1)` is a special case). -/
theorem hweights_of_cardinal_L (P : Parameters) (hP : Admissible P) {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (L : ℂ → ℝ)
    (τ : ∀ N : ℕ, Fin ((P.n0 - P.g0) * N) → ℝ) (hτ : ∀ N, Function.Injective (τ N))
    (C : ℝ) (hC : 0 ≤ C)
    (hcard : ∀ (N : ℕ) (a : Fin ((P.n0 - P.g0) * N)) (z : ℂ), ‖z‖ ≤ 1 →
      ‖((quadBasis (τ N) a).map (algebraMap ℝ ℂ)).eval z‖ ≤
        C * N * Real.exp ((N : ℝ) * (L z - L ((τ N a : ℝ) : ℂ))))
    (D C₀ w : ℝ) (δ : ℝ → ℝ)
    (hcirc : ∀ z : ℂ, ‖z‖ = ζ →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ + L z ≤ D)
    (hseg : ∀ x : ℝ, ζ ≤ |x| → |x| < 1 →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ + L (x : ℂ) -
        2 * (P.g0 : ℝ) * Real.log ζ ≤ D)
    (hC0 : ∀ (N : ℕ) (a : Fin ((P.n0 - P.g0) * N)), -L ((τ N a : ℝ) : ℂ) ≤ C₀ + δ (τ N a))
    (hw : C₀ + D - ((P.n0 : ℝ) - 2 * P.g0) * Real.log ζ < w) (Cw : ℝ) (hCw : 0 < Cw) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N → ∀ k : ℕ, k < P.n N →
      ∀ a : Fin ((P.n0 - P.g0) * N),
      |(rowCommonFactor P N).eval (τ N a)| * |restrictedWeight P N k (τ N) a| *
        CatalanMeasure.zetaBeta ζ p m k ≤ Cw * (N : ℝ) * Real.exp ((w + δ (τ N a)) * N) := by
  obtain ⟨hn0, hb0, hq0, hh0, hgn⟩ := hP
  have hg : P.g0 ≤ P.n0 := by omega
  have hd : 0 < P.n0 - P.g0 := by omega
  have hdR : (0 : ℝ) < ((P.n0 - P.g0 : ℕ) : ℝ) := by exact_mod_cast hd
  set Dn : ℕ := 1 + P.b0 + P.n0 + P.q0 with hDn
  set ε : ℝ := w - (C₀ + D - ((P.n0 : ℝ) - 2 * P.g0) * Real.log ζ) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set K1 : ℝ := 4 * (Dn : ℝ) * (ζ / (1 - ζ)) * C with hK1
  have hK10 : 0 ≤ K1 := by
    have : 0 < 1 - ζ := by linarith
    rw [hK1]; positivity
  filter_upwards [eventually_mul_pow_le_exp (K1 / Cw) 1 hε0, eventually_gt_atTop 0]
    with N hNexp hN p m hpm k hk a
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set t : ℝ := τ N a with ht
  set g : ℂ → ℝ := fun z => L z / ((P.n0 - P.g0 : ℕ) : ℝ) with hgdef
  set B : ℝ := C * N * Real.exp (-((N : ℝ) * L (t : ℂ))) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hHQ : 0 < P.h N + P.q N := by
    simp only [Parameters.h, Parameters.q]; positivity
  have hcard' : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖((quadBasis (τ N) a).map (algebraMap ℝ ℂ)).eval z‖ ≤
        B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z) := by
    intro z hz
    refine (hcard N a z hz).trans (le_of_eq ?_)
    have e1 : (((P.n0 - P.g0) * N : ℕ) : ℝ) * g z = (N : ℝ) * L z := by
      rw [hgdef]; push_cast; field_simp
    have e3 : Real.exp (-((N : ℝ) * L (t : ℂ))) * Real.exp ((N : ℝ) * L z) =
        Real.exp ((N : ℝ) * (L z - L (t : ℂ))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, hB, mul_assoc (C * (N : ℝ)), e3]
  set F : ℝ := (2 * (P.g0 : ℝ) * N - k) * Real.log ζ + (N : ℝ) * D with hF
  have hscaled : ∀ z : ℂ, CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g z =
      (2 * (P.g0 : ℝ) * N - k) * Real.log ‖z‖ +
        (N : ℝ) * (((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ + L z) := by
    intro z
    unfold CatalanMeasure.GenD.Analytic.scaledNodalPhi
    simp only [Parameters.g, Parameters.h, Parameters.q, hgdef]
    push_cast
    field_simp
    ring
  have hcirc' : ∀ z : ℂ, ‖z‖ = ζ →
      CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g z ≤ F := by
    intro z hz
    rw [hscaled, hz, hF]
    have := mul_le_mul_of_nonneg_left (hcirc z hz) hNR.le
    linarith
  have hseg' : ∀ x : ℝ, ζ ≤ |x| → |x| < 1 →
      CatalanMeasure.GenD.Analytic.scaledNodalPhi P N k g (x : ℂ) ≤ F := by
    intro x hx hx1
    rw [hscaled, hF, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hseg x hx hx1
    have hx0 : 0 < |x| := hζ0.trans_le hx
    have hu : Real.log ζ ≤ Real.log |x| := Real.log_le_log hζ0 hx
    have hu0 : Real.log |x| ≤ 0 := Real.log_nonpos hx0.le hx1.le
    have hkR : (k : ℝ) ≥ 0 := Nat.cast_nonneg k
    have hg0 : (0 : ℝ) ≤ 2 * (P.g0 : ℝ) * N := by positivity
    set X := ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ + L (x : ℂ) with hX
    have hX' : X ≤ D + 2 * (P.g0 : ℝ) * Real.log ζ := by linarith
    nlinarith [mul_nonneg hkR (sub_nonneg.mpr hu), mul_nonneg hg0 (neg_nonneg.mpr hu0),
      mul_le_mul_of_nonneg_left hX' hNR.le]
  have key := nodal_weight_joint_le_open P hg (hτ N) k a g hζ0 hζ1.le hB0 hHQ hcard' hcirc' hseg'
  have hcount : 1 + (P.b N + k + P.q N - P.A N) ≤ Dn * N := by
    have hsub := Nat.sub_le (P.b N + k + P.q N) (P.A N)
    rw [hDn]
    simp only [Nat.add_mul, Nat.one_mul]
    simp only [Parameters.b, Parameters.q, Parameters.n] at hk hsub ⊢
    omega
  have hJ : (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) ≤ (Dn : ℝ) * N := by
    exact_mod_cast hcount
  have hζr : 0 ≤ ζ / (1 - ζ) := by
    have : 0 < 1 - ζ := by linarith
    positivity
  have hz := zetaBeta_le_exp hζ0 hζ1 hpm hk
  have hzn := zetaBeta_nonneg hζ0 p m k
  have h1 := mul_le_mul_of_nonneg_left (hC0 N a) hNR.le
  have hE : -((N : ℝ) * L (t : ℂ)) + F + (((P.n N : ℕ) : ℝ) - k) * Real.log ζ⁻¹ ≤
      δ t * N + (w - ε) * N := by
    rw [Real.log_inv, hF, hε]
    simp only [Parameters.n]
    push_cast
    nlinarith [h1]
  have hKN : K1 * N ≤ Cw * Real.exp (ε * N) := by
    have := hNexp
    rw [pow_one, div_mul_eq_mul_div, div_le_iff₀ hCw] at this
    linarith
  have hexpF : 0 ≤ Real.exp F := (Real.exp_pos _).le
  calc _ ≤ (4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) * (B * Real.exp F)) *
        (ζ / (1 - ζ) * Real.exp ((((P.n N : ℕ) : ℝ) - k) * Real.log ζ⁻¹)) :=
        mul_le_mul key hz hzn (by positivity)
    _ ≤ (4 * ((Dn : ℝ) * N) * (B * Real.exp F)) *
        (ζ / (1 - ζ) * Real.exp ((((P.n N : ℕ) : ℝ) - k) * Real.log ζ⁻¹)) := by
        gcongr
    _ = K1 * (N : ℝ) ^ 2 * Real.exp (-((N : ℝ) * L (t : ℂ)) + F +
          (((P.n N : ℕ) : ℝ) - k) * Real.log ζ⁻¹) := by
        have hsplit : Real.exp (-((N : ℝ) * L (t : ℂ)) + F +
            (((P.n N : ℕ) : ℝ) - k) * Real.log ζ⁻¹) =
            Real.exp (-((N : ℝ) * L (t : ℂ))) * Real.exp F *
              Real.exp ((((P.n N : ℕ) : ℝ) - k) * Real.log ζ⁻¹) := by
          rw [Real.exp_add (-((N : ℝ) * L (t : ℂ)) + F), Real.exp_add (-((N : ℝ) * L (t : ℂ)))]
        rw [hsplit, hB, hK1]
        ring
    _ ≤ K1 * (N : ℝ) ^ 2 * Real.exp (δ t * N + (w - ε) * N) := by
        gcongr
    _ = (K1 * N) * (N * Real.exp (δ t * N + w * N)) * Real.exp (-(ε * N)) := by
        rw [show δ t * N + (w - ε) * N = (δ t * N + w * N) + -(ε * N) by ring, Real.exp_add]
        ring
    _ ≤ (Cw * Real.exp (ε * N)) * (N * Real.exp (δ t * N + w * N)) * Real.exp (-(ε * N)) := by
        gcongr
    _ = Cw * (N : ℝ) * Real.exp ((w + δ t) * N) := by
        rw [show (w + δ t) * N = δ t * N + w * N by ring]
        have : Real.exp (ε * N) * Real.exp (-(ε * N)) = 1 := by
          rw [← Real.exp_add]; simp
        calc (Cw * Real.exp (ε * N)) * (N * Real.exp (δ t * N + w * N)) * Real.exp (-(ε * N))
            = Cw * N * Real.exp (δ t * N + w * N) * (Real.exp (ε * N) * Real.exp (-(ε * N))) := by ring
          _ = _ := by rw [this, mul_one]

end Weights2

section Terminal

open Filter OAI.InternalCatalan CatalanMeasure.Parametric

/-- **G05 + G07 for the interval nodes `tauI`**: the hypothesis `hweights` of
`weighted_atom_point_zeta_of_signed`, from (hcirc), (hseg) for `L = ivlL`. -/
theorem hweights_tauI (P : Parameters) (hP : Admissible P) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (lo hi : Fin (P.n0 - P.g0) × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c')))
    (hlo : ∀ c, -1 ≤ lo c) (hhi : ∀ c, hi c ≤ 1)
    (D C₀ w : ℝ) (δ : ℝ → ℝ)
    (hcirc : ∀ z : ℂ, ‖z‖ = ζ →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ + ivlL lo hi z ≤ D)
    (hseg : ∀ x : ℝ, ζ ≤ |x| → |x| < 1 →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ + ivlL lo hi (x : ℂ) -
        2 * (P.g0 : ℝ) * Real.log ζ ≤ D)
    (hC0 : ∀ (N : ℕ) (a : Fin ((P.n0 - P.g0) * N)),
      -ivlL lo hi ((tauI lo hi N a : ℝ) : ℂ) ≤ C₀ + δ (tauI lo hi N a))
    (hw : C₀ + D - ((P.n0 : ℝ) - 2 * P.g0) * Real.log ζ < w) (Cw : ℝ) (hCw : 0 < Cw) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N → ∀ k : ℕ, k < P.n N →
      ∀ a : Fin ((P.n0 - P.g0) * N),
      |(rowCommonFactor P N).eval (tauI lo hi N a)| *
        |restrictedWeight P N k (tauI lo hi N) a| * CatalanMeasure.zetaBeta ζ p m k ≤
          Cw * (N : ℝ) * Real.exp ((w + δ (tauI lo hi N a)) * N) := by
  obtain ⟨C, hC, hcard⟩ := quadBasis_tauI_le lo hi hlt hdisj hlo hhi
  exact hweights_of_cardinal_L P hP hζ0 hζ1 (ivlL lo hi) (tauI lo hi)
    (tauI_injective lo hi hlt hdisj) C hC hcard D C₀ w δ hcirc hseg hC0 hw Cw hCw

/-- **Terminal trace** (rows 1, 2, 5 and 6 of the G terminal table): the interval nodes, with
(hcirc), (hseg), feed `weighted_atom_point_zeta_of_signed` and give
`WeightedAtomPointBinom P (5 Cw) (tauI lo hi) G target (r + w)`. -/
theorem weighted_atom_point_interval {target r w c₁ c₂ c₃ α₁ ζ : ℝ} (P : Parameters)
    (hP : Admissible P) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (Cw : ℝ) (hCw : 0 < Cw) (δ : ℝ → ℝ)
    (lo hi : Fin (P.n0 - P.g0) × Fin 2 → ℝ) (hlt : ∀ c, lo c < hi c)
    (hdisj : ∀ c c', c ≠ c' → Disjoint (Ioo (lo c) (hi c)) (Ioo (lo c') (hi c')))
    (hlo : ∀ c, -1 ≤ lo c) (hhi : ∀ c, hi c ≤ 1) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hNd : ∀ N m (y : Fin m → ℝ) (a : Fin m → Fin ((P.n0 - P.g0) * N)), Function.Injective a →
      (∀ j, realCoordinateInv (y j) = tauI lo hi N (a j)) → Nd N m y)
    (hfirst : FreeFirstBoundZ P G ζ δ target c₁)
    (hnear : FreeNearBoundZ P G Nd ζ δ target c₂ α₁)
    (hlarge : FreeLargeBoundZ P G ζ δ target c₃ α₁)
    (hc₁ : c₁ ≤ r) (hc₂ : c₂ ≤ r) (hc₃ : c₃ ≤ r)
    (D C₀ : ℝ)
    (hcirc : ∀ z : ℂ, ‖z‖ = ζ →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ + ivlL lo hi z ≤ D)
    (hseg : ∀ x : ℝ, ζ ≤ |x| → |x| < 1 →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - (x : ℂ)‖ + ivlL lo hi (x : ℂ) -
        2 * (P.g0 : ℝ) * Real.log ζ ≤ D)
    (hC0 : ∀ (N : ℕ) (a : Fin ((P.n0 - P.g0) * N)),
      -ivlL lo hi ((tauI lo hi N a : ℝ) : ℂ) ≤ C₀ + δ (tauI lo hi N a))
    (hw : C₀ + D - ((P.n0 : ℝ) - 2 * P.g0) * Real.log ζ < w) :
    WeightedAtomPointBinom P (5 * Cw) (tauI lo hi) G target (r + w) :=
  weighted_atom_point_zeta_of_signed P hP hζ0 Cw hCw.le δ (tauI lo hi) G Nd hNd hfirst hnear
    hlarge hc₁ hc₂ hc₃
    (hweights_tauI P hP hζ0 hζ1 lo hi hlt hdisj hlo hhi D C₀ w δ hcirc hseg hC0 hw Cw hCw)

end Terminal

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.lagrange_basis_le
#print axioms CatalanMeasure.GenD.Signed.RouteI.lagrange_basis_le_L
#print axioms CatalanMeasure.GenD.Signed.RouteI.quadBasis_tauI_le
#print axioms CatalanMeasure.GenD.Signed.RouteI.hweights_of_cardinal_L
#print axioms CatalanMeasure.GenD.Signed.RouteI.hweights_tauI
#print axioms CatalanMeasure.GenD.Signed.RouteI.weighted_atom_point_interval
#print axioms CatalanMeasure.GenD.Signed.RouteI.tauI_injective
#print axioms CatalanMeasure.GenD.Signed.RouteI.tauI_mem
#print axioms CatalanMeasure.GenD.Signed.RouteI.tauI_mem_Ioo
#print axioms CatalanMeasure.GenD.Signed.RouteI.tauI_ne_zero
#print axioms CatalanMeasure.GenD.Signed.RouteI.tauI_support
#print axioms CatalanMeasure.GenD.Signed.RouteI.half_exp_le_norm_T_ofReal
#print axioms CatalanMeasure.GenD.Signed.RouteI.norm_lagrange_cheb_le
#print axioms CatalanMeasure.GenD.Signed.RouteI.real_bound_extend
#print axioms CatalanMeasure.GenD.Signed.RouteI.nodal_weight_joint_le_open
#print axioms CatalanMeasure.GenD.Signed.RouteI.mem_Icc_of_abs_ivlCoord_le_one
#print axioms CatalanMeasure.GenD.Signed.RouteI.card_pair_sigma
#print axioms CatalanMeasure.GenD.Signed.RouteI.nodeSys_injective
#print axioms CatalanMeasure.GenD.Signed.RouteI.pairK_spec
