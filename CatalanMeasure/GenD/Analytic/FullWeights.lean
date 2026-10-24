module

public import CatalanMeasure.GenD.Analytic.GapWeights

@[expose] public section

/-!
# Analytic layer (group 4): full-interval Chebyshev nodes, any `J = d0 N`

Generic port of `Parametric.FullIntervalQuadrature` / `FullIntervalWeights` (and the radius used
by `TwentyCircle`).  The Chebyshev roots `chebX J` contain `0` when `J` is odd, where the common
factor `X^A` vanishes.  We therefore use `K = 2*((J+1)/2)` (even, `K - J <= 1`) and keep the
first `J` roots of `T_K`: for odd `J` one root is dropped (the same device as `gapNodesGen`);
for even `J` the nodes are exactly `chebX J`.  The circle estimate for `T_K` is a hypothesis
`FullCircleBound`; the output is `GapWeightBounds` for the family `fullNodesD`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev Finset OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

def fullK (J : ℕ) : ℕ := 2 * ((J + 1) / 2)

def fullNodes (J : ℕ) : Fin J → ℝ :=
  fun i => CatalanMeasure.chebX (fullK J) (Fin.castLE (by unfold fullK; omega) i)

def fullNodesD (P : Parameters) (N : ℕ) : Fin ((P.n0 - P.g0) * N) → ℝ :=
  fullNodes ((P.n0 - P.g0) * N)

def fullNodal (J : ℕ) : ℝ[X] := ∏ j : Fin J, (X - C (fullNodes J j))

def fullExtra (J : ℕ) : ℝ[X] :=
  ∏ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val), (X - C (CatalanMeasure.chebX (fullK J) i))

/-- Circle estimate for `T_K`, `K = fullK (d0 N)`. -/
def FullCircleBound (P : Parameters) (r C wc : ℝ) : Prop :=
  ∀ (N : ℕ) (z : ℂ), 0 < N → ‖z‖ = r →
    ‖((T ℝ (fullK ((P.n0 - P.g0) * N) : ℤ)).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) ≤ C * Real.exp (wc * N)

theorem fullNodes_injective (J : ℕ) : Function.Injective (fullNodes J) := by
  intro i j h
  exact Fin.castLE_injective _ (CatalanMeasure.chebX_injective _ h)

theorem fullNodes_mem (J : ℕ) (i : Fin J) : fullNodes J i ∈ Set.Ioo (-1 : ℝ) 1 :=
  CatalanMeasure.chebX_mem _

theorem fullNodes_ne_zero (J : ℕ) (i : Fin J) : fullNodes J i ≠ 0 := by
  intro h
  unfold fullNodes CatalanMeasure.chebX CatalanMeasure.chebAngle at h
  have hK : 0 < fullK J := by have := i.isLt; unfold fullK; omega
  have hKR : (0 : ℝ) < fullK J := by exact_mod_cast hK
  have hlt := i.isLt
  have h2 : (2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * (fullK J : ℝ)) = Real.pi / 2 := by
    have hlo : 0 < (2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * (fullK J : ℝ)) := by
      positivity
    have hhi : (2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * (fullK J : ℝ)) < Real.pi := by
      rw [div_lt_iff₀ (by positivity)]
      have : (2 * ((i : ℕ) : ℝ) + 1) < 2 * (fullK J : ℝ) := by
        have : ((i : ℕ) : ℝ) + 1 ≤ fullK J := by
          exact_mod_cast (show (i : ℕ) + 1 ≤ fullK J by unfold fullK at *; omega)
        linarith
      nlinarith [Real.pi_pos]
    have hc : Real.cos ((2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * (fullK J : ℝ))) = 0 := by
      simpa using h
    rw [← Real.cos_pi_div_two] at hc
    exact Real.injOn_cos ⟨hlo.le, hhi.le⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hc
  -- (2i+1) / (2K) = 1/2  <=>  2i+1 = K, impossible for K even
  have h3 : (2 * ((i : ℕ) : ℝ) + 1) = fullK J := by
    field_simp at h2
    nlinarith [Real.pi_pos]
  have h4 : 2 * (i : ℕ) + 1 = fullK J := by exact_mod_cast h3
  unfold fullK at h4
  omega

theorem fullNodal_mul_extra {J : ℕ} (hJ : 0 < J) :
    T ℝ (fullK J : ℤ) = C ((2 : ℝ) ^ (fullK J - 1)) * (fullNodal J * fullExtra J) := by
  have hK : 0 < fullK J := by unfold fullK; omega
  rw [CatalanMeasure.T_eq_nodal hK, prod_fin_split (K := fullK J) (L := J)
    (by unfold fullK; omega)]
  rfl

theorem fullExtra_card_le (J : ℕ) :
    (univ.filter (fun i : Fin (fullK J) => J ≤ i.val)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [mem_filter, mem_univ, true_and] at hi hj
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  unfold fullK at *
  omega

theorem fullExtra_norm_ge (J : ℕ) {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) (z : ℂ) (hz : ‖z‖ = r) :
    r - 1 ≤ ‖((fullExtra J).map (algebraMap ℝ ℂ)).eval z‖ := by
  unfold fullExtra
  rw [Polynomial.map_prod, eval_prod, norm_prod]
  have hf : ∀ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val),
      r - 1 ≤ ‖(((X - C (CatalanMeasure.chebX (fullK J) i) : ℝ[X]).map
        (algebraMap ℝ ℂ)).eval z)‖ := by
    intro i _
    have hp := CatalanMeasure.chebX_mem i
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C,
      Complex.coe_algebraMap]
    have hh := norm_sub_norm_le z (CatalanMeasure.chebX (fullK J) i : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, hz] at hh
    have hab : |CatalanMeasure.chebX (fullK J) i| < 1 := abs_lt.mpr hp
    linarith only [hh, hab]
  have hc : ∏ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val), (r - 1) ≤
      ∏ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val),
        ‖(((X - C (CatalanMeasure.chebX (fullK J) i) : ℝ[X]).map
          (algebraMap ℝ ℂ)).eval z)‖ :=
    Finset.prod_le_prod₀ (fun _ _ => by linarith only [hr1]) hf
  rw [prod_const] at hc
  have hle : (r - 1) ^ 1 ≤ (r - 1) ^ (univ.filter (fun i : Fin (fullK J) => J ≤ i.val)).card :=
    pow_le_pow_of_le_one (by linarith only [hr1]) (by linarith only [hr2]) (fullExtra_card_le J)
  simpa using hle.trans hc

theorem fullExtra_eval_abs_le (J : ℕ) {t : ℝ} (ht : |t| ≤ 1) : |(fullExtra J).eval t| ≤ 2 := by
  unfold fullExtra
  rw [eval_prod, abs_prod]
  have hf : ∀ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val),
      |(X - C (CatalanMeasure.chebX (fullK J) i) : ℝ[X]).eval t| ≤ 2 := by
    intro i _
    have hp := CatalanMeasure.chebX_mem i
    simp only [eval_sub, eval_X, eval_C]
    have := abs_le.mp ht
    rw [abs_le]
    constructor <;> linarith only [this.1, this.2, hp.1, hp.2]
  have hc : ∏ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val),
      |(X - C (CatalanMeasure.chebX (fullK J) i) : ℝ[X]).eval t| ≤
      ∏ i ∈ univ.filter (fun i : Fin (fullK J) => J ≤ i.val), (2 : ℝ) :=
    Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hf
  rw [prod_const] at hc
  calc _ ≤ _ := hc
    _ ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (fullExtra_card_le J)
    _ = 2 := by norm_num

theorem fullTK_derivative_node {J : ℕ} (j : Fin J) :
    (derivative (T ℝ (fullK J : ℤ))).eval (fullNodes J j) =
      (2 : ℝ) ^ (fullK J - 1) * ((derivative (fullNodal J)).eval (fullNodes J j) *
        (fullExtra J).eval (fullNodes J j)) := by
  have hQ : (fullNodal J).eval (fullNodes J j) = 0 := by
    unfold fullNodal
    rw [eval_prod]
    exact prod_eq_zero (mem_univ j) (by simp)
  have hJ : 0 < J := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  rw [fullNodal_mul_extra hJ, derivative_C_mul, derivative_mul, eval_mul, eval_C,
    eval_add, eval_mul, eval_mul, hQ]
  ring

/-- Cardinal polynomial of the full-interval nodes on `|z| = r`. -/
theorem full_cardinal_norm_le {J : ℕ} (hJ : 0 < J) {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2)
    (i : Fin J) (z : ℂ) (hz : ‖z‖ = r) :
    ‖((quadBasis (fullNodes J) i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      2 * ‖((T ℝ (fullK J : ℤ)).map (algebraMap ℝ ℂ)).eval z‖ / (r - 1) ^ 2 := by
  set lead : ℝ := (2 : ℝ) ^ (fullK J - 1) with hlead
  have hl : 0 < lead := by positivity
  have hr : 0 < r - 1 := sub_pos.mpr hr1
  have hQ : fullNodal J = C 1 * ∏ j : Fin J, (X - C (fullNodes J j)) := by simp [fullNodal]
  have hτ := fullNodes_injective J
  have hmem := fullNodes_mem J
  have hE2 := fullExtra_eval_abs_le J (t := fullNodes J i)
    (abs_le.mpr ⟨by linarith only [(hmem i).1], by linarith only [(hmem i).2]⟩)
  have hPd : (fullK J : ℝ) ≤ |(derivative (T ℝ (fullK J : ℤ))).eval (fullNodes J i)| :=
    cheb_derivative_eval_ge (Fin.castLE (by unfold fullK; omega) i)
  have hPn := fullTK_derivative_node i
  have hK1 : (1 : ℝ) ≤ fullK J := by
    exact_mod_cast (show 1 ≤ fullK J by unfold fullK; omega)
  have hder : 1 / (2 * lead) ≤ |(derivative (fullNodal J)).eval (fullNodes J i)| := by
    rw [hPn, abs_mul, abs_mul, abs_of_pos hl] at hPd
    have h1 : 1 ≤ lead * (|(derivative (fullNodal J)).eval (fullNodes J i)| *
        |(fullExtra J).eval (fullNodes J i)|) := hK1.trans hPd
    have h2 : lead * (|(derivative (fullNodal J)).eval (fullNodes J i)| *
        |(fullExtra J).eval (fullNodes J i)|) ≤
        lead * (|(derivative (fullNodal J)).eval (fullNodes J i)| * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 (abs_nonneg _)) hl.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [h1, h2]
  have hcard := norm_cardinal_le_of_nodal hτ hmem i hQ (by positivity) hder hr1 z hz
  have hP := congrArg (fun Q : ℝ[X] => ‖(Q.map (algebraMap ℝ ℂ)).eval z‖)
    (fullNodal_mul_extra hJ)
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, norm_mul,
    Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs] at hP
  have hE := fullExtra_norm_ge J hr1 hr2 z hz
  set A := ‖((T ℝ (fullK J : ℤ)).map (algebraMap ℝ ℂ)).eval z‖ with hA
  set q := ‖((fullNodal J).map (algebraMap ℝ ℂ)).eval z‖ with hq
  set e := ‖((fullExtra J).map (algebraMap ℝ ℂ)).eval z‖ with he
  have hq0 : 0 ≤ q := norm_nonneg _
  have hlq : lead * q * (r - 1) ≤ A := by
    rw [hP, abs_of_pos hl]
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hl.le hq0)
    nlinarith only [this]
  have hstep : q / (1 / (2 * lead) * (r - 1)) ≤ 2 * A / (r - 1) ^ 2 := by
    rw [show q / (1 / (2 * lead) * (r - 1)) = 2 * (lead * q) / (r - 1) by field_simp]
    rw [div_le_div_iff₀ hr (by positivity)]
    nlinarith only [hlq, hr]
  exact hcard.trans hstep

theorem full_common_basis_coeff_zero (P : Parameters) (hg : P.g0 ≤ P.n0) (N : ℕ)
    (j : Fin ((P.n0 - P.g0) * N)) (i : ℕ) (hi : P.H N ≤ i) :
    (rowCommonFactor P N * quadBasis (fullNodesD P N) j).coeff i = 0 := by
  have hf := rowCommonFactor_natDegree_le P N
  have hb : (quadBasis (fullNodesD P N) j).natDegree ≤ (P.n0 - P.g0) * N - 1 :=
    quadBasis_natDegree_le (fullNodes_injective _) j
  have hd : (rowCommonFactor P N * quadBasis (fullNodesD P N) j).natDegree ≤
      (rowCommonFactor P N).natDegree + (quadBasis (fullNodesD P N) j).natDegree :=
    natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  have hJ : (P.n0 - P.g0) * N + P.g0 * N = P.n0 * N := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hg]
  have hpos : 0 < (P.n0 - P.g0) * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.A, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h] at hi hf
  obtain ⟨t, ht⟩ : ∃ t, t = (P.n0 - P.g0) * N := ⟨_, rfl⟩
  rw [← ht] at hJ hpos
  have hb2 : (quadBasis (fullNodesD P N) j).natDegree ≤ t - 1 := by rw [ht]; exact hb
  obtain ⟨nn, hnn⟩ : ∃ nn, nn = P.n0 * N := ⟨_, rfl⟩
  rw [← hnn] at hJ hi
  omega

theorem full_functional_le (P : Parameters) (hg : P.g0 ≤ P.n0) {r C wc : ℝ}
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hcirc : FullCircleBound P r C wc)
    (N k : ℕ) (j : Fin ((P.n0 - P.g0) * N)) :
    |polynomialFunctional P N k (rowCommonFactor P N * quadBasis (fullNodesD P N) j)| ≤
      4 * (P.H N : ℝ) * (2 * (C * Real.exp (wc * N)) / (r - 1) ^ 2) := by
  have hJ : 0 < (P.n0 - P.g0) * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hJ)
  apply polynomialFunctional_common_factor_le P N k _
    (full_common_basis_coeff_zero P hg N j) (radius := r) hr1.le
  intro z hz
  have hc := full_cardinal_norm_le hJ hr1 hr2 j z hz
  have hb := hcirc N z hN hz
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, eval_mul, eval_pow, eval_sub, eval_one, eval_X, norm_mul, norm_pow]
  have hr : 0 < (r - 1) ^ 2 := by have := sub_pos.mpr hr1; positivity
  calc _ ≤ (2 * ‖((T ℝ (fullK ((P.n0 - P.g0) * N) : ℤ)).map (algebraMap ℝ ℂ)).eval z‖ /
        (r - 1) ^ 2) * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 / (r - 1) ^ 2 * (‖((T ℝ (fullK ((P.n0 - P.g0) * N) : ℤ)).map
          (algebraMap ℝ ℂ)).eval z‖ * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N)) := by ring
    _ ≤ 2 / (r - 1) ^ 2 * (C * Real.exp (wc * N)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem full_weight_joint_le (P : Parameters) (hg : P.g0 ≤ P.n0) {r C wc : ℝ}
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hcirc : FullCircleBound P r C wc)
    (N k : ℕ) (j : Fin ((P.n0 - P.g0) * N)) :
    |(rowCommonFactor P N).eval (fullNodesD P N j)| *
      |restrictedWeight P N k (fullNodesD P N) j| ≤
      4 * (P.H N : ℝ) * (2 * (C * Real.exp (wc * N)) / (r - 1) ^ 2) := by
  have hn := rowCommonFactor_eval_ne_zero_of P N (fullNodes_ne_zero _ j)
    (fullNodes_mem _ j).2.ne
  have key : ∀ x y : ℝ, x ≠ 0 → |x| * (|y| / |x|) = |y| := fun x y hx => by
    have := abs_ne_zero.mpr hx
    field_simp
  rw [restrictedWeight, abs_div]
  exact le_of_eq_of_le (key _ _ hn) (full_functional_le P hg hr1 hr2 hcirc N k j)

theorem full_weight_bounds (P : Parameters) (hg : P.g0 ≤ P.n0) {r C wc w : ℝ}
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hcirc : FullCircleBound P r C wc) (hw : wc < w) :
    GapWeightBounds P (fullNodesD P) w := by
  set c0 : ℝ := 8 * (P.H 1 : ℝ) * C / (r - 1) ^ 2 with hc0
  have ht : Filter.Tendsto (fun N : ℕ => Real.exp ((w - wc) * N)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop (sub_pos.mpr hw) tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (c0 / 108000), Filter.eventually_gt_atTop 0]
    with N hN hN0 k j
  refine (full_weight_joint_le P hg hr1 hr2 hcirc N k j).trans ?_
  have hH : (P.H N : ℝ) = (P.H 1 : ℝ) * N := by
    simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
      Parameters.q, Parameters.g, Parameters.h]
    push_cast; ring
  have hexp : Real.exp (w * N) = Real.exp (wc * N) * Real.exp ((w - wc) * N) := by
    rw [← Real.exp_add]; congr 1; ring
  have hN1 : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [hH, hexp]
  have he := Real.exp_pos (wc * N)
  have hmul := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by norm_num : (0 : ℝ) < 108000)).mp hN)
    (mul_nonneg hN1.le he.le)
  have hr : 0 < (r - 1) ^ 2 := by have := sub_pos.mpr hr1; positivity
  have : 4 * ((P.H 1 : ℝ) * N) * (2 * (C * Real.exp (wc * N)) / (r - 1) ^ 2) =
      c0 * (N * Real.exp (wc * N)) := by
    rw [hc0]; field_simp; ring
  rw [this]
  nlinarith only [hmul]

end

end Analytic
end CatalanMeasure.GenD
