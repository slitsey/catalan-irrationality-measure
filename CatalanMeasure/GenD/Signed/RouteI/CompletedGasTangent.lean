module

public import CatalanMeasure.GenD.Signed.PhysicalPick
public import CatalanMeasure.GenD.Signed.RouteI.Wrappers
public import CatalanMeasure.GenD.Signed.Brackets
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CatalanMeasure.GenD.Signed.RealPlace
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import CatalanMeasure.FreePopulationFields
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CatalanMeasure.GenD.Analytic.Fields
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import CatalanMeasure.GenD.Signed.RouteI.CompletedGasTangentBase

@[expose] public section





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields

noncomputable section

/-! ### The cubed Poisson density -/

/-- Generating function of `(1 + A k + B k^2) x^k`. -/
def cubeG (A B : ℂ) (x : ℂ) : ℂ :=
  x / (1 - x) + A * (x / (1 - x) ^ 2) + B * (x * (1 + x) / (1 - x) ^ 3)

theorem hasSum_cubeG {x : ℂ} (hx : ‖x‖ < 1) (A B : ℂ) :
    HasSum (fun k : ℕ => x ^ (k + 1) * (1 + A * ((k : ℂ) + 1) + B * ((k : ℂ) + 1) ^ 2))
      (cubeG A B x) := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have : x = 1 := by linear_combination -h
    rw [this] at hx
    simp at hx
  have h0 := hasSum_geometric_of_norm_lt_one hx
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hx
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hx
  have h := (((h0.add (h1.mul_left A)).add (((h2.mul_left 2).sub h1).mul_left B)).mul_left x)
  convert h using 1
  · funext k
    have e1 : (((k + 1).choose 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by simp
    have e2 : (((k + 2).choose 2 : ℕ) : ℂ) = ((k : ℂ) + 2) * ((k : ℂ) + 1) / 2 := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    rw [e1, e2, pow_succ]
    ring
  · unfold cubeG
    field_simp
    ring

/-- The algebraic identity behind the cubed Poisson density. -/
theorem cube_identity {x y N : ℂ} (hx : 1 - x ≠ 0) (hy : 1 - y ≠ 0)
    (hNd : N = 1 + 4 * (x * y) + (x * y) ^ 2) (hN : N ≠ 0) :
    1 + cubeG (3 * (1 + x * y) * (1 - x * y) / (2 * N)) ((1 - x * y) ^ 2 / (2 * N)) x +
        cubeG (3 * (1 + x * y) * (1 - x * y) / (2 * N)) ((1 - x * y) ^ 2 / (2 * N)) y =
      (1 - x * y) ^ 5 / (N * ((1 - x) * (1 - y)) ^ 3) := by
  unfold cubeG
  field_simp
  rw [hNd]
  ring

variable (S : CapSource)

/-- The multiplier `q^k (1 + A k + B k^2)`. -/
def cubeK (k : ℕ) : ℝ := S.q ^ k * (1 + S.strength * k + S.curvature * k ^ 2)

/-- `E(α) = 1 - 2 q cos α + q^2`. -/
def cubeE (α : ℝ) : ℝ := 1 - 2 * S.q * Real.cos α + S.q ^ 2

/-- The cubed Poisson density of mass one against `dα/2π`. -/
def cubePhi (α : ℝ) : ℝ := (1 - S.q ^ 2) ^ 5 / ((1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2) * cubeE S α ^ 3)

variable {S}

theorem cap_q_pos : 0 < S.q := Real.exp_pos _

theorem cap_q_lt_one (hε : 0 < S.eps) : S.q < 1 := by
  unfold CapSource.q
  rw [Real.exp_lt_one_iff]
  linarith

theorem cubeE_ge (hε : 0 < S.eps) (α : ℝ) : (1 - S.q) ^ 2 ≤ cubeE S α := by
  have h0 := cap_q_pos (S := S)
  have := Real.cos_le_one α
  unfold cubeE
  nlinarith

theorem cubeE_pos (hε : 0 < S.eps) (α : ℝ) : 0 < cubeE S α := by
  have h1 := cap_q_lt_one hε
  have : 0 < (1 - S.q) ^ 2 := by
    have : 0 < 1 - S.q := by linarith
    positivity
  exact this.trans_le (cubeE_ge hε α)

theorem cubePhi_nonneg (hε : 0 < S.eps) (α : ℝ) : 0 ≤ cubePhi S α := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have hE := cubeE_pos hε α
  have : 0 ≤ 1 - S.q ^ 2 := by nlinarith
  unfold cubePhi
  positivity

/-- A uniform bound of the density. -/
def cubeF (S : CapSource) : ℝ :=
  (1 - S.q ^ 2) ^ 5 / ((1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2) * ((1 - S.q) ^ 2) ^ 3)

theorem cubePhi_le (hε : 0 < S.eps) (α : ℝ) : cubePhi S α ≤ cubeF S := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have hq : 0 < 1 - S.q := by linarith
  have hE := cubeE_ge hε α
  have h2 : 0 ≤ 1 - S.q ^ 2 := by nlinarith
  unfold cubePhi cubeF
  gcongr

theorem cubePhi_continuous (hε : 0 < S.eps) : Continuous (cubePhi S) := by
  have h0 := cap_q_pos (S := S)
  have hc : Continuous (cubeE S) := by
    unfold cubeE
    fun_prop
  unfold cubePhi
  refine continuous_const.div (continuous_const.mul (hc.pow 3)) fun α => ?_
  have := cubeE_pos hε α
  positivity

theorem cap_strength_eq (hε : 0 < S.eps) :
    S.strength = 3 * (1 + S.q ^ 2) * (1 - S.q ^ 2) / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have h2 : 1 - S.q ^ 2 ≠ 0 := by nlinarith
  have h3 : 1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2 ≠ 0 := by positivity
  unfold CapSource.strength CapSource.normalizer
  field_simp

theorem cap_curvature_eq (hε : 0 < S.eps) :
    S.curvature = (1 - S.q ^ 2) ^ 2 / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have h2 : 1 - S.q ^ 2 ≠ 0 := by nlinarith
  have h3 : 1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2 ≠ 0 := by positivity
  unfold CapSource.curvature CapSource.normalizer
  field_simp

/-- **Fourier series of the cubed Poisson density.** -/
theorem cubePhi_hasSum (hε : 0 < S.eps) (α : ℝ) :
    HasSum (fun k : ℕ => 2 * cubeK S (k + 1) * Real.cos (((k : ℝ) + 1) * α)) (cubePhi S α - 1) := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  set q := S.q with hq
  set x : ℂ := (q : ℂ) * Complex.exp (α * Complex.I) with hx
  set y : ℂ := (q : ℂ) * Complex.exp (-(α * Complex.I)) with hy
  have hxn : ‖x‖ = q := by
    rw [hx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h0]
  have hyc : conj x = y := by
    rw [hx, hy, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    simp
  have hxy : x * y = ((q ^ 2 : ℝ) : ℂ) := by
    rw [hx, hy, mul_mul_mul_comm, ← Complex.exp_add]
    simp [sq]
  have hne : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := by
    intro z hz h
    have : z = 1 := by linear_combination -h
    rw [this] at hz
    simp at hz
  have hxl : ‖x‖ < 1 := by rw [hxn]; exact h1
  have hyl : ‖y‖ < 1 := by rw [← hyc, Complex.norm_conj]; exact hxl
  have hA : ((S.strength : ℝ) : ℂ) = 3 * (1 + x * y) * (1 - x * y) /
      (2 * (1 + 4 * (x * y) + (x * y) ^ 2)) := by
    rw [cap_strength_eq hε, hxy]
    push_cast
    ring
  have hB : ((S.curvature : ℝ) : ℂ) = (1 - x * y) ^ 2 / (2 * (1 + 4 * (x * y) + (x * y) ^ 2)) := by
    rw [cap_curvature_eq hε, hxy]
    push_cast
    ring
  have hr : 1 - x * y ≠ 0 := by
    rw [hxy]
    have : 1 - q ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have hN : 1 + 4 * (x * y) + (x * y) ^ 2 ≠ 0 := by
    rw [hxy]
    have : 1 + 4 * q ^ 2 + (q ^ 2) ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hid := cube_identity (hne x hxl) (hne y hyl) rfl hN
  rw [← hA, ← hB] at hid
  have hsum := hasSum_cubeG hxl (S.strength : ℂ) (S.curvature : ℂ)
  have hre := Complex.reCLM.hasSum hsum
  have hE : (1 - x) * (1 - y) = ((cubeE S α : ℝ) : ℂ) := by
    have e : x + y = ((2 * q * Real.cos α : ℝ) : ℂ) := by
      rw [hx, hy]
      push_cast
      rw [Complex.cos]
      ring_nf
    have : (1 - x) * (1 - y) = 1 - (x + y) + x * y := by ring
    rw [this, e, hxy]
    simp only [cubeE, ← hq]
    push_cast
    ring
  have hval : (Complex.reCLM (cubeG (S.strength : ℂ) (S.curvature : ℂ) x)) * 2 =
      cubePhi S α - 1 := by
    have hconj : conj (cubeG (S.strength : ℂ) (S.curvature : ℂ) x) =
        cubeG (S.strength : ℂ) (S.curvature : ℂ) y := by
      unfold cubeG
      simp only [map_add, map_mul, map_div₀, map_sub, map_one, map_pow, hyc, Complex.conj_ofReal]
    have hre2 : ((Complex.reCLM (cubeG (S.strength : ℂ) (S.curvature : ℂ) x) * 2 : ℝ) : ℂ) =
        cubeG (S.strength : ℂ) (S.curvature : ℂ) x +
          cubeG (S.strength : ℂ) (S.curvature : ℂ) y := by
      rw [← hconj, Complex.add_conj]
      simp
      ring
    have : ((Complex.reCLM (cubeG (S.strength : ℂ) (S.curvature : ℂ) x) * 2 : ℝ) : ℂ) =
        ((cubePhi S α - 1 : ℝ) : ℂ) := by
      rw [hre2]
      have e2 : ((cubePhi S α : ℝ) : ℂ) = (1 - x * y) ^ 5 /
          ((1 + 4 * (x * y) + (x * y) ^ 2) * ((1 - x) * (1 - y)) ^ 3) := by
        rw [hE, hxy]
        simp only [cubePhi, ← hq]
        push_cast
        ring
      push_cast
      rw [e2, ← hid]
      ring
    exact_mod_cast this
  rw [← hval]
  convert hre.mul_right 2 using 1
  funext k
  have hpow : x ^ (k + 1) = ((q ^ (k + 1) : ℝ) : ℂ) *
      Complex.exp ((((k : ℝ) + 1) * α : ℝ) * Complex.I) := by
    rw [hx, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  have hmul : (Complex.reCLM (x ^ (k + 1) * (1 + (S.strength : ℂ) * ((k : ℂ) + 1) +
      (S.curvature : ℂ) * ((k : ℂ) + 1) ^ 2))) =
      q ^ (k + 1) * Real.cos (((k : ℝ) + 1) * α) *
        (1 + S.strength * ((k : ℝ) + 1) + S.curvature * ((k : ℝ) + 1) ^ 2) := by
    have e : (1 + (S.strength : ℂ) * ((k : ℂ) + 1) + (S.curvature : ℂ) * ((k : ℂ) + 1) ^ 2) =
        ((1 + S.strength * ((k : ℝ) + 1) + S.curvature * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, hpow, Complex.reCLM_apply, Complex.re_mul_ofReal, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  rw [hmul]
  simp only [cubeK, ← hq]
  push_cast
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open OAI.InternalCatalan

noncomputable section


/-! ### Trigonometric orthogonality on `(-π, π]` -/

local notation "π" => Real.pi

theorem pi_le : -π ≤ π := by linarith [Real.pi_pos]

theorem int_cos_int {n : ℤ} (hn : n ≠ 0) : ∫ φ in Ioc (-π) π, Real.cos ((n : ℝ) * φ) = 0 := by
  have hc : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← intervalIntegral.integral_of_le pi_le,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos, mul_neg,
    Real.sin_neg, Real.sin_int_mul_pi]
  simp

theorem int_sin_int (n : ℤ) : ∫ φ in Ioc (-π) π, Real.sin ((n : ℝ) * φ) = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  have hc : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← intervalIntegral.integral_of_le pi_le,
    intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin, mul_neg,
    Real.cos_neg]
  simp

theorem cos_int_integrable (n : ℤ) :
    Integrable (fun φ : ℝ => Real.cos ((n : ℝ) * φ)) (volume.restrict (Ioc (-π) π)) :=
  (by fun_prop : Continuous fun φ : ℝ => Real.cos ((n : ℝ) * φ)).integrableOn_Ioc

theorem sin_int_integrable (n : ℤ) :
    Integrable (fun φ : ℝ => Real.sin ((n : ℝ) * φ)) (volume.restrict (Ioc (-π) π)) :=
  (by fun_prop : Continuous fun φ : ℝ => Real.sin ((n : ℝ) * φ)).integrableOn_Ioc

theorem int_one : ∫ _φ in Ioc (-π) π, (1 : ℝ) = 2 * π := by
  rw [← intervalIntegral.integral_of_le pi_le, intervalIntegral.integral_const]
  simp
  ring

theorem int_cos_cos {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    ∫ φ in Ioc (-π) π, Real.cos ((j : ℝ) * φ) * Real.cos ((k : ℝ) * φ) =
      if j = k then π else 0 := by
  have e : ∀ φ : ℝ, Real.cos ((j : ℝ) * φ) * Real.cos ((k : ℝ) * φ) =
      (Real.cos ((((j : ℤ) - k : ℤ) : ℝ) * φ) + Real.cos ((((j : ℤ) + k : ℤ) : ℝ) * φ)) / 2 := by
    intro φ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp only [e]
  rw [integral_div, integral_add (cos_int_integrable _) (cos_int_integrable _),
    int_cos_int (n := (j : ℤ) + k) (by omega)]
  split_ifs with h
  · subst h
    have : ∫ φ in Ioc (-π) π, Real.cos ((((j : ℤ) - j : ℤ) : ℝ) * φ) = 2 * π := by
      simp only [sub_self, Int.cast_zero, zero_mul, Real.cos_zero]
      exact int_one
    rw [this]
    ring
  · rw [int_cos_int (n := (j : ℤ) - k) (by omega)]
    simp

theorem int_sin_cos (j k : ℕ) :
    ∫ φ in Ioc (-π) π, Real.cos ((j : ℝ) * φ) * Real.sin ((k : ℝ) * φ) = 0 := by
  have e : ∀ φ : ℝ, Real.cos ((j : ℝ) * φ) * Real.sin ((k : ℝ) * φ) =
      (Real.sin ((((k : ℤ) + j : ℤ) : ℝ) * φ) + Real.sin ((((k : ℤ) - j : ℤ) : ℝ) * φ)) / 2 := by
    intro φ
    push_cast
    rw [sub_mul, add_mul, Real.sin_sub, Real.sin_add]
    ring
  simp only [e]
  rw [integral_div, integral_add (sin_int_integrable _) (sin_int_integrable _), int_sin_int,
    int_sin_int]
  simp

theorem hasSum_int_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : ℕ → α → ℝ} {f : α → ℝ} {b : ℕ → ℝ} (hm : ∀ n, AEStronglyMeasurable (F n) μ)
    (hb : ∀ n a, |F n a| ≤ b n) (hs : Summable b) (hl : ∀ a, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) :=
  hasSum_integral_of_dominated_convergence (fun n _ => b n) hm (fun n => ae_of_all _ (hb n))
    (ae_of_all _ fun _ => hs) (integrable_const _) (ae_of_all _ hl)

/-! ### Even densities with a cosine series -/

/-- A nonnegative continuous density `1 + 2 Σ a_k cos kφ`. -/
structure TrigDens (a : ℕ → ℝ) (g : ℝ → ℝ) : Prop where
  summ : Summable fun k : ℕ => |a (k + 1)|
  cont : Continuous g
  nonneg : ∀ φ, 0 ≤ g φ
  series : ∀ φ, HasSum (fun k : ℕ => 2 * a (k + 1) * Real.cos (((k : ℝ) + 1) * φ)) (g φ - 1)

namespace TrigDens

variable {a : ℕ → ℝ} {g : ℝ → ℝ}

theorem even (H : TrigDens a g) (φ : ℝ) : g (-φ) = g φ := by
  have h := H.series (-φ)
  simp only [mul_neg, Real.cos_neg] at h
  have := h.unique (H.series φ)
  linarith

/-- The uniform bound of the density. -/
def bound (a : ℕ → ℝ) : ℝ := 1 + 2 * ∑' k : ℕ, |a (k + 1)|

theorem le_bound (H : TrigDens a g) (φ : ℝ) : g φ ≤ bound a := by
  have h2 : HasSum (fun k : ℕ => 2 * |a (k + 1)|) (2 * ∑' k : ℕ, |a (k + 1)|) :=
    H.summ.hasSum.mul_left 2
  have := hasSum_le (fun k => ?_) (H.series φ) h2
  · unfold bound
    linarith
  · have h4 : a (k + 1) * Real.cos (((k : ℝ) + 1) * φ) ≤ |a (k + 1)| := by
      calc _ ≤ |a (k + 1) * Real.cos (((k : ℝ) + 1) * φ)| := le_abs_self _
        _ = |a (k + 1)| * |Real.cos (((k : ℝ) + 1) * φ)| := abs_mul _ _
        _ ≤ |a (k + 1)| * 1 := by
            gcongr
            exact Real.abs_cos_le_one _
        _ = _ := mul_one _
    linarith

theorem bound_nonneg (H : TrigDens a g) : 0 ≤ bound a := (H.nonneg 0).trans (H.le_bound 0)

theorem test (H : TrigDens a g) {h : ℝ → ℝ} (hc : Continuous h) (hb : ∀ φ, |h φ| ≤ 1) :
    HasSum (fun k : ℕ => 2 * a (k + 1) *
        ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) * h φ)
      ((∫ φ in Ioc (-π) π, g φ * h φ) - ∫ φ in Ioc (-π) π, h φ) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (-π) π)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hs := hasSum_int_of_bound (μ := volume.restrict (Ioc (-π) π))
    (F := fun (k : ℕ) φ => 2 * a (k + 1) * Real.cos (((k : ℝ) + 1) * φ) * h φ)
    (f := fun φ => (g φ - 1) * h φ) (b := fun k => 2 * |a (k + 1)|)
    (fun n => (by fun_prop : Continuous fun φ : ℝ =>
      2 * a (n + 1) * Real.cos (((n : ℝ) + 1) * φ) * h φ).aestronglyMeasurable)
    (fun n φ => by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h1 := Real.abs_cos_le_one (((n : ℝ) + 1) * φ)
      have h2 := hb φ
      calc 2 * |a (n + 1)| * |Real.cos (((n : ℝ) + 1) * φ)| * |h φ| ≤ 2 * |a (n + 1)| * 1 * 1 := by
            gcongr
        _ = _ := by ring)
    (H.summ.mul_left 2) (fun φ => (H.series φ).mul_right _)
  have hgi : Integrable (fun φ => g φ * h φ) (volume.restrict (Ioc (-π) π)) :=
    (H.cont.mul hc).integrableOn_Ioc
  have hhi : Integrable h (volume.restrict (Ioc (-π) π)) := hc.integrableOn_Ioc
  have e : ∫ φ in Ioc (-π) π, (g φ - 1) * h φ =
      (∫ φ in Ioc (-π) π, g φ * h φ) - ∫ φ in Ioc (-π) π, h φ := by
    rw [← integral_sub hgi hhi]
    congr 1
    funext φ
    ring
  rw [← e]
  convert hs using 2 with k
  rw [← integral_const_mul]
  congr 1
  funext φ
  ring

theorem mass (H : TrigDens a g) : ∫ φ in Ioc (-π) π, g φ = 2 * π := by
  have h := H.test (h := fun _ => 1) continuous_const (by simp)
  have e : ∀ k : ℕ, ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) * 1 = 0 := by
    intro k
    have := int_cos_int (n := (k : ℤ) + 1) (by omega)
    push_cast at this
    simpa using this
  simp only [e, mul_zero] at h
  have h0 := h.unique hasSum_zero
  simp only [mul_one] at h0
  have h1 := int_one
  linarith

theorem cos_moment (H : TrigDens a g) (n : ℕ) :
    ∫ φ in Ioc (-π) π, g φ * Real.cos (((n : ℝ) + 1) * φ) = 2 * π * a (n + 1) := by
  have hc : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := fun k => by push_cast; ring
  have h := H.test (h := fun φ => Real.cos (((n : ℝ) + 1) * φ)) (by fun_prop)
    (fun φ => Real.abs_cos_le_one _)
  have e : ∀ k : ℕ, ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) *
      Real.cos (((n : ℝ) + 1) * φ) = if k = n then π else 0 := by
    intro k
    rw [hc k, hc n, int_cos_cos (by omega) (by omega)]
    simp
  have e0 : ∫ φ in Ioc (-π) π, Real.cos (((n : ℝ) + 1) * φ) = 0 := by
    have := int_cos_int (n := (n : ℤ) + 1) (by omega)
    push_cast at this
    exact this
  simp only [e, e0, sub_zero] at h
  have h1 : HasSum (fun k : ℕ => 2 * a (k + 1) * if k = n then π else 0) (2 * a (n + 1) * π) := by
    convert hasSum_single (f := fun k : ℕ => 2 * a (k + 1) * if k = n then π else 0) n
      (fun k hk => by simp [hk]) using 1
    simp
  rw [h.unique h1]
  ring

theorem sin_moment (H : TrigDens a g) (n : ℕ) :
    ∫ φ in Ioc (-π) π, g φ * Real.sin (((n : ℝ) + 1) * φ) = 0 := by
  have hc : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := fun k => by push_cast; ring
  have h := H.test (h := fun φ => Real.sin (((n : ℝ) + 1) * φ)) (by fun_prop)
    (fun φ => Real.abs_sin_le_one _)
  have e : ∀ k : ℕ, ∫ φ in Ioc (-π) π, Real.cos (((k : ℝ) + 1) * φ) *
      Real.sin (((n : ℝ) + 1) * φ) = 0 := by
    intro k
    rw [hc k, hc n, int_sin_cos]
  have e0 : ∫ φ in Ioc (-π) π, Real.sin (((n : ℝ) + 1) * φ) = 0 := by
    have := int_sin_int ((n : ℤ) + 1)
    push_cast at this
    exact this
  simp only [e, e0, sub_zero, mul_zero] at h
  exact h.unique hasSum_zero

end TrigDens

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open OAI.InternalCatalan

noncomputable section

local notation "π" => Real.pi

/-! ### Circle algebra -/

theorem circ_mul (r r' φ φ' : ℝ) : circ r φ * circ r' φ' = circ (r * r') (φ + φ') := by
  unfold circ
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

theorem circ_pow (r φ : ℝ) (n : ℕ) : circ r φ ^ n = circ (r ^ n) ((n : ℝ) * φ) := by
  unfold circ
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  congr 2
  ring

theorem circ_re (r φ : ℝ) : (circ r φ).re = r * Real.cos φ := by
  unfold circ
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem circ_conj (r φ : ℝ) : conj (circ r φ) = circ r (-φ) := by
  unfold circ
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp

theorem norm_one_sub_circ_neg (τ α : ℝ) : ‖1 - circ τ (-α)‖ = ‖1 - circ τ α‖ := by
  rw [← circ_conj, ← Complex.norm_conj (1 - circ τ α), map_sub, map_one]

/-- Unit rotation moves the factor to a circle difference. -/
theorem one_sub_circ_norm (τ θ φ : ℝ) : ‖1 - circ τ (θ - φ)‖ = ‖circ τ θ - circ 1 φ‖ := by
  have e : circ τ θ - circ 1 φ = -circ 1 φ * (1 - circ τ (θ - φ)) := by
    have : circ 1 φ * circ τ (θ - φ) = circ τ θ := by
      rw [circ_mul, one_mul]
      congr 1
      ring
    linear_combination -this
  rw [e, norm_mul, norm_neg, circ_norm zero_le_one, one_mul]

theorem log_one_sub_hasSum {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (α : ℝ) :
    HasSum (fun k : ℕ => -(τ ^ (k + 1) * Real.cos (((k : ℝ) + 1) * α) / ((k : ℝ) + 1)))
      (Real.log ‖1 - circ τ α‖) := by
  have hz : ‖circ τ α‖ < 1 := by rw [circ_norm h0]; exact h1
  have h := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hz)
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  have h3 := h2.neg
  convert h3 using 1
  · funext k
    rw [circ_pow]
    have e : circ (τ ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * α) / (((k + 1 : ℕ) : ℂ)) =
        circ (τ ^ (k + 1) / ((k : ℝ) + 1)) (((k : ℝ) + 1) * α) := by
      unfold circ
      push_cast
      ring
    rw [e, Complex.reCLM_apply, circ_re]
    ring
  · simp [Complex.log_re]

/-! ### The arc measure of a trigonometric density -/

variable {a : ℕ → ℝ} {g : ℝ → ℝ} {s : ℝ}

/-- The arc measure of `s g`. -/
def trigM (s : ℝ) (g : ℝ → ℝ) : Measure ℝ := arcM fun φ => s * g φ

theorem trigM_integral (H : TrigDens a g) (hs : 0 ≤ s) (h : ℝ → ℝ) :
    ∫ φ, h φ ∂trigM s g = ∫ φ in Ioc (-π) π, s * g φ * h φ := by
  unfold trigM arcM
  have hm : Measurable fun φ => ENNReal.ofReal (s * g φ) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul H.cont).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun φ => ?_)
  have : 0 ≤ s * g φ := mul_nonneg hs (H.nonneg φ)
  simp only [ENNReal.toReal_ofReal this, smul_eq_mul]

theorem trigM_le (H : TrigDens a g) (hs : 0 ≤ s) (φ : ℝ) :
    s * g φ ≤ s * TrigDens.bound a := mul_le_mul_of_nonneg_left (H.le_bound φ) hs

theorem trigM_finite (H : TrigDens a g) (hs : 0 ≤ s) : IsFiniteMeasure (trigM s g) :=
  arcM_finite (mul_nonneg hs H.bound_nonneg) (trigM_le H hs)

theorem trigM_mass (H : TrigDens a g) (hs : 0 ≤ s) : (trigM s g).real Set.univ = 2 * π * s := by
  haveI := trigM_finite H hs
  have h := trigM_integral H hs (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [integral_const_mul, H.mass] at h
  simpa [mul_comm, mul_assoc, mul_left_comm] using h

theorem trigM_cos (H : TrigDens a g) (hs : 0 ≤ s) (n : ℕ) :
    ∫ φ, Real.cos (((n : ℝ) + 1) * φ) ∂trigM s g = 2 * π * s * a (n + 1) := by
  rw [trigM_integral H hs]
  simp only [mul_assoc]
  rw [integral_const_mul, H.cos_moment]
  ring

theorem trigM_sin (H : TrigDens a g) (hs : 0 ≤ s) (n : ℕ) :
    ∫ φ, Real.sin (((n : ℝ) + 1) * φ) ∂trigM s g = 0 := by
  rw [trigM_integral H hs]
  simp only [mul_assoc]
  rw [integral_const_mul, H.sin_moment, mul_zero]

theorem trigM_neg (H : TrigDens a g) (hs : 0 ≤ s) (h : ℝ → ℝ) :
    ∫ φ, h (-φ) ∂trigM s g = ∫ φ, h φ ∂trigM s g := by
  rw [trigM_integral H hs, trigM_integral H hs, ← intervalIntegral.integral_of_le pi_le,
    ← intervalIntegral.integral_of_le pi_le]
  have := intervalIntegral.integral_comp_neg (a := -π) (b := π) (fun φ => s * g φ * h φ)
  simp only [neg_neg, H.even] at this
  exact this

theorem trigM_ae_cos (θ : ℝ) (H : TrigDens a g) :
    ∀ᵐ φ ∂trigM s g, Real.cos θ ≠ Real.cos φ := by
  have hc : ({φ : ℝ | Real.cos θ = Real.cos φ}).Countable := by
    refine ((Set.countable_range fun k : ℤ => 2 * (k : ℝ) * π + θ).union
      (Set.countable_range fun k : ℤ => 2 * (k : ℝ) * π - θ)).mono ?_
    intro φ hφ
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hφ
    · exact Or.inl ⟨k, hk.symm⟩
    · exact Or.inr ⟨k, hk.symm⟩
  have hv : ∀ᵐ φ ∂(volume : Measure ℝ), Real.cos θ ≠ Real.cos φ := by
    rw [ae_iff]
    simpa using hc.measure_zero volume
  have hr := ae_restrict_of_ae (s := Ioc (-π) π) hv
  exact (withDensity_absolutelyContinuous _ _).ae_le hr

/-- Square-root ball bounds of the circle pushforward. -/
theorem trigM_good (H : TrigDens a g) (hs : 0 ≤ s) {r : ℝ} (hr : 0 < r) :
    GoodRef ((trigM s g).map (circ r)) := by
  haveI := trigM_finite H hs
  have hF := mul_nonneg hs H.bound_nonneg
  exact goodRef_of_eucl (by positivity) hr.le (circ_eucl hF (trigM_le H hs) hr)

theorem log_norm_integrable {q : Measure ℂ} (h : GoodRef q) (z : ℂ) :
    Integrable (fun w => Real.log ‖z - w‖) q := by
  obtain ⟨_, ⟨C, hC, hb⟩, hh⟩ := h
  exact (logChord_pot_eq hC hb hh z).1

theorem trigM_log_integrable (H : TrigDens a g) (hs : 0 ≤ s) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (fun φ => Real.log ‖z - circ r φ‖) (trigM s g) := by
  have h := log_norm_integrable (trigM_good H hs hr) z
  have hm := (circ_continuous r).measurable
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).mp h

theorem trigM_L_integrable (H : TrigDens a g) (hs : 0 ≤ s) (τ θ : ℝ) :
    Integrable (fun φ => Real.log ‖1 - circ τ (θ - φ)‖) (trigM s g) := by
  simp only [one_sub_circ_norm]
  exact trigM_log_integrable H hs one_pos _

/-! ### The logarithmic potentials -/

/-- The series of the potential. -/
def trigS (a : ℕ → ℝ) (τ θ : ℝ) : ℝ :=
  ∑' k : ℕ, τ ^ (k + 1) * a (k + 1) * Real.cos (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1)

theorem trigM_cos_shift (H : TrigDens a g) (hs : 0 ≤ s) (n : ℕ) (θ : ℝ) :
    ∫ φ, Real.cos (((n : ℝ) + 1) * (θ - φ)) ∂trigM s g =
      2 * π * s * a (n + 1) * Real.cos (((n : ℝ) + 1) * θ) := by
  haveI := trigM_finite H hs
  have e : ∀ φ : ℝ, Real.cos (((n : ℝ) + 1) * (θ - φ)) =
      Real.cos (((n : ℝ) + 1) * θ) * Real.cos (((n : ℝ) + 1) * φ) +
        Real.sin (((n : ℝ) + 1) * θ) * Real.sin (((n : ℝ) + 1) * φ) := by
    intro φ
    rw [mul_sub, Real.cos_sub]
  simp only [e]
  have i1 : Integrable (fun φ : ℝ => Real.cos (((n : ℝ) + 1) * φ)) (trigM s g) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun φ => Real.abs_cos_le_one _)
  have i2 : Integrable (fun φ : ℝ => Real.sin (((n : ℝ) + 1) * φ)) (trigM s g) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun φ => Real.abs_sin_le_one _)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    trigM_cos H hs, trigM_sin H hs]
  ring

theorem trigM_L_lt (H : TrigDens a g) (hs : 0 ≤ s) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ τ (θ - φ)‖ ∂trigM s g = -(2 * π * s) * trigS a τ θ := by
  haveI := trigM_finite H hs
  have hsum := hasSum_int_of_bound (μ := trigM s g)
    (F := fun (k : ℕ) φ => -(τ ^ (k + 1) * Real.cos (((k : ℝ) + 1) * (θ - φ)) / ((k : ℝ) + 1)))
    (f := fun φ => Real.log ‖1 - circ τ (θ - φ)‖) (b := fun k => τ ^ (k + 1))
    (fun n => (by fun_prop : Continuous fun φ : ℝ =>
      -(τ ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1))).aestronglyMeasurable)
    (fun n φ => by
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      rw [abs_neg, abs_div, abs_mul, abs_of_nonneg (pow_nonneg h0 _),
        abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
      have hc := Real.abs_cos_le_one (((n : ℝ) + 1) * (θ - φ))
      rw [div_le_iff₀ (by linarith)]
      have hp := pow_nonneg h0 (n + 1)
      nlinarith [abs_nonneg (Real.cos (((n : ℝ) + 1) * (θ - φ)))])
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one h0 h1))
    (fun φ => log_one_sub_hasSum h0 h1 _)
  have e : ∀ n : ℕ, ∫ φ, -(τ ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1))
      ∂trigM s g = -(2 * π * s) * (τ ^ (n + 1) * a (n + 1) * Real.cos (((n : ℝ) + 1) * θ) /
        ((n : ℝ) + 1)) := by
    intro n
    rw [integral_neg, integral_div, integral_const_mul, trigM_cos_shift H hs]
    ring
  simp only [e] at hsum
  rw [← hsum.tsum_eq, tsum_mul_left]
  rfl

theorem exp_product_norm (θ φ : ℝ) :
    ‖1 - circ 1 (θ - φ)‖ * ‖1 - circ 1 (θ + φ)‖ = 2 * |Real.cos θ - Real.cos φ| := by
  rw [← norm_mul]
  have e : (1 - circ 1 (θ - φ)) * (1 - circ 1 (θ + φ)) =
      -circ 1 θ * (((2 * (Real.cos φ - Real.cos θ) : ℝ) : ℂ)) := by
    unfold circ
    push_cast
    have hE := Complex.exp_ne_zero ((θ : ℂ) * Complex.I)
    have hP := Complex.exp_ne_zero ((φ : ℂ) * Complex.I)
    have h1 : Complex.exp (((θ : ℂ) - φ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) / Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [sub_mul, Complex.exp_sub]
    have h2 : Complex.exp (((θ : ℂ) + φ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I) := by
      rw [add_mul, Complex.exp_add]
    have h3 : ∀ u : ℂ, Complex.exp (-u * Complex.I) = (Complex.exp (u * Complex.I))⁻¹ := by
      intro u
      rw [neg_mul, Complex.exp_neg]
    rw [Complex.cos, Complex.cos, h1, h2, h3, h3]
    field_simp
    ring
  rw [e, norm_mul, norm_neg, circ_norm zero_le_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]

theorem trigM_L_one (H : TrigDens a g) (hs : 0 ≤ s) (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ 1 (θ - φ)‖ ∂trigM s g = -(2 * π * s) * trigS a 1 θ := by
  haveI := trigM_finite H hs
  set m := trigM s g with hm
  set f1 : ℝ → ℝ := fun φ => Real.log ‖1 - circ 1 (θ - φ)‖ with hf1
  set f2 : ℝ → ℝ := fun φ => Real.log ‖1 - circ 1 (θ + φ)‖ with hf2
  have i1 : Integrable f1 m := trigM_L_integrable H hs 1 θ
  have i2 : Integrable f2 m := by
    have h := trigM_L_integrable H hs 1 (-θ)
    refine h.congr (ae_of_all _ fun φ => ?_)
    have : -θ - φ = -(θ + φ) := by ring
    simp only [hf2, this, norm_one_sub_circ_neg]
  have heq : ∫ φ, f2 φ ∂m = ∫ φ, f1 φ ∂m := by
    have := trigM_neg H hs f1
    simpa [hf1, hf2, sub_neg_eq_add] using this
  have hne := trigM_ae_cos (s := s) θ H
  have hsplit : ∀ᵐ φ ∂m, f1 φ + f2 φ = Real.log 2 + Real.log |Real.cos θ - Real.cos φ| := by
    filter_upwards [hne] with φ hφ
    have hd : |Real.cos θ - Real.cos φ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hφ)
    have hp := exp_product_norm θ φ
    have hn1 : ‖1 - circ 1 (θ - φ)‖ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hp
      exact (mul_ne_zero two_ne_zero hd) hp.symm
    have hn2 : ‖1 - circ 1 (θ + φ)‖ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hp
      exact (mul_ne_zero two_ne_zero hd) hp.symm
    simp only [hf1, hf2]
    rw [← Real.log_mul hn1 hn2, hp, Real.log_mul two_ne_zero hd]
  have hint : Integrable (fun φ => Real.log |Real.cos θ - Real.cos φ|) m := by
    have h := (i1.add i2).sub (integrable_const (Real.log 2))
    refine h.congr ?_
    filter_upwards [hsplit] with φ hφ
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hφ]
    ring
  have hmom : ∀ k : ℕ, (∫ φ, (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos φ) ∂m) =
      2 * π * s * a (k + 1) := by
    intro k
    have : ∀ φ : ℝ, (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.cos φ) =
        Real.cos (((k : ℝ) + 1) * φ) := by
      intro φ
      rw [Polynomial.Chebyshev.T_real_cos]
      push_cast
      rfl
    simp only [this]
    exact trigM_cos H hs k
  have hid := cosine_potential_identity m Real.cos Real.continuous_cos.measurable
    (ae_of_all _ fun φ => ⟨Real.neg_one_le_cos φ, Real.cos_le_one φ⟩)
    (x := Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hne hint
    (fun k => ∫ φ, (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval (Real.cos φ) ∂m) (fun _ => rfl)
    (by
      have hb : Summable fun n : ℕ => |2 * π * s| * |a (n + 1)| := H.summ.mul_left _
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
      rw [hmom n, abs_mul]
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      exact div_le_self (by positivity) hn)
  have hbt : barrierTrialT (fun k => ∫ φ, (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval
      (Real.cos φ) ∂m) (Real.cos θ) = 2 * π * s * trigS a 1 θ := by
    unfold barrierTrialT trigS
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    beta_reduce
    rw [hmom k, Polynomial.Chebyshev.T_real_cos]
    push_cast
    simp only [one_pow, one_mul]
    ring
  have hmass : m.real Set.univ = 2 * π * s := trigM_mass H hs
  have htot : ∫ φ, f1 φ ∂m + ∫ φ, f2 φ ∂m =
      m.real Set.univ * Real.log 2 + ∫ φ, Real.log |Real.cos θ - Real.cos φ| ∂m := by
    rw [← integral_add i1 i2, integral_congr_ae hsplit, integral_add (integrable_const _) hint,
      integral_const]
    rfl
  rw [hid, hbt, hmass, heq] at htot
  show ∫ φ, f1 φ ∂m = _
  linarith

theorem trigM_L (H : TrigDens a g) (hs : 0 ≤ s) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ τ (θ - φ)‖ ∂trigM s g = -(2 * π * s) * trigS a τ θ := by
  rcases h1.lt_or_eq with h | h
  · exact trigM_L_lt H hs h0 h θ
  · subst h
    exact trigM_L_one H hs θ

/-- Mirror potential. -/
theorem trigM_mirror (H : TrigDens a g) (hs : 0 ≤ s) {ρ r : ℝ} (h0 : 0 ≤ ρ * r) (h1 : ρ * r ≤ 1)
    (θ : ℝ) :
    ∫ φ, Real.log ‖1 - circ ρ θ * circ r φ‖ ∂trigM s g = -(2 * π * s) * trigS a (ρ * r) θ := by
  have h := trigM_neg H hs (fun φ => Real.log ‖1 - circ (ρ * r) (θ - φ)‖)
  simp only [sub_neg_eq_add] at h
  simp only [circ_mul]
  rw [h]
  exact trigM_L H hs h0 h1 θ

/-- Direct potential on a circle. -/
theorem trigM_pot (H : TrigDens a g) (hs : 0 ≤ s) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (θ : ℝ) :
    ∫ φ, Real.log ‖circ ρ θ - circ r φ‖ ∂trigM s g =
      2 * π * s * Real.log (max ρ r) -
        2 * π * s * trigS a (min ρ r / max ρ r) θ := by
  haveI := trigM_finite H hs
  have hmp : 0 < max ρ r := lt_max_of_lt_left hρ
  have hτ0 : 0 ≤ min ρ r / max ρ r := div_nonneg (le_min hρ.le hr.le) hmp.le
  have hτ1 : min ρ r / max ρ r ≤ 1 := (div_le_one hmp).mpr (min_le_max)
  have hfac : ∀ φ : ℝ, ‖circ ρ θ - circ r φ‖ =
      max ρ r * ‖1 - circ (min ρ r / max ρ r) (θ - φ)‖ := by
    intro φ
    rcases le_total r ρ with h | h
    · rw [max_eq_left h, min_eq_right h]
      have e : circ ρ θ - circ r φ = circ ρ θ * (1 - circ (r / ρ) (-(θ - φ))) := by
        rw [mul_sub, mul_one, circ_mul, mul_div_cancel₀ _ hρ.ne']
        congr 2
        ring
      rw [e, norm_mul, circ_norm hρ.le, norm_one_sub_circ_neg]
    · rw [max_eq_right h, min_eq_left h]
      have e : circ ρ θ - circ r φ = -circ r φ * (1 - circ (ρ / r) (θ - φ)) := by
        have : circ r φ * circ (ρ / r) (θ - φ) = circ ρ θ := by
          rw [circ_mul, mul_div_cancel₀ _ hr.ne']
          congr 1
          ring
        linear_combination -this
      rw [e, norm_mul, norm_neg, circ_norm hr.le]
  have hne : ∀ᵐ φ ∂trigM s g, ‖1 - circ (min ρ r / max ρ r) (θ - φ)‖ ≠ 0 := by
    filter_upwards [trigM_ae_cos (s := s) θ H] with φ hφ h0
    have hz := sub_eq_zero.mp (norm_eq_zero.mp h0)
    have hn : ‖circ (min ρ r / max ρ r) (θ - φ)‖ = 1 := by rw [← hz]; simp
    rw [circ_norm hτ0] at hn
    rw [hn] at hz
    have hre := congrArg Complex.re hz
    rw [circ_re] at hre
    simp only [Complex.one_re, one_mul] at hre
    have hc : Real.cos (θ - φ) = 1 := hre.symm
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hc
    apply hφ
    have : θ = φ + (k : ℝ) * (2 * π) := by linarith
    rw [this, Real.cos_add_int_mul_two_pi]
  have e : ∀ᵐ φ ∂trigM s g, Real.log ‖circ ρ θ - circ r φ‖ =
      Real.log (max ρ r) + Real.log ‖1 - circ (min ρ r / max ρ r) (θ - φ)‖ := by
    filter_upwards [hne] with φ hφ
    rw [hfac, Real.log_mul hmp.ne' hφ]
  rw [integral_congr_ae e, integral_add (integrable_const _) (trigM_L_integrable H hs _ _),
    integral_const, trigM_L H hs hτ0 hτ1, smul_eq_mul]
  show (trigM s g).real Set.univ * _ + _ = _
  rw [trigM_mass H hs]
  ring

/-! ### The density of an auxiliary entry -/

variable {S : CapFields.CapSource}

/-- The symmetrised cubed Poisson density at a phase. -/
def phDens (S : CapFields.CapSource) (ph φ : ℝ) : ℝ := (cubePhi S (φ - ph) + cubePhi S (φ + ph)) / 2

/-- Its coefficients. -/
def phCoef (S : CapFields.CapSource) (ph : ℝ) (k : ℕ) : ℝ := cubeK S k * Real.cos ((k : ℝ) * ph)

theorem cubeK_summable (hε : 0 < S.eps) : Summable fun k : ℕ => |cubeK S (k + 1)| := by
  have h0 := cap_q_pos (S := S)
  have h1 := cap_q_lt_one hε
  have hn : ‖S.q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1
  have s0 : Summable fun k : ℕ => S.q ^ k := summable_geometric_of_lt_one h0.le h1
  have s1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * S.q ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have s2 : Summable fun k : ℕ => ((k : ℝ) ^ 2) * S.q ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have s : Summable fun k : ℕ => cubeK S k := by
    have := (s0.add (s1.mul_left S.strength)).add (s2.mul_left S.curvature)
    refine this.congr fun k => ?_
    unfold cubeK
    ring
  exact ((summable_nat_add_iff 1).mpr s).abs

theorem phDens_trig (hε : 0 < S.eps) (ph : ℝ) : TrigDens (phCoef S ph) (phDens S ph) where
  summ := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) (cubeK_summable hε)
    unfold phCoef
    rw [abs_mul]
    calc _ ≤ |cubeK S (k + 1)| * 1 := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  cont := by
    have h := cubePhi_continuous hε
    unfold phDens
    fun_prop
  nonneg := fun φ => by
    have := cubePhi_nonneg hε (φ - ph)
    have := cubePhi_nonneg hε (φ + ph)
    unfold phDens
    positivity
  series := fun φ => by
    have h := ((cubePhi_hasSum hε (φ - ph)).add (cubePhi_hasSum hε (φ + ph))).div_const 2
    convert h using 1
    · funext k
      unfold phCoef
      have e1 : ((k : ℝ) + 1) * (φ - ph) = ((k : ℝ) + 1) * φ - ((k : ℝ) + 1) * ph := by ring
      have e2 : ((k : ℝ) + 1) * (φ + ph) = ((k : ℝ) + 1) * φ + ((k : ℝ) + 1) * ph := by ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]
      push_cast
      ring
    · unfold phDens
      ring

/-- `trigS` is the auxiliary series with the coefficients of the cap fields. -/
theorem trigS_coef (ph τ θ : ℝ) :
    -trigS (phCoef S ph) τ θ = ∑' k : ℕ, S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  unfold trigS
  rw [← tsum_neg]
  refine tsum_congr fun k => ?_
  unfold phCoef cubeK CapFields.CapSource.coef
  push_cast
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

local notation "π" => Real.pi

/-! ### Potentials of sums and pushforwards -/

theorem planarPot_add {q₁ q₂ : Measure ℂ} (h₁ : GoodRef q₁) (h₂ : GoodRef q₂) (z : ℂ) :
    planarPot (q₁ + q₂) z = planarPot q₁ z + planarPot q₂ z := by
  unfold planarPot
  exact integral_add_measure (log_norm_integrable h₁ z) (log_norm_integrable h₂ z)

theorem goodRef_list {ι : Type*} (l : List ι) (m : ι → Measure ℂ) (h : ∀ i ∈ l, GoodRef (m i)) :
    GoodRef (l.map m).sum := by
  induction l with
  | nil => exact GoodRef.zero
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem planarPot_zero (z : ℂ) : planarPot 0 z = 0 := by
  simp [planarPot]

theorem planarPot_list {ι : Type*} (l : List ι) (m : ι → Measure ℂ) (h : ∀ i ∈ l, GoodRef (m i))
    (z : ℂ) : planarPot (l.map m).sum z = (l.map fun i => planarPot (m i) z).sum := by
  induction l with
  | nil => simp [planarPot_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [planarPot_add (h a (by simp)) (goodRef_list l m fun i hi => h i (by simp [hi])),
      ih fun i hi => h i (by simp [hi])]

theorem real_univ_list {ι : Type*} (l : List ι) (m : ι → Measure ℂ)
    (h : ∀ i ∈ l, IsFiniteMeasure (m i)) :
    IsFiniteMeasure (l.map m).sum ∧
      (l.map m).sum.real Set.univ = (l.map fun i => (m i).real Set.univ).sum := by
  induction l with
  | nil => exact ⟨by simpa using (inferInstance : IsFiniteMeasure (0 : Measure ℂ)), by simp⟩
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih fun i hi => h i (by simp [hi])
    haveI := h a (by simp)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨inferInstance, ?_⟩
    rw [measureReal_add_apply, i2]

theorem planarPot_map {α : Type*} [MeasurableSpace α] {m : Measure α} {f : α → ℂ}
    (hf : Measurable f) (z : ℂ) :
    planarPot (m.map f) z = ∫ a, Real.log ‖z - f a‖ ∂m := by
  unfold planarPot
  refine integral_map hf.aemeasurable ?_
  exact (Real.measurable_log.comp (measurable_const.sub measurable_id).norm).aestronglyMeasurable

theorem integral_split4 {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    {A B : α → ℝ} (hA : Integrable A m) (hB : Integrable B m) (a b c : ℝ) :
    ∫ φ, (A φ + B φ - a - b - c) ∂m =
      (∫ φ, A φ ∂m) + (∫ φ, B φ ∂m) - m.real Set.univ * (a + b + c) := by
  have e : (fun φ => A φ + B φ - a - b - c) = fun φ => A φ + (B φ - (a + b + c)) := by
    funext φ
    ring
  have h1 : ∫ φ, (A φ + (B φ - (a + b + c))) ∂m =
      (∫ φ, A φ ∂m) + ∫ φ, (B φ - (a + b + c)) ∂m :=
    integral_add (f := A) (g := fun φ => B φ - (a + b + c)) hA (hB.sub (integrable_const _))
  have h2 : ∫ φ, (B φ - (a + b + c)) ∂m = (∫ φ, B φ ∂m) - ∫ _φ, (a + b + c) ∂m :=
    integral_sub (f := B) (g := fun _ => a + b + c) hB (integrable_const _)
  rw [e, h1, h2, integral_const, smul_eq_mul]
  ring

/-! ### Auxiliary entries -/

variable {S : CapSource}

/-- The angular measure of an auxiliary entry. -/
def auxMu (S : CapSource) (e : AuxEntry) : Measure ℝ :=
  trigM (e.w / (2 * π)) (phDens S e.phase)

/-- The positive auxiliary circle. -/
def auxP (S : CapSource) (e : AuxEntry) : Measure ℂ := (auxMu S e).map (circ (S.rad e.rad))

/-- The negative auxiliary curve in the Joukowski coordinate. -/
def auxJ (S : CapSource) (e : AuxEntry) : Measure ℂ :=
  (auxMu S e).map fun φ => joukowski (circ (S.rad e.rad) φ)

theorem scale_nonneg (e : AuxEntry) : 0 ≤ e.w / (2 * π) :=
  div_nonneg e.w_nonneg (by positivity)

theorem two_pi_scale (e : AuxEntry) : 2 * π * (e.w / (2 * π)) = e.w := by
  have := Real.pi_pos
  field_simp

theorem rad_pos (S : CapSource) (i : ℕ) : 0 < S.rad i := Real.exp_pos _

theorem auxMu_finite (hε : 0 < S.eps) (e : AuxEntry) : IsFiniteMeasure (auxMu S e) :=
  trigM_finite (phDens_trig hε e.phase) (scale_nonneg e)

theorem auxMu_mass (hε : 0 < S.eps) (e : AuxEntry) : (auxMu S e).real Set.univ = e.w := by
  unfold auxMu
  rw [trigM_mass (phDens_trig hε e.phase) (scale_nonneg e), two_pi_scale]

theorem joukowski_circ_continuous {r : ℝ} (hr : 0 < r) :
    Continuous fun φ => joukowski (circ r φ) := by
  have hc := circ_continuous r
  have hne : ∀ φ, circ r φ ≠ 0 := fun φ => by
    rw [← norm_pos_iff, circ_norm hr.le]
    exact hr
  unfold joukowski
  exact (hc.add (hc.inv₀ hne)).div_const _

theorem auxP_good (hε : 0 < S.eps) (e : AuxEntry) : GoodRef (auxP S e) :=
  trigM_good (phDens_trig hε e.phase) (scale_nonneg e) (rad_pos S _)

theorem auxJ_good (hε : 0 < S.eps) (e : AuxEntry) : GoodRef (auxJ S e) := by
  have H := phDens_trig (S := S) hε e.phase
  have hs := scale_nonneg e
  haveI := trigM_finite H hs
  haveI : IsFiniteMeasure (auxMu S e) := auxMu_finite hε e
  haveI : IsFiniteMeasure (auxJ S e) := by
    unfold auxJ
    infer_instance
  have hF := mul_nonneg hs H.bound_nonneg
  have hr := rad_pos S e.rad
  exact goodRef_of_eucl (by positivity) (by positivity) (jcirc_eucl hF (trigM_le H hs) hr)

theorem auxP_mass (hε : 0 < S.eps) (e : AuxEntry) : (auxP S e).real Set.univ = e.w := by
  haveI := auxMu_finite (S := S) hε e
  unfold auxP
  rw [map_measureReal_apply (circ_continuous _).measurable MeasurableSet.univ, Set.preimage_univ,
    auxMu_mass hε]

theorem auxJ_mass (hε : 0 < S.eps) (e : AuxEntry) : (auxJ S e).real Set.univ = e.w := by
  haveI := auxMu_finite (S := S) hε e
  unfold auxJ
  rw [map_measureReal_apply (joukowski_circ_continuous (rad_pos S _)).measurable
    MeasurableSet.univ, Set.preimage_univ, auxMu_mass hε]

/-- The cosine series of an auxiliary entry. -/
def auxSer (S : CapSource) (ph τ θ : ℝ) : ℝ :=
  ∑' k : ℕ, S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph) *
    Real.cos (((k + 1 : ℕ) : ℝ) * θ)

theorem aux_direct (hε : 0 < S.eps) (e : AuxEntry) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    planarPot (auxP S e) (circ ρ θ) =
      e.w * (Real.log (max ρ (S.rad e.rad)) +
        auxSer S e.phase (min ρ (S.rad e.rad) / max ρ (S.rad e.rad)) θ) := by
  unfold auxP
  rw [planarPot_map (circ_continuous _).measurable]
  unfold auxMu
  rw [trigM_pot (phDens_trig hε e.phase) (scale_nonneg e) hρ (rad_pos S _), two_pi_scale]
  unfold auxSer
  rw [← trigS_coef]
  ring

/-- Off the cosine null set, the two factors of a Joukowski difference do not vanish. -/
theorem jouk_split {ρ r θ φ : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hc : Real.cos θ ≠ Real.cos φ) :
    Real.log ‖joukowski (circ ρ θ) - joukowski (circ r φ)‖ =
      Real.log ‖circ ρ θ - circ r φ‖ + Real.log ‖1 - circ ρ θ * circ r φ‖ - Real.log 2 -
        Real.log ρ - Real.log r := by
  have hz : circ ρ θ ≠ 0 := by
    rw [← norm_pos_iff, circ_norm hρ.le]
    exact hρ
  have ht : circ r φ ≠ 0 := by
    rw [← norm_pos_iff, circ_norm hr.le]
    exact hr
  have h1 : circ ρ θ - circ r φ ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hn := congrArg norm he
    rw [circ_norm hρ.le, circ_norm hr.le] at hn
    have hre := congrArg Complex.re he
    rw [circ_re, circ_re, hn] at hre
    exact hc (mul_left_cancel₀ hr.ne' hre)
  have h2 : 1 - circ ρ θ * circ r φ ≠ 0 := by
    intro h
    have he : circ (ρ * r) (θ + φ) = 1 := by
      rw [← circ_mul]
      linear_combination -h
    have hn := congrArg norm he
    rw [circ_norm (by positivity)] at hn
    simp only [norm_one] at hn
    have hre := congrArg Complex.re he
    rw [circ_re, hn] at hre
    simp only [one_mul, Complex.one_re] at hre
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hre
    apply hc
    have : θ = -φ + (k : ℝ) * (2 * π) := by linarith
    rw [this, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  have e : joukowski (circ ρ θ) - joukowski (circ r φ) =
      -((circ ρ θ - circ r φ) * (1 - circ ρ θ * circ r φ) / (2 * (circ ρ θ * circ r φ))) := by
    rw [joukowski_factor hz ht]
    field_simp
    ring
  rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_mul, circ_norm hρ.le, circ_norm hr.le,
    Complex.norm_ofNat, Real.log_div (by positivity) (by positivity),
    Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2),
    Real.log_mul two_ne_zero (by positivity), Real.log_mul hρ.ne' hr.ne']
  ring

theorem aux_fold (hε : 0 < S.eps) (e : AuxEntry) {ρ : ℝ} (hρ : 0 < ρ)
    (hρr : ρ * S.rad e.rad ≤ 1) (θ : ℝ) :
    planarPot (auxJ S e) (joukowski (circ ρ θ)) =
      e.w * (Real.log (max ρ (S.rad e.rad)) +
        auxSer S e.phase (min ρ (S.rad e.rad) / max ρ (S.rad e.rad)) θ +
        auxSer S e.phase (ρ * S.rad e.rad) θ - Real.log 2 - Real.log ρ -
        Real.log (S.rad e.rad)) := by
  have H := phDens_trig (S := S) hε e.phase
  have hs := scale_nonneg e
  have hr := rad_pos S e.rad
  haveI := trigM_finite H hs
  set r := S.rad e.rad with hrdef
  unfold auxJ
  rw [planarPot_map (joukowski_circ_continuous hr).measurable]
  unfold auxMu
  have hsplit : ∀ᵐ φ ∂trigM (e.w / (2 * π)) (phDens S e.phase),
      Real.log ‖joukowski (circ ρ θ) - joukowski (circ r φ)‖ =
        Real.log ‖circ ρ θ - circ r φ‖ + Real.log ‖1 - circ ρ θ * circ r φ‖ - Real.log 2 -
          Real.log ρ - Real.log r := by
    filter_upwards [trigM_ae_cos (s := e.w / (2 * π)) θ H] with φ hφ
    exact jouk_split hρ hr hφ
  have i1 := trigM_log_integrable H hs hr (circ ρ θ)
  have i2 : Integrable (fun φ => Real.log ‖1 - circ ρ θ * circ r φ‖)
      (trigM (e.w / (2 * π)) (phDens S e.phase)) := by
    refine (trigM_L_integrable H hs (ρ * r) (-θ)).congr (ae_of_all _ fun φ => ?_)
    have : -θ - φ = -(θ + φ) := by ring
    simp only [this, norm_one_sub_circ_neg, circ_mul]
  have hmass := trigM_mass H hs
  rw [integral_congr_ae hsplit, integral_split4 i1 i2, hmass, two_pi_scale,
    trigM_pot H hs hρ hr, trigM_mirror H hs (by positivity) hρr, two_pi_scale]
  unfold auxSer
  rw [← trigS_coef, ← trigS_coef]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

/-! ### Cells in the two planes -/

/-- A cell in the physical coordinate. -/
def cellP (c : YCell) : Measure ℂ := (cellM c).map fun Y => ((physX Y : ℝ) : ℂ)

/-- A cell in the Joukowski coordinate `Y/2`. -/
def cellJ (c : YCell) : Measure ℂ := (cellM c).map fun Y => ((Y / 2 : ℝ) : ℂ)

theorem physX_ofReal_measurable : Measurable fun Y => ((physX Y : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp physX_measurable

theorem half_ofReal_measurable : Measurable fun Y : ℝ => ((Y / 2 : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (by fun_prop)

theorem cell_abs_le (c : YCell) {Y : ℝ} (hY : Y ∈ Icc c.lo c.hi) : |Y| ≤ |c.lo| + |c.hi| := by
  have h1 := neg_abs_le c.lo
  have h2 := le_abs_self c.hi
  have h3 := abs_nonneg c.lo
  have h4 := abs_nonneg c.hi
  rw [abs_le]
  exact ⟨by linarith [hY.1], by linarith [hY.2]⟩

theorem physX_lip {c : YCell} (hc : RowCell c) {Y Y' : ℝ} (hY : Y ∈ Icc c.lo c.hi)
    (hY' : Y' ∈ Icc c.lo c.hi) :
    |Y - Y'| ≤ (1 + (|c.lo| + |c.hi| + 1) ^ 2) * |physX Y - physX Y'| := by
  obtain ⟨a0, a1, a2⟩ := physX_mem hc hY
  obtain ⟨b0, b1, b2⟩ := physX_mem hc hY'
  set B := |c.lo| + |c.hi| + 1 with hB
  have hYb := cell_abs_le c hY
  have hYb' := cell_abs_le c hY'
  have inv : ∀ {X W : ℝ}, X + 1 / X = W → |X| ≤ 1 → |W| ≤ |c.lo| + |c.hi| → |1 / X| ≤ B := by
    intro X W h1 h2 h3
    have : 1 / X = W - X := by linarith
    rw [this]
    calc |W - X| ≤ |W| + |X| := abs_sub _ _
      _ ≤ B := by rw [hB]; linarith
  have i1 := inv a2 a1 hYb
  have i2 := inv b2 b1 hYb'
  have e : Y - Y' = (physX Y - physX Y') * (1 - (1 / physX Y) * (1 / physX Y')) := by
    have e0 : Y - Y' = (physX Y + 1 / physX Y) - (physX Y' + 1 / physX Y') := by rw [a2, b2]
    rw [e0]
    field_simp
    ring
  rw [e, abs_mul, mul_comm]
  have hb : |1 - (1 / physX Y) * (1 / physX Y')| ≤ 1 + B ^ 2 := by
    calc _ ≤ |(1 : ℝ)| + |(1 / physX Y) * (1 / physX Y')| := abs_sub _ _
      _ = 1 + |1 / physX Y| * |1 / physX Y'| := by rw [abs_one, abs_mul]
      _ ≤ 1 + B * B := by gcongr
      _ = _ := by ring
  gcongr

theorem cellP_good {c : YCell} (hc : RowCell c) : GoodRef (cellP c) := by
  haveI : IsFiniteMeasure (cellP c) := by
    unfold cellP
    infer_instance
  have h := cell_eucl c physX_measurable
    (K := 1 + (|c.lo| + |c.hi| + 1) ^ 2) (R := 1) (by positivity)
    (fun Y hY Y' hY' => physX_lip hc hY hY') (fun Y hY => (physX_mem hc hY).2.1)
  have hs := cell_scale_nonneg c
  exact goodRef_of_eucl (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (by positivity))
    c.w_nonneg) zero_le_one h

theorem cellJ_good (c : YCell) : GoodRef (cellJ c) := by
  haveI : IsFiniteMeasure (cellJ c) := by
    unfold cellJ
    infer_instance
  have h := cell_eucl c (f := fun Y => Y / 2) (by fun_prop) (K := 2) (R := |c.lo| + |c.hi|)
    (by norm_num)
    (fun Y _ Y' _ => by
      have : Y / 2 - Y' / 2 = (Y - Y') / 2 := by ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith)
    (fun Y hY => by
      have := cell_abs_le c hY
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := abs_nonneg Y
      linarith)
  have hs := cell_scale_nonneg c
  exact goodRef_of_eucl (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (by norm_num))
    c.w_nonneg) (by positivity) h

theorem cellP_mass (c : YCell) : (cellP c).real Set.univ = c.w := by
  unfold cellP
  rw [map_measureReal_apply physX_ofReal_measurable MeasurableSet.univ, Set.preimage_univ,
    cellM_real_univ]

theorem cellJ_mass (c : YCell) : (cellJ c).real Set.univ = c.w := by
  unfold cellJ
  rw [map_measureReal_apply half_ofReal_measurable MeasurableSet.univ, Set.preimage_univ,
    cellM_real_univ]

/-! ### Norm formulas -/

theorem circ_im (r φ : ℝ) : (circ r φ).im = r * Real.sin φ := by
  unfold circ
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem circ_sub_sq (ρ θ x : ℝ) :
    ‖circ ρ θ - (x : ℂ)‖ ^ 2 = ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, circ_re, circ_im,
    sub_zero]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith

theorem one_sub_circ_sq (ρ θ x : ℝ) :
    ‖1 - circ ρ θ * (x : ℂ)‖ ^ 2 = 1 - 2 * ρ * x * Real.cos θ + ρ ^ 2 * x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, circ_re, circ_im, mul_zero, sub_zero,
    add_zero, zero_sub]
  have := Real.sin_sq_add_cos_sq θ
  have e : ρ ^ 2 * x ^ 2 = ρ ^ 2 * x ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by rw [this, mul_one]
  rw [e]
  ring

theorem log_norm_half (z : ℂ) {v : ℝ} (h : ‖z‖ ^ 2 = v) : Real.log ‖z‖ = (1 / 2) * Real.log v := by
  rw [← h, Real.log_pow]
  push_cast
  ring

/-! ### Potentials of one cell -/

theorem cellP_pot (c : YCell) (z : ℂ) :
    planarPot (cellP c) z = ∫ Y, Real.log ‖z - ((physX Y : ℝ) : ℂ)‖ ∂cellM c :=
  planarPot_map physX_ofReal_measurable z

theorem cellJ_pot (c : YCell) (z : ℂ) :
    planarPot (cellJ c) z = ∫ Y, Real.log ‖z - ((Y / 2 : ℝ) : ℂ)‖ ∂cellM c :=
  planarPot_map half_ofReal_measurable z

theorem real_norm_sub (a b : ℝ) : ‖(a : ℂ) - (b : ℂ)‖ = |a - b| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem cell_row_pot {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    planarPot (cellP c) (x : ℂ) =
      c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x) + c.w * Real.log |x| -
        ∫ Y, Real.log |1 - x * physX Y| ∂cellM c := by
  have h := (cell_row_recombine hc hx hx0).2
  rw [cellP_pot]
  simp only [real_norm_sub]
  linarith

theorem cell_refl_integrable {c : YCell} (hc : RowCell c) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Integrable (fun Y => Real.log |1 - y * physX Y|) (cellM c) := by
  apply cell_integrable_of_continuousOn
  have hcont := physX_continuousOn_cell hc
  have h1 : ContinuousOn (fun Y => 1 - y * physX Y) (Icc c.lo c.hi) :=
    continuousOn_const.sub (continuousOn_const.mul hcont)
  exact (h1.abs).log fun Y hY => abs_ne_zero.mpr (one_sub_mul_ne hy (physX_mem hc hY).2.1)

theorem cell_near_pot {c : YCell} (hc : RowCell c) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    planarPot (cellP c) ((1 / y : ℝ) : ℂ) =
      -(c.w * Real.log y) + ∫ Y, Real.log |1 - y * physX Y| ∂cellM c := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hy0 := hy.1
  rw [cellP_pot]
  have e : ∀ᵐ Y ∂cellM c, Real.log ‖((1 / y : ℝ) : ℂ) - ((physX Y : ℝ) : ℂ)‖ =
      Real.log |1 - y * physX Y| - Real.log y := by
    filter_upwards [cell_ae_mem c] with Y hY
    have h1 := one_sub_mul_ne hy' (physX_mem hc hY).2.1
    have e1 : 1 / y - physX Y = (1 - y * physX Y) / y := by
      field_simp
    rw [real_norm_sub, e1, abs_div, abs_of_pos hy0, Real.log_div (abs_ne_zero.mpr h1) hy0.ne']
  rw [integral_congr_ae e, integral_sub (cell_refl_integrable hc hy') (integrable_const _),
    integral_const, smul_eq_mul, cellM_real_univ]
  ring

theorem cell_fold_row (c : YCell) (x : ℝ) :
    planarPot (cellJ c) (((x + 1 / x) / 2 : ℝ) : ℂ) = c.pot (x + 1 / x) - c.w * Real.log 2 := by
  rw [cellJ_pot]
  have e : ∀ᵐ Y ∂cellM c, Real.log ‖(((x + 1 / x) / 2 : ℝ) : ℂ) - ((Y / 2 : ℝ) : ℂ)‖ =
      Real.log |x + 1 / x - Y| - Real.log 2 := by
    filter_upwards [cell_ae_ne c (x + 1 / x)] with Y hY
    have h1 : x + 1 / x - Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
    have e1 : (x + 1 / x) / 2 - Y / 2 = (x + 1 / x - Y) / 2 := by ring
    rw [real_norm_sub, e1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.log_div (abs_ne_zero.mpr h1) two_ne_zero]
  rw [integral_congr_ae e, integral_sub (cell_integrable_log c _) (integrable_const _),
    integral_const, smul_eq_mul, cellM_real_univ]
  unfold YCell.pot
  rw [cell_avg_eq]

theorem cell_phys_eq (c : YCell) (f : ℝ → ℝ) : c.phys f = ∫ Y, f (physX Y) ∂cellM c := by
  unfold YCell.phys
  exact cell_avg_eq c _

theorem cell_circ_pot (c : YCell) (ρ θ : ℝ) :
    planarPot (cellP c) (circ ρ θ) =
      c.phys fun x => (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2) := by
  rw [cellP_pot, cell_phys_eq]
  exact integral_congr_ae (ae_of_all _ fun Y => log_norm_half _ (circ_sub_sq ρ θ _))

theorem cell_log_integrable {c : YCell} (hc : RowCell c) (z : ℂ) :
    Integrable (fun Y => Real.log ‖z - ((physX Y : ℝ) : ℂ)‖) (cellM c) := by
  have h := log_norm_integrable (cellP_good hc) z
  exact (integrable_map_measure h.aestronglyMeasurable physX_ofReal_measurable.aemeasurable).mp h

theorem cell_log_phys_integrable {c : YCell} (hc : RowCell c) :
    Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
  apply cell_integrable_of_continuousOn
  exact ((physX_continuousOn_cell hc).abs).log fun Y hY => abs_ne_zero.mpr (physX_mem hc hY).1

theorem cell_circ_fold {c : YCell} (hc : RowCell c) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    planarPot (cellJ c) (joukowski (circ ρ θ)) =
      (c.phys fun x => (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2)) +
      (c.phys fun x => (1 / 2) * Real.log (1 - 2 * ρ * x * Real.cos θ + ρ ^ 2 * x ^ 2)) -
      c.w * (Real.log 2 + Real.log ρ) - c.phys (fun u => Real.log |u|) := by
  set γ := circ ρ θ with hγ
  have hγ0 : γ ≠ 0 := by
    rw [hγ, ← norm_pos_iff, circ_norm hρ.le]
    exact hρ
  have hγn : ‖γ‖ = ρ := circ_norm hρ.le θ
  have split : ∀ᵐ Y ∂cellM c, Real.log ‖joukowski γ - ((Y / 2 : ℝ) : ℂ)‖ =
      Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ) - Real.log |physX Y| := by
    filter_upwards [cell_ae_mem c, cell_ae_ne c (2 * (joukowski γ).re)] with Y hY hne
    obtain ⟨a0, -, a2⟩ := physX_mem hc hY
    have hX : ((physX Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast a0
    have hJ : joukowski ((physX Y : ℝ) : ℂ) = ((Y / 2 : ℝ) : ℂ) := by
      have e0 : ((Y / 2 : ℝ) : ℂ) = (((physX Y + 1 / physX Y) / 2 : ℝ) : ℂ) := by rw [a2]
      rw [e0]
      unfold joukowski
      push_cast
      rw [one_div]
    have hd : joukowski γ - ((Y / 2 : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hne
      have := congrArg Complex.re (sub_eq_zero.mp h)
      rw [Complex.ofReal_re] at this
      rw [this]
      ring
    have e : joukowski γ - ((Y / 2 : ℝ) : ℂ) =
        -((γ - ((physX Y : ℝ) : ℂ)) * (1 - γ * ((physX Y : ℝ) : ℂ)) /
          (2 * (γ * ((physX Y : ℝ) : ℂ)))) := by
      rw [← hJ, joukowski_factor hγ0 hX]
      field_simp
      ring
    have h1 : γ - ((physX Y : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hd
      rw [e, h]
      simp
    have h2 : 1 - γ * ((physX Y : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hd
      rw [e, h]
      simp
    rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_mul, hγn, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs,
      Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2))
        (mul_ne_zero two_ne_zero (mul_ne_zero hρ.ne' (abs_ne_zero.mpr a0))),
      Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2),
      Real.log_mul two_ne_zero (mul_ne_zero hρ.ne' (abs_ne_zero.mpr a0)),
      Real.log_mul hρ.ne' (abs_ne_zero.mpr a0)]
    ring
  have i1 := cell_log_integrable hc γ
  have i2 : Integrable (fun Y => Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖) (cellM c) := by
    have h := (cell_log_integrable hc γ⁻¹).add (integrable_const (Real.log ρ))
    refine h.congr ?_
    filter_upwards [cell_ae_mem c, cell_ae_ne c (2 * (joukowski γ).re)] with Y hY hne
    simp only [Pi.add_apply]
    have e : 1 - γ * ((physX Y : ℝ) : ℂ) = γ * (γ⁻¹ - ((physX Y : ℝ) : ℂ)) := by
      rw [mul_sub, mul_inv_cancel₀ hγ0]
    by_cases hz : γ⁻¹ - ((physX Y : ℝ) : ℂ) = 0
    · exfalso
      apply hne
      obtain ⟨a0, -, a2⟩ := physX_mem hc hY
      have hg : γ = (((physX Y : ℝ) : ℂ))⁻¹ := by
        rw [← sub_eq_zero.mp hz, inv_inv]
      have hJ : joukowski γ = ((Y / 2 : ℝ) : ℂ) := by
        have e0 : ((Y / 2 : ℝ) : ℂ) = (((physX Y + 1 / physX Y) / 2 : ℝ) : ℂ) := by rw [a2]
        rw [e0]
        unfold joukowski
        rw [hg, inv_inv]
        push_cast
        rw [one_div]
        ring
      rw [hJ, Complex.ofReal_re]
      ring
    · rw [e, norm_mul, hγn, Real.log_mul hρ.ne' (norm_ne_zero_iff.mpr hz)]
      ring
  have i3 := cell_log_phys_integrable hc
  rw [cellJ_pot, integral_congr_ae split]
  have s1 : ∫ Y, (Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ) - Real.log |physX Y|) ∂cellM c =
      (∫ Y, Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ ∂cellM c) +
        (∫ Y, Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ ∂cellM c) -
        c.w * (Real.log 2 + Real.log ρ) - ∫ Y, Real.log |physX Y| ∂cellM c := by
    have h3 : ∫ Y, (Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ) - Real.log |physX Y|) ∂cellM c =
        (∫ Y, (Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ + Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ -
        (Real.log 2 + Real.log ρ)) ∂cellM c) - ∫ Y, Real.log |physX Y| ∂cellM c :=
      integral_sub ((i1.add i2).sub (integrable_const _)) i3
    have h4 := integral_split4 i1 i2 (Real.log 2 + Real.log ρ) 0 0 (m := cellM c)
    simp only [sub_zero, add_zero] at h4
    rw [h3, h4, cellM_real_univ]
  rw [s1, cell_phys_eq, cell_phys_eq, cell_phys_eq]
  have e1 : ∫ Y, Real.log ‖γ - ((physX Y : ℝ) : ℂ)‖ ∂cellM c =
      ∫ Y, (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * physX Y * Real.cos θ + physX Y ^ 2) ∂cellM c :=
    integral_congr_ae (ae_of_all _ fun Y => log_norm_half _ (circ_sub_sq ρ θ _))
  have e2 : ∫ Y, Real.log ‖1 - γ * ((physX Y : ℝ) : ℂ)‖ ∂cellM c =
      ∫ Y, (1 / 2) * Real.log (1 - 2 * ρ * physX Y * Real.cos θ + ρ ^ 2 * physX Y ^ 2) ∂cellM c :=
    integral_congr_ae (ae_of_all _ fun Y => log_norm_half _ (one_sub_circ_sq ρ θ _))
  rw [e1, e2]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

/-! ## Moment prefixes -/

/-- The prefix `1..J` of a moment sequence; the index `0` is dropped. -/
def momentPrefix (J : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≠ 0 ∧ k ≤ J then u k else 0

theorem momentPrefix_abs_summable (J : ℕ) (u : ℕ → ℝ) :
    Summable (fun k => |momentPrefix J u k|) := by
  apply (summable_nat_add_iff (J+1)).mp
  have hn (n : ℕ) : ¬(n+(J+1) ≠ 0 ∧ n+(J+1) ≤ J) := by omega
  simpa only [momentPrefix, hn, if_false, abs_zero] using
    (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))

theorem momentPrefix_succ (J : ℕ) (u : ℕ → ℝ) (n : ℕ) :
    momentPrefix J u (n+1) = if n < J then u (n+1) else 0 := by
  unfold momentPrefix
  by_cases h : n < J
  · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- A `tsum` over the shifted index of a prefix is the finite sum. -/
theorem tsum_momentPrefix (J : ℕ) (u : ℕ → ℝ) (c : ℕ → ℝ) :
    (∑' n, momentPrefix J u (n+1) * c n) = ∑ n ∈ range J, u (n+1) * c n := by
  rw [tsum_eq_sum (s := range J)]
  · exact Finset.sum_congr rfl fun n hn => by
      rw [momentPrefix_succ, if_pos (Finset.mem_range.mp hn)]
  · intro n hn
    rw [momentPrefix_succ, if_neg (by simpa using hn), zero_mul]

theorem barrierTrialT_prefix (J : ℕ) (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialT (momentPrefix J u) x =
      ∑ n ∈ range J, u (n+1) * (Polynomial.Chebyshev.T ℝ ((n+1:ℕ):ℤ)).eval x / ((n+1:ℕ):ℝ) := by
  unfold barrierTrialT
  have h := tsum_momentPrefix J u
    (fun n => (Polynomial.Chebyshev.T ℝ ((n+1:ℕ):ℤ)).eval x / ((n+1:ℕ):ℝ))
  simpa only [mul_div_assoc] using h

theorem barrierTrialS_prefix (J : ℕ) (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialS (momentPrefix J u) x =
      ∑ n ∈ range J, u (n+1) * x^(n+1) / ((n+1:ℕ):ℝ) := by
  unfold barrierTrialS
  have h := tsum_momentPrefix J u (fun n => x^(n+1) / ((n+1:ℕ):ℝ))
  simpa only [mul_div_assoc] using h

theorem barrierTrialNormSq_prefix_le (J : ℕ) (u : ℕ → ℝ)
    (hu : Summable (fun n => u (n+1)^2 / ((n+1:ℕ):ℝ))) :
    barrierTrialNormSq (momentPrefix J u) ≤ barrierTrialNormSq u := by
  unfold barrierTrialNormSq
  have hsum : (∑' n, momentPrefix J u (n+1)^2 / ((n+1:ℕ):ℝ)) =
      ∑ n ∈ range J, u (n+1)^2 / ((n+1:ℕ):ℝ) := by
    rw [tsum_eq_sum (s := range J)]
    · exact Finset.sum_congr rfl fun n hn => by
        rw [momentPrefix_succ, if_pos (Finset.mem_range.mp hn)]
    · intro n hn
      rw [momentPrefix_succ, if_neg (by simpa using hn)]
      simp
  rw [hsum]
  exact hu.sum_le_tsum _ (fun n _ => by positivity)

/-! ## Uniform passage from a prefix to the full weighted moment field -/

theorem weighted_moment_uniform {β : Type*} (u : ℕ → ℝ)
    (phi : ℕ → β → ℝ) (S : Set β)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ)))
    (hphi : ∀ n x, x ∈ S → |phi n x| ≤ 1) :
    TendstoUniformlyOn
      (fun J x => ∑ n ∈ Finset.range J, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ))
      (fun x => ∑' n, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ)) atTop S := by
  apply tendstoUniformlyOn_tsum_nat hu
  intro n x hx
  have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  have hb := mul_le_mul_of_nonneg_left (hphi (n+1) x hx) (abs_nonneg (u (n+1)))
  simpa only [mul_one] using hb

/-- One prefix length works for every point, before any point is chosen. -/
theorem one_prefix_before_all_points {β : Type*} (u : ℕ → ℝ)
    (phi : ℕ → β → ℝ) (S : Set β)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ)))
    (hphi : ∀ n x, x ∈ S → |phi n x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ x ∈ S,
      |(∑' n, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ)) -
        (∑ n ∈ Finset.range J, u (n+1)*phi (n+1) x / ((n+1:ℕ):ℝ))| < ε := by
  have ht := weighted_moment_uniform u phi S hu hphi
  simpa only [Real.dist_eq] using (Metric.tendstoUniformlyOn_iff.mp ht) ε hε

theorem T_prefix_uniform (u : ℕ → ℝ)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ x ∈ Icc (-1:ℝ) 1,
      |barrierTrialT u x - barrierTrialT (momentPrefix J u) x| < ε := by
  have h := one_prefix_before_all_points u
    (fun n x => (Polynomial.Chebyshev.T ℝ (n:ℤ)).eval x) (Icc (-1:ℝ) 1) hu
    (fun n x hx => Polynomial.Chebyshev.abs_eval_T_real_le_one (n:ℤ) (abs_le.mpr hx)) hε
  filter_upwards [h] with J hJ x hx
  rw [barrierTrialT_prefix]
  exact hJ x hx

theorem S_prefix_uniform (u : ℕ → ℝ)
    (hu : Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J in atTop, ∀ x ∈ Icc (-1:ℝ) 1,
      |barrierTrialS u x - barrierTrialS (momentPrefix J u) x| < ε := by
  have h := one_prefix_before_all_points u
    (fun n x => x^n) (Icc (-1:ℝ) 1) hu
    (fun n x hx => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)) hε
  filter_upwards [h] with J hJ x hx
  rw [barrierTrialS_prefix]
  exact hJ x hx

/-! ## The free pin tangent at a reference pair -/

/-- Reference intercept `-Q(F*,C*)` in moment form, at reference mass `b`. -/
def anchorIntercept (b : ℝ) (a v : ℕ → ℝ) : ℝ :=
  (3/2:ℝ)*b^2*Real.log 2 + barrierTrialNormSq a + barrierTrialNormSq v/2

/-- Derivative of `Q` in the free-row variable. -/
def anchorRowField (b : ℝ) (a v : ℕ → ℝ) (x : ℝ) : ℝ :=
  -b*Real.log 2 - 2*barrierTrialT a x - barrierTrialS v x

/-- Derivative of `Q` in the free-column variable. -/
def anchorColumnField (b : ℝ) (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  -2*b*Real.log 2 + 2*barrierTrialT v s


/-! ### GP Lemma 5.1: the intercept along a finitely supported move

`anchorIntercept b a v = (3/2) b² log 2 + ‖a‖² + ‖v‖²/2` with `‖u‖² = ∑ u_k² / k`.  Polarisation of
the weighted inner product `⟨u, w⟩ = ∑ u_k w_k / k` along the move `a + da⁰ + τ da¹`,
`v + dv⁰ + τ dv¹` with `da^i`, `dv^i` of finite support. -/

/-- The weighted inner product of two moment sequences. -/
def barrierInner (u w : ℕ → ℝ) : ℝ := ∑' k : ℕ, u (k + 1) * w (k + 1) / ((k + 1 : ℕ) : ℝ)

theorem barrierTrialNormSq_eq_inner (u : ℕ → ℝ) : barrierTrialNormSq u = barrierInner u u := by
  unfold barrierTrialNormSq barrierInner
  congr 1
  ext k
  ring

theorem summable_inner_of_support (u : ℕ → ℝ) {w : ℕ → ℝ} {K : ℕ} (hw : ∀ k, K ≤ k → w k = 0) :
    Summable (fun k : ℕ => u (k + 1) * w (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
  have : K ≤ k + 1 := by
    have := Finset.mem_range.not.mp hk
    omega
  simp [hw (k + 1) this]

theorem barrierInner_add_right (u : ℕ → ℝ) {w z : ℕ → ℝ} {K : ℕ} (hw : ∀ k, K ≤ k → w k = 0)
    (hz : ∀ k, K ≤ k → z k = 0) :
    barrierInner u (fun k => w k + z k) = barrierInner u w + barrierInner u z := by
  unfold barrierInner
  rw [← (summable_inner_of_support u hw).tsum_add (summable_inner_of_support u hz)]
  congr 1
  ext k
  ring

theorem barrierInner_smul_right (u : ℕ → ℝ) {w : ℕ → ℝ} (τ : ℝ) :
    barrierInner u (fun k => τ * w k) = τ * barrierInner u w := by
  unfold barrierInner
  rw [← tsum_mul_left]
  congr 1
  ext k
  ring

theorem barrierInner_comm (u w : ℕ → ℝ) : barrierInner u w = barrierInner w u := by
  unfold barrierInner
  congr 1
  ext k
  ring

theorem barrierTrialNormSq_add {u w : ℕ → ℝ} {K : ℕ}
    (hu : Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hw : ∀ k, K ≤ k → w k = 0) :
    barrierTrialNormSq (fun k => u k + w k) =
      barrierTrialNormSq u + 2 * barrierInner u w + barrierTrialNormSq w := by
  have h1 := summable_inner_of_support u hw
  have h2 : Summable (fun k : ℕ => w (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
    have := summable_inner_of_support w hw
    simpa [sq] using this
  unfold barrierTrialNormSq barrierInner
  have e : ∀ k : ℕ, (u (k + 1) + w (k + 1)) ^ 2 / ((k + 1 : ℕ) : ℝ) =
      u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) + 2 * (u (k + 1) * w (k + 1) / ((k + 1 : ℕ) : ℝ)) +
        w (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ) := fun k => by ring
  simp only [e]
  rw [(hu.add (h1.mul_left 2)).tsum_add h2, hu.tsum_add (h1.mul_left 2), tsum_mul_left]

/-- **GP Lemma 5.1 (intercept polarisation).**  Along the move `w⁰ + τ w¹` of finite support,
`anchorIntercept b (a + da⁰ + τ da¹) (v + dv⁰ + τ dv¹) = I₀ + (L₀ + Q₀₀) + τ (L₁ + 2 Q₀₁) + τ² Q₁₁`
with `L_i = 2⟨a, da^i⟩ + ⟨v, dv^i⟩` and `Q_ij = ⟨da^i, da^j⟩ + ½⟨dv^i, dv^j⟩`. -/
theorem anchorIntercept_move (b : ℝ) {a v da0 da1 dv0 dv1 : ℕ → ℝ} {K : ℕ}
    (ha : Summable (fun k : ℕ => a (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hv : Summable (fun k : ℕ => v (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (ha0 : ∀ k, K ≤ k → da0 k = 0) (ha1 : ∀ k, K ≤ k → da1 k = 0)
    (hv0 : ∀ k, K ≤ k → dv0 k = 0) (hv1 : ∀ k, K ≤ k → dv1 k = 0) (τ : ℝ) :
    anchorIntercept b (fun k => a k + (da0 k + τ * da1 k)) (fun k => v k + (dv0 k + τ * dv1 k)) =
      anchorIntercept b a v +
        ((2 * barrierInner a da0 + barrierInner v dv0) +
          (barrierInner da0 da0 + barrierInner dv0 dv0 / 2)) +
        τ * ((2 * barrierInner a da1 + barrierInner v dv1) +
          2 * (barrierInner da0 da1 + barrierInner dv0 dv1 / 2)) +
        τ ^ 2 * (barrierInner da1 da1 + barrierInner dv1 dv1 / 2) := by
  have hwa : ∀ k, K ≤ k → da0 k + τ * da1 k = 0 := fun k hk => by simp [ha0 k hk, ha1 k hk]
  have hwv : ∀ k, K ≤ k → dv0 k + τ * dv1 k = 0 := fun k hk => by simp [hv0 k hk, hv1 k hk]
  have hs1 : ∀ k, K ≤ k → τ * da1 k = 0 := fun k hk => by simp [ha1 k hk]
  have hs2 : ∀ k, K ≤ k → τ * dv1 k = 0 := fun k hk => by simp [hv1 k hk]
  have lin : ∀ (u d0 d1 : ℕ → ℝ), (∀ k, K ≤ k → d0 k = 0) → (∀ k, K ≤ k → d1 k = 0) →
      barrierInner u (fun k => d0 k + τ * d1 k) = barrierInner u d0 + τ * barrierInner u d1 :=
    fun u d0 d1 h0 h1 => by
      rw [barrierInner_add_right u h0 (fun k hk => by simp [h1 k hk]),
        barrierInner_smul_right u τ]
  have quad : ∀ (d0 d1 : ℕ → ℝ), (∀ k, K ≤ k → d0 k = 0) → (∀ k, K ≤ k → d1 k = 0) →
      barrierTrialNormSq (fun k => d0 k + τ * d1 k) =
        barrierInner d0 d0 + 2 * τ * barrierInner d0 d1 + τ ^ 2 * barrierInner d1 d1 :=
    fun d0 d1 h0 h1 => by
      rw [barrierTrialNormSq_eq_inner, lin _ d0 d1 h0 h1,
        barrierInner_comm (fun k => d0 k + τ * d1 k) d0,
        barrierInner_comm (fun k => d0 k + τ * d1 k) d1,
        lin d0 d0 d1 h0 h1, lin d1 d0 d1 h0 h1, barrierInner_comm d1 d0]
      ring
  unfold anchorIntercept
  rw [barrierTrialNormSq_add ha hwa, barrierTrialNormSq_add hv hwv,
    quad da0 da1 ha0 ha1, quad dv0 dv1 hv0 hv1, lin a da0 da1 ha0 ha1, lin v dv0 dv1 hv0 hv1]
  ring

/-- For one fixed prefix and damping the free pin interaction has the anchor tangent, with the
mass square retained, the two endpoint logarithms kept, and the regularization error explicit. -/
theorem free_pin_prefix_tangent {ν e : ℝ} (hν : 0<ν) (he : e ∈ Ioo (0:ℝ) (1/8))
    {p : ℕ} (hp : (p:ℝ) ≤ ν) {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1:ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0:ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (b : ℝ) (a v : ℕ → ℝ) (J : ℕ) :
    pinOffDiagonalInteraction ν 1 x s ≤
      anchorIntercept b (momentPrefix J a) (momentPrefix J v)
      - (3/2:ℝ)*((p:ℝ)/ν-b)^2*Real.log 2
      + (∑ i, anchorRowField b (momentPrefix J a) (momentPrefix J v) (x i))/ν
      + (∑ j, anchorColumnField b (momentPrefix J v) (s j))/ν
      - (∑ i, Real.log (1-x i))/(2*ν^2) - (∑ j, Real.log (1-s j))/ν^2
      + 2*e*(∑' j, |momentPrefix J a j|) + 4*e*(∑' j, |momentPrefix J v j|)
      + freePopulationRegularizationError ν e := by
  have h := free_population_canonical hν he hp hx hs hxi hsi (momentPrefix J a) (momentPrefix J v)
    (momentPrefix_abs_summable J a) (momentPrefix_abs_summable J v)
  have hrow : (∑ i, anchorRowField b (momentPrefix J a) (momentPrefix J v) (x i))/ν =
      (∑ i, (-2*barrierTrialT (momentPrefix J a) (x i) -
        barrierTrialS (momentPrefix J v) (x i)))/ν + ((p:ℝ)/ν)*(-b*Real.log 2) := by
    unfold anchorRowField
    have : ∀ i, -b*Real.log 2 - 2*barrierTrialT (momentPrefix J a) (x i) -
        barrierTrialS (momentPrefix J v) (x i) = -b*Real.log 2 +
        (-2*barrierTrialT (momentPrefix J a) (x i) -
        barrierTrialS (momentPrefix J v) (x i)) := fun i => by ring
    simp only [this, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hcol : (∑ j, anchorColumnField b (momentPrefix J v) (s j))/ν =
      (∑ j, 2*barrierTrialT (momentPrefix J v) (s j))/ν + ((p:ℝ)/ν)*(-2*b*Real.log 2) := by
    unfold anchorColumnField
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hrow, hcol]
  unfold anchorIntercept
  nlinarith only [h]

/-- O(1/k) moments give the two summability inputs of the tangent. -/
theorem summable_of_moment_bound {u : ℕ → ℝ} {C : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k) :
    Summable (fun n => |u (n+1)| / ((n+1:ℕ):ℝ)) ∧
      Summable (fun n => u (n+1)^2 / ((n+1:ℕ):ℝ)) := by
  have hbase : Summable (fun n : ℕ => 1 / (((n+1:ℕ):ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using h
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hu 1 one_ne_zero)
    simpa using h
  constructor
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hbase.mul_left C)
    have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have h := hu (n+1) (Nat.succ_ne_zero n)
    calc |u (n+1)| / ((n+1:ℕ):ℝ) ≤ (C / ((n+1:ℕ):ℝ)) / ((n+1:ℕ):ℝ) :=
          div_le_div_of_nonneg_right h hd.le
      _ = C * (1 / (((n+1:ℕ):ℝ))^2) := by field_simp
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hbase.mul_left (C^2))
    have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    have hd1 : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have h := hu (n+1) (Nat.succ_ne_zero n)
    have hsq : u (n+1)^2 ≤ (C / ((n+1:ℕ):ℝ))^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc u (n+1)^2 / ((n+1:ℕ):ℝ) ≤ u (n+1)^2 := div_le_self (sq_nonneg _) hd1
      _ ≤ (C / ((n+1:ℕ):ℝ))^2 := hsq
      _ = C^2 * (1 / (((n+1:ℕ):ℝ))^2) := by field_simp

/-- **Uniform free tangent.** Given `ε`, one prefix `J`, then one damping `e`, then one threshold
`ν₀` work for every `ν ≥ ν₀`, every population size `p ≤ ν` and all configurations: the cutoffs
come before every configuration.  The mass square is retained. -/
theorem free_pin_anchor_tangent (b : ℝ) (a v : ℕ → ℝ)
    (ha : Summable (fun n => |a (n+1)| / ((n+1:ℕ):ℝ)))
    (hv : Summable (fun n => |v (n+1)| / ((n+1:ℕ):ℝ)))
    (ha2 : Summable (fun n => a (n+1)^2 / ((n+1:ℕ):ℝ)))
    (hv2 : Summable (fun n => v (n+1)^2 / ((n+1:ℕ):ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ (p : ℕ), (p:ℝ) ≤ ν →
      ∀ (x s : Fin p → ℝ), (∀ i, x i ∈ Ioo (-1:ℝ) 1) → (∀ j, s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      pinOffDiagonalInteraction ν 1 x s ≤
        anchorIntercept b a v - (3/2:ℝ)*((p:ℝ)/ν-b)^2*Real.log 2
        + (∑ i, anchorRowField b a v (x i))/ν + (∑ j, anchorColumnField b v (s j))/ν
        - (∑ i, Real.log (1-x i))/(2*ν^2) - (∑ j, Real.log (1-s j))/ν^2 + ε := by
  have hδ : 0 < ε/10 := by positivity
  obtain ⟨J, hJa, hJv, hJc⟩ :=
    ((T_prefix_uniform a ha hδ).and ((S_prefix_uniform v hv hδ).and
      (T_prefix_uniform v hv hδ))).exists
  set Sa := ∑' j, |momentPrefix J a j| with hSa
  set Sv := ∑' j, |momentPrefix J v j| with hSv
  have hSa0 : 0 ≤ Sa := tsum_nonneg fun _ => abs_nonneg _
  have hSv0 : 0 ≤ Sv := tsum_nonneg fun _ => abs_nonneg _
  obtain ⟨e, he, hec⟩ := Analytic.exists_small_damping
    (show (0:ℝ) ≤ 2*Sa+4*Sv+14 by positivity) (show 0 < ε/4 by positivity)
  set A : ℝ := (Real.log 2-2*Real.log (1-realEnergyTau e^2))/2+
    (Real.log 2-Real.log e)/2+(Real.log 2-2*Real.log e) with hA
  have hreg : ∀ ν : ℝ, 0 < ν → freePopulationRegularizationError ν e = A/ν+14*e := by
    intro ν hν
    unfold freePopulationRegularizationError
    rw [hA]
    field_simp
  refine ⟨(|A|+1)*4/ε, by positivity, fun ν hν p hp x s hx hs hxi hsi => ?_⟩
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hν
  have hAν : A/ν ≤ ε/4 := by
    rw [div_le_iff₀ hν0]
    have h1 : (|A|+1)*4 ≤ ν*ε := (div_le_iff₀ hε).mp hν
    nlinarith only [h1, le_abs_self A, abs_nonneg A]
  have hT := free_pin_prefix_tangent hν0 he hp hx hs hxi hsi b a v J
  have hx' : ∀ i, x i ∈ Icc (-1:ℝ) 1 := fun i => ⟨(hx i).1.le, (hx i).2.le⟩
  have hs' : ∀ j, s j ∈ Icc (-1:ℝ) 1 := fun j => ⟨by linarith [(hs j).1], (hs j).2.le⟩
  have hrow := pin_average_le_of_le_add hν0 hp
    (fun i => anchorRowField b (momentPrefix J a) (momentPrefix J v) (x i))
    (fun i => anchorRowField b a v (x i)) (c := 3*(ε/10)) (by positivity) (fun i => by
      have h1 := (abs_lt.mp (hJa (x i) (hx' i))).2
      have h2 := (abs_lt.mp (hJv (x i) (hx' i))).2
      have h1' := (abs_lt.mp (hJa (x i) (hx' i))).1
      have h2' := (abs_lt.mp (hJv (x i) (hx' i))).1
      unfold anchorRowField
      linarith only [h1, h2, h1', h2'])
  have hcol := pin_average_le_of_le_add hν0 hp
    (fun j => anchorColumnField b (momentPrefix J v) (s j))
    (fun j => anchorColumnField b v (s j)) (c := 2*(ε/10)) (by positivity) (fun j => by
      have h1 := (abs_lt.mp (hJc (s j) (hs' j))).1
      unfold anchorColumnField
      linarith only [h1])
  have hI : anchorIntercept b (momentPrefix J a) (momentPrefix J v) ≤ anchorIntercept b a v := by
    unfold anchorIntercept
    have h1 := barrierTrialNormSq_prefix_le J a ha2
    have h2 := barrierTrialNormSq_prefix_le J v hv2
    linarith only [h1, h2]
  rw [hreg ν hν0] at hT
  have hec' : 2*e*Sa+4*e*Sv+14*e < ε/4 := by nlinarith only [hec]
  linarith only [hT, hrow, hcol, hI, hAν, hec']

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas






namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Filter Set MeasureTheory OAI.InternalCatalan Topology
open scoped BigOperators
open CapFields CapFields.YCell

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

/-! ### Moment decay -/

theorem cell_phys_moment_bound {c : YCell} (hc : RowCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 →
      |c.phys fun u => (Tc k).eval u| ≤ C / k ∧ |c.phys fun u => u^k| ≤ C / k := by
  obtain ⟨K, hK0, hK⟩ := cell_primitive_bound hc
  have hs := cell_scale_nonneg c
  refine ⟨c.w / (c.hi - c.lo) * (2 * K), by positivity, fun k hk => ?_⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have key : ∀ F G : ℝ → ℝ, Continuous F → (∀ t, HasDerivAt G (F t) t) →
      (∀ t ∈ Icc (-1:ℝ) 1, |G t| ≤ 2 / (k:ℝ)) →
      |c.phys F| ≤ c.w / (c.hi - c.lo) * (2 * K) / k := by
    intro F G hF hG hB
    unfold YCell.phys YCell.avg
    rw [abs_mul, abs_of_nonneg hs]
    have := hK F G (2 / k) hF hG hB
    calc c.w / (c.hi - c.lo) * |∫ Y in c.lo..c.hi, F (physX Y)|
        ≤ c.w / (c.hi - c.lo) * (2 / k * K) := by gcongr
      _ = _ := by ring
  obtain ⟨G1, g1, b1⟩ := cheb_primitive k hk
  obtain ⟨G2, g2, b2⟩ := pow_primitive k hk
  exact ⟨key _ G1 (chebT_measurable k) g1 b1, key _ G2 (by fun_prop) g2 b2⟩

theorem cell_col_moment_bound {c : YCell} (hc : ColCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 → |c.avg fun u => (Tc k).eval u| ≤ C / k := by
  have hs := cell_scale_nonneg c
  refine ⟨c.w / (c.hi - c.lo) * 4, by positivity, fun k hk => ?_⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨G, g, b⟩ := cheb_primitive k hk
  unfold YCell.avg
  rw [abs_mul, abs_of_nonneg hs, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => g t) ((chebT_measurable k).intervalIntegrable _ _)]
  have hlo : c.lo ∈ Icc (-1:ℝ) 1 := ⟨hc.1, c.lo_lt.le.trans hc.2⟩
  have hhi : c.hi ∈ Icc (-1:ℝ) 1 := ⟨hc.1.trans c.lo_lt.le, hc.2⟩
  have h1 := b _ hlo
  have h2 := b _ hhi
  have h3 : |G c.hi - G c.lo| ≤ 4 / k := by
    refine (abs_sub _ _).trans ?_
    have : (4:ℝ) / k = 2 / k + 2 / k := by ring
    linarith
  calc c.w / (c.hi - c.lo) * |G c.hi - G c.lo| ≤ c.w / (c.hi - c.lo) * (4 / k) := by gcongr
    _ = _ := by ring

/-- Chebyshev moments of a list of row cells. -/
def rowT (L : List YCell) (k : ℕ) : ℝ := physL L fun u => (Tc k).eval u
/-- Power moments of a list of row cells. -/
def rowB (L : List YCell) (k : ℕ) : ℝ := physL L fun u => u^k
/-- Chebyshev moments of a list of column cells. -/
def colT (L : List YCell) (k : ℕ) : ℝ := (L.map fun c => c.avg fun u => (Tc k).eval u).sum
/-- The anchor difference `V = B - 2C`. -/
def anchorV (R C : List YCell) (k : ℕ) : ℝ := rowB R k - 2 * colT C k

theorem physL_cons (c : YCell) (L : List YCell) (f : ℝ → ℝ) :
    physL (c :: L) f = c.phys f + physL L f := by simp [physL]
theorem potL_cons (c : YCell) (L : List YCell) (y : ℝ) :
    potL (c :: L) y = c.pot y + potL L y := by simp [potL]
theorem massL_cons (c : YCell) (L : List YCell) : massL (c :: L) = c.w + massL L := by
  simp [massL]
theorem colT_cons (c : YCell) (L : List YCell) (k : ℕ) :
    colT (c :: L) k = (c.avg fun u => (Tc k).eval u) + colT L k := by simp [colT]

theorem row_moment_bound {L : List YCell} (hL : ∀ c ∈ L, RowCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 → |rowT L k| ≤ C / k ∧ |rowB L k| ≤ C / k := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun k _ => by simp [rowT, rowB, physL]⟩
  | cons c L ih =>
    obtain ⟨C1, h1, b1⟩ := cell_phys_moment_bound (hL c (by simp))
    obtain ⟨C2, h2, b2⟩ := ih fun d hd => hL d (by simp [hd])
    refine ⟨C1 + C2, by positivity, fun k hk => ?_⟩
    obtain ⟨p1, p2⟩ := b1 k hk
    obtain ⟨q1, q2⟩ := b2 k hk
    simp only [rowT, rowB, physL_cons] at *
    rw [add_div]
    exact ⟨(abs_add_le _ _).trans (add_le_add p1 q1), (abs_add_le _ _).trans (add_le_add p2 q2)⟩

theorem col_moment_bound {L : List YCell} (hL : ∀ c ∈ L, ColCell c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≠ 0 → |colT L k| ≤ C / k := by
  induction L with
  | nil => exact ⟨0, le_rfl, fun k _ => by simp [colT]⟩
  | cons c L ih =>
    obtain ⟨C1, h1, b1⟩ := cell_col_moment_bound (hL c (by simp))
    obtain ⟨C2, h2, b2⟩ := ih fun d hd => hL d (by simp [hd])
    refine ⟨C1 + C2, by positivity, fun k hk => ?_⟩
    rw [colT_cons, add_div]
    exact (abs_add_le _ _).trans (add_le_add (b1 k hk) (b2 k hk))

/-- **Anchor weighted summability**: both anchor moment vectors are `O(1/k)`. -/
theorem anchor_moment_bound {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, k ≠ 0 → |rowT R k| ≤ K / k ∧ |anchorV R C k| ≤ K / k := by
  obtain ⟨C1, h1, b1⟩ := row_moment_bound hR
  obtain ⟨C2, h2, b2⟩ := col_moment_bound hC
  refine ⟨C1 + 2 * C2, by positivity, fun k hk => ?_⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  obtain ⟨p1, p2⟩ := b1 k hk
  have p3 := b2 k hk
  constructor
  · refine p1.trans ?_
    gcongr
    linarith
  · unfold anchorV
    have h3 : |2 * colT C k| ≤ 2 * (C2 / k) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    have := abs_sub (rowB R k) (2 * colT C k)
    have e : (C1 + 2 * C2) / k = C1 / k + 2 * (C2 / k) := by ring
    rw [e]
    linarith

/-! ### Series terms -/

/-- The term of `barrierTrialT`. -/
def termT (u : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  u (n + 1) * (Tc (n+1)).eval x / ((n + 1 : ℕ) : ℝ)
/-- The term of `barrierTrialS`. -/
def termS (u : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ := u (n + 1) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ)

theorem termT_summable {u : ℕ → ℝ} {C : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k) {x : ℝ}
    (hx : x ∈ Icc (-1:ℝ) 1) : Summable (termT u x) := by
  refine Summable.of_norm_bounded (summable_of_moment_bound hu).1 fun n => ?_
  have hT : |(Tc (n+1)).eval x| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)
  unfold termT
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
  gcongr
  calc |u (n+1)| * |(Tc (n+1)).eval x| ≤ |u (n+1)| * 1 := by gcongr
    _ = _ := mul_one _

theorem termS_summable {u : ℕ → ℝ} {C : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ C / k) {x : ℝ}
    (hx : x ∈ Icc (-1:ℝ) 1) : Summable (termS u x) := by
  refine Summable.of_norm_bounded (summable_of_moment_bound hu).1 fun n => ?_
  have hT : |x^(n+1)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
  unfold termS
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
  gcongr
  calc |u (n+1)| * |x^(n+1)| ≤ |u (n+1)| * 1 := by gcongr
    _ = _ := mul_one _

theorem barrierTrialT_eq (u : ℕ → ℝ) (x : ℝ) : barrierTrialT u x = ∑' n, termT u x n := rfl
theorem barrierTrialS_eq (u : ℕ → ℝ) (x : ℝ) : barrierTrialS u x = ∑' n, termS u x n := rfl

/-! ### Row identity -/

theorem cell_row_series {c : YCell} (hc : RowCell c) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (hx0 : x ≠ 0) :
    HasSum (fun n => 2 * termT (fun k => c.phys fun u => (Tc k).eval u) x n +
        termS (fun k => c.phys fun u => u^k) x n)
      (-(c.phys (fun u => Real.log |u|) + c.pot (x + 1 / x)) - c.w * Real.log 2 -
        c.w * Real.log |x|) := by
  obtain ⟨C, -, hC⟩ := cell_phys_moment_bound hc
  obtain ⟨hint, hrec⟩ := cell_row_recombine hc hx hx0
  have hxI : x ∈ Icc (-1:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hsum := (summable_of_moment_bound (u := fun k => c.phys fun u => (Tc k).eval u)
    fun k hk => (hC k hk).1).1
  have hpot := cosine_potential_identity (cellM c) physX physX_measurable
    (by
      filter_upwards [cell_ae_mem c] with Y hY
      exact abs_le.mp (physX_mem hc hY).2.1)
    hxI
    (by
      filter_upwards [cell_ae_mem c, cell_ae_ne c (x + 1 / x)] with Y hY hne h
      apply hne
      rw [h]
      exact (physX_mem hc hY).2.2.symm)
    hint (fun k => c.phys fun u => (Tc k).eval u) (fun k => by
      unfold YCell.phys
      rw [cell_avg_eq]) hsum
  rw [cellM_real_univ] at hpot
  have hT := (termT_summable (u := fun k => c.phys fun u => (Tc k).eval u)
    (fun k hk => (hC k hk).1) hxI).hasSum
  have hR := cell_reflection hc hx
  have h := (hT.mul_left 2).add hR
  rw [← barrierTrialT_eq] at h
  convert h using 1
  · funext n
    rfl
  · rw [hrec, hpot]
    ring

theorem list_row_series {L : List YCell} (hL : ∀ c ∈ L, RowCell c) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x ≠ 0) :
    HasSum (fun n => 2 * termT (rowT L) x n + termS (rowB L) x n)
      (-(physL L (fun u => Real.log |u|) + potL L (x + 1 / x)) - massL L * Real.log 2 -
        massL L * Real.log |x|) := by
  induction L with
  | nil => simpa [termT, termS, rowT, rowB, physL, potL, massL] using hasSum_zero
  | cons c L ih =>
    have h1 := cell_row_series (hL c (by simp)) hx hx0
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termT, termS, rowT, rowB, physL_cons]
      ring
    · rw [physL_cons, potL_cons, massL_cons]
      ring

theorem list_cross_series {L : List YCell} (hL : ∀ c ∈ L, ColCell c) {x : ℝ}
    (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x ≠ 0) :
    HasSum (fun n => 2 * termS (colT L) x n)
      (-(potL (L.map dil2) (x + 1 / x)) - massL L * Real.log |x|) := by
  induction L with
  | nil => simpa [termS, colT, potL, massL] using hasSum_zero
  | cons c L ih =>
    have h1 := cell_cross (hL c (by simp)) hx hx0
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termS, colT_cons]
      ring
    · rw [List.map_cons, potL_cons, massL_cons]
      ring

/-- **Anchor row identity (R).** -/
theorem anchor_row_identity {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) (hm : massL R = massL C) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1)
    (hx0 : x ≠ 0) :
    physL R (fun u => Real.log |u|) + potL R (x + 1 / x) - potL (C.map dil2) (x + 1 / x) =
      -massL R * Real.log 2 - 2 * barrierTrialT (rowT R) x -
        barrierTrialS (anchorV R C) x := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound hR hC
  have hxI : x ∈ Icc (-1:ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hT := (termT_summable (u := rowT R) (fun k hk => (hK k hk).1) hxI).hasSum
  have hS := (termS_summable (u := anchorV R C) (fun k hk => (hK k hk).2) hxI).hasSum
  rw [← barrierTrialT_eq] at hT
  rw [← barrierTrialS_eq] at hS
  have h1 := list_row_series hR hx hx0
  have h2 := list_cross_series hC hx hx0
  have h3 := (hT.mul_left 2).add hS
  have e : (fun n => 2 * termT (rowT R) x n + termS (anchorV R C) x n) =
      fun n => (2 * termT (rowT R) x n + termS (rowB R) x n) - 2 * termS (colT C) x n := by
    funext n
    simp only [termS, anchorV]
    ring
  rw [e] at h3
  have := h3.unique (h1.sub h2)
  rw [hm] at this ⊢
  linarith only [this]

/-! ### Column identity -/

theorem cell_col_self {c : YCell} (hc : ColCell c) {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (termT (fun k => c.avg fun u => (Tc k).eval u) s)
      ((-c.pot s - c.w * Real.log 2) / 2) := by
  obtain ⟨C, -, hC⟩ := cell_col_moment_bound hc
  have hsum := (summable_of_moment_bound (u := fun k => c.avg fun u => (Tc k).eval u) hC).1
  have hpot := cosine_potential_identity (cellM c) id measurable_id
    (by
      filter_upwards [cell_ae_mem c] with u hu
      exact ⟨hc.1.trans hu.1, hu.2.trans hc.2⟩)
    hs
    (by
      filter_upwards [cell_ae_ne c s] with u hu
      exact hu.symm)
    (cell_integrable_log c s) (fun k => c.avg fun u => (Tc k).eval u)
    (fun k => cell_avg_eq _ _) hsum
  rw [cellM_real_univ] at hpot
  have hT := (termT_summable hC hs).hasSum
  rw [← barrierTrialT_eq] at hT
  convert hT using 1
  have e : c.pot s = ∫ y, Real.log |s - id y| ∂cellM c := cell_avg_eq _ _
  rw [e, hpot]
  ring

theorem cell_abs_pow_le {c : YCell} (hc : RowCell c) (k : ℕ) :
    ∫ Y, |physX Y|^k ∂cellM c ≤ |c.phys fun u => u^k| := by
  have hB : (c.phys fun u => u^k) = ∫ Y, physX Y^k ∂cellM c := cell_avg_eq _ _
  rw [hB]
  rcases hc with h | h
  · have hae : ∀ᵐ Y ∂cellM c, |physX Y|^k = physX Y^k := by
      filter_upwards [cell_ae_mem c] with Y hY
      rw [abs_of_pos (physX_spec_pos (h.trans hY.1)).1]
    rw [integral_congr_ae hae]
    exact le_abs_self _
  · have hae : ∀ᵐ Y ∂cellM c, |physX Y|^k = (-1)^k * physX Y^k := by
      filter_upwards [cell_ae_mem c] with Y hY
      rw [abs_of_neg (physX_spec_neg (hY.2.trans h)).1, neg_pow]
    rw [integral_congr_ae hae, integral_const_mul]
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem col_kernel {t s : ℝ} (ht : t ∈ Ioo (-1:ℝ) 1) (ht0 : t ≠ 0) (hs : s ∈ Icc (-1:ℝ) 1) :
    Real.log |t| + Real.log |2 * s - (t + 1 / t)| = Real.log (1 - 2 * t * s + t^2) := by
  have hp := cross_pos' ht hs
  have e : 2 * s - (t + 1 / t) = -((1 - 2 * t * s + t^2) / t) := by
    field_simp
    ring
  rw [e, abs_neg, abs_div, abs_of_pos hp, Real.log_div hp.ne' (abs_ne_zero.mpr ht0)]
  ring

theorem cell_row_cross {c : YCell} (hc : RowCell c) {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (fun n => 2 * termT (fun k => c.phys fun u => u^k) s n)
      (-(c.phys (fun u => Real.log |u|) + c.pot (2 * s))) := by
  obtain ⟨C, hC0, hC⟩ := cell_phys_moment_bound hc
  have hcont := physX_continuousOn_cell hc
  let F : ℕ → ℝ → ℝ := fun n Y => 2 * physX Y^(n+1) * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ)
  have hFi : ∀ n, Integrable (F n) (cellM c) := fun n => by
    apply cell_integrable_of_continuousOn
    exact ((continuousOn_const.mul (hcont.pow _)).mul continuousOn_const).div_const _
  have hTs : ∀ n : ℕ, |(Tc (n+1)).eval s| ≤ 1 := fun n =>
    Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hs)
  have hbound : ∀ n : ℕ, ∫ Y, ‖F n Y‖ ∂cellM c ≤ 2 * C * (1 / ((n+1:ℕ):ℝ)^2) := by
    intro n
    have hk : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
    have hle : ∀ Y, ‖F n Y‖ ≤ (2 / ((n+1:ℕ):ℝ)) * |physX Y|^(n+1) := fun Y => by
      simp only [F]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc 2 * |physX Y|^(n+1) * |(Tc (n+1)).eval s| / ((n+1:ℕ):ℝ)
          ≤ 2 * |physX Y|^(n+1) * 1 / ((n+1:ℕ):ℝ) := by
            gcongr
            exact hTs n
        _ = _ := by ring
    have hi2 : Integrable (fun Y => |physX Y|^(n+1)) (cellM c) :=
      cell_integrable_of_continuousOn c (hcont.abs.pow _)
    calc ∫ Y, ‖F n Y‖ ∂cellM c ≤ ∫ Y, (2 / ((n+1:ℕ):ℝ)) * |physX Y|^(n+1) ∂cellM c :=
          integral_mono (hFi n).norm (hi2.const_mul _) hle
      _ = (2 / ((n+1:ℕ):ℝ)) * ∫ Y, |physX Y|^(n+1) ∂cellM c := integral_const_mul _ _
      _ ≤ (2 / ((n+1:ℕ):ℝ)) * (C / ((n+1:ℕ):ℝ)) := by
          gcongr
          exact (cell_abs_pow_le hc (n+1)).trans (hC (n+1) (Nat.succ_ne_zero n)).2
      _ = _ := by
          field_simp
  have hbase0 : Summable (fun n : ℕ => 1 / (((n+1:ℕ):ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using h
  have hbase : Summable (fun n : ℕ => 2 * C * (1 / (((n+1:ℕ):ℝ))^2)) := hbase0.mul_left _
  have hsum : Summable fun n => ∫ Y, ‖F n Y‖ ∂cellM c :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound hbase
  have h := hasSum_integral_of_summable_integral_norm hFi hsum
  have hlim : ∀ᵐ Y ∂cellM c, ∑' n, F n Y = -(Real.log |physX Y| + Real.log |2 * s - Y|) := by
    filter_upwards [cell_ae_mem c, cell_ae_ne c 2, cell_ae_ne c (-2)] with Y hY h2 hm2
    obtain ⟨t0, t1, t2⟩ := physX_mem hc hY
    have ht : physX Y ∈ Ioo (-1:ℝ) 1 := by
      obtain ⟨p, q⟩ := abs_le.mp t1
      refine ⟨lt_of_le_of_ne p fun e => hm2 ?_, lt_of_le_of_ne q fun e => h2 ?_⟩
      · rw [← t2, ← e]
        norm_num
      · rw [← t2, e]
        norm_num
    have h3 := energy_hasSum_cross_kernel ht hs
    have h4 := (hasSum_nat_add_iff' 1).mpr h3
    have h5 := col_kernel ht t0 hs
    rw [t2] at h5
    rw [h5]
    simpa [F] using h4.tsum_eq
  have ev : ∫ Y, (∑' n, F n Y) ∂cellM c =
      -(c.phys (fun u => Real.log |u|) + c.pot (2 * s)) := by
    have i2 : Integrable (fun Y => Real.log |physX Y|) (cellM c) := by
      apply cell_integrable_of_continuousOn
      apply ContinuousOn.log hcont.abs
      intro Y hY
      exact abs_ne_zero.mpr (physX_mem hc hY).1
    rw [integral_congr_ae hlim, integral_neg, integral_add i2 (cell_integrable_log c (2 * s))]
    unfold YCell.phys YCell.pot
    rw [cell_avg_eq, cell_avg_eq]
  rw [ev] at h
  convert h using 2 with n
  have hB : (c.phys fun u => u^(n+1)) = ∫ Y, physX Y^(n+1) ∂cellM c := cell_avg_eq _ _
  have e : (fun Y => F n Y) = fun Y => (2 * (Tc (n+1)).eval s / ((n+1:ℕ):ℝ)) * physX Y^(n+1) := by
    funext Y
    simp only [F]
    ring
  rw [e, integral_const_mul, ← hB]
  simp only [termT]
  ring

theorem list_col_self {L : List YCell} (hL : ∀ c ∈ L, ColCell c) {s : ℝ}
    (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (termT (colT L) s) ((-potL L s - massL L * Real.log 2) / 2) := by
  induction L with
  | nil =>
    have h0 : HasSum (fun _ : ℕ => (0:ℝ)) 0 := hasSum_zero
    have e : termT (colT []) s = fun _ : ℕ => (0:ℝ) := by
      funext n
      simp [termT, colT]
    rw [e]
    simpa [potL, massL] using h0
  | cons c L ih =>
    have h1 := cell_col_self (hL c (by simp)) hs
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termT, colT_cons]
      ring
    · rw [potL_cons, massL_cons]
      ring

theorem list_row_cross {L : List YCell} (hL : ∀ c ∈ L, RowCell c) {s : ℝ}
    (hs : s ∈ Icc (-1:ℝ) 1) :
    HasSum (fun n => 2 * termT (rowB L) s n)
      (-(physL L (fun u => Real.log |u|) + potL L (2 * s))) := by
  induction L with
  | nil => simpa [termT, rowB, physL, potL] using hasSum_zero
  | cons c L ih =>
    have h1 := cell_row_cross (hL c (by simp)) hs
    have h2 := ih fun d hd => hL d (by simp [hd])
    convert h1.add h2 using 1
    · funext n
      simp only [termT, rowB, physL_cons]
      ring
    · rw [physL_cons, potL_cons]
      ring

/-- **Anchor column identity (C).** -/
theorem anchor_col_identity {R C : List YCell} (hR : ∀ c ∈ R, RowCell c)
    (hC : ∀ c ∈ C, ColCell c) {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) :
    -physL R (fun u => Real.log |u|) + 2 * potL C s - potL R (2 * s) =
      -2 * massL C * Real.log 2 + 2 * barrierTrialT (anchorV R C) s := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound hR hC
  have hT := (termT_summable (u := anchorV R C) (fun k hk => (hK k hk).2) hs).hasSum
  rw [← barrierTrialT_eq] at hT
  have h1 := list_row_cross hR hs
  have h2 := list_col_self hC hs
  have e : (fun n => 2 * termT (anchorV R C) s n) =
      fun n => 2 * termT (rowB R) s n - 4 * termT (colT C) s n := by
    funext n
    simp only [termT, anchorV]
    ring
  have h3 := hT.mul_left 2
  rw [e] at h3
  have := h3.unique (h1.sub (h2.mul_left 4))
  linarith only [this]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

local notation "π" => Real.pi

variable {S : CapSource}

/-! ### The two reference measures -/

/-- Positive completed-gas reference, in the physical plane. -/
def qP (S : CapSource) : Measure ℂ :=
  ((S.gas Sign.pos).map cellP).sum + ((S.aux Sign.pos).map (auxP S)).sum

/-- Negative completed-gas reference, in the Joukowski plane. -/
def qM (S : CapSource) : Measure ℂ :=
  ((S.gas Sign.neg).map cellJ).sum + ((S.aux Sign.neg).map (auxJ S)).sum

theorem qP_good_parts (hS : S.Admissible) :
    GoodRef ((S.gas Sign.pos).map cellP).sum ∧ GoodRef ((S.aux Sign.pos).map (auxP S)).sum :=
  ⟨goodRef_list _ _ fun _ hc => cellP_good (Or.inl (hS.gas_pos _ hc)),
    goodRef_list _ _ fun e _ => auxP_good hS.eps_pos e⟩

theorem qM_good_parts (hS : S.Admissible) :
    GoodRef ((S.gas Sign.neg).map cellJ).sum ∧ GoodRef ((S.aux Sign.neg).map (auxJ S)).sum :=
  ⟨goodRef_list _ _ fun c _ => cellJ_good c, goodRef_list _ _ fun e _ => auxJ_good hS.eps_pos e⟩

theorem qP_good (hS : S.Admissible) : GoodRef (qP S) :=
  (qP_good_parts hS).1.add (qP_good_parts hS).2

theorem qM_good (hS : S.Admissible) : GoodRef (qM S) :=
  (qM_good_parts hS).1.add (qM_good_parts hS).2

theorem qP_mass (hS : S.Admissible) : (qP S).real Set.univ = 1 := by
  obtain ⟨f1, -, -⟩ := (qP_good_parts hS).1
  obtain ⟨f2, -, -⟩ := (qP_good_parts hS).2
  unfold qP
  rw [measureReal_add_apply,
    (real_univ_list _ cellP fun c hc => (cellP_good (Or.inl (hS.gas_pos c hc))).1).2,
    (real_univ_list _ (auxP S) fun e _ => (auxP_good hS.eps_pos e).1).2]
  simp only [cellP_mass, auxP_mass hS.eps_pos]
  have := hS.aux_pos_mass
  unfold CapSource.auxMass at this
  unfold massL at this
  linarith

theorem qM_mass (hS : S.Admissible) : (qM S).real Set.univ = 53 / 58 := by
  obtain ⟨f1, -, -⟩ := (qM_good_parts hS).1
  obtain ⟨f2, -, -⟩ := (qM_good_parts hS).2
  unfold qM
  rw [measureReal_add_apply,
    (real_univ_list _ cellJ fun c _ => (cellJ_good c).1).2,
    (real_univ_list _ (auxJ S) fun e _ => (auxJ_good hS.eps_pos e).1).2]
  simp only [cellJ_mass, auxJ_mass hS.eps_pos]
  have := hS.aux_neg_mass
  unfold CapSource.auxMass at this
  unfold massL at this
  linarith

theorem qP_pot (hS : S.Admissible) (z : ℂ) :
    planarPot (qP S) z = ((S.gas Sign.pos).map fun c => planarPot (cellP c) z).sum +
      ((S.aux Sign.pos).map fun e => planarPot (auxP S e) z).sum := by
  unfold qP
  rw [planarPot_add (qP_good_parts hS).1 (qP_good_parts hS).2,
    planarPot_list _ _ (fun _ hc => cellP_good (Or.inl (hS.gas_pos _ hc))),
    planarPot_list _ _ (fun e _ => auxP_good hS.eps_pos e)]

theorem qM_pot (hS : S.Admissible) (z : ℂ) :
    planarPot (qM S) z = ((S.gas Sign.neg).map fun c => planarPot (cellJ c) z).sum +
      ((S.aux Sign.neg).map fun e => planarPot (auxJ S e) z).sum := by
  unfold qM
  rw [planarPot_add (qM_good_parts hS).1 (qM_good_parts hS).2,
    planarPot_list _ _ (fun c _ => cellJ_good c),
    planarPot_list _ _ (fun e _ => auxJ_good hS.eps_pos e)]

/-! ### Radii -/

theorem rad_le_one (hS : S.Admissible) (i : ℕ) : S.rad i ≤ 1 := by
  unfold CapSource.rad
  rw [Real.exp_le_one_iff]
  linarith [hS.sigma_nonneg i]

theorem rad_anti (hS : S.Admissible) {i j : ℕ} (h : i ≤ j) : S.rad j ≤ S.rad i := by
  unfold CapSource.rad
  exact Real.exp_le_exp.mpr (neg_le_neg (hS.sigma_mono h))

theorem log_rad (i : ℕ) : Real.log (S.rad i) = -S.sigma i := Real.log_exp _

theorem log_max_rad (hS : S.Admissible) (i j : ℕ) :
    Real.log (max (S.rad i) (S.rad j)) = -S.sigma (min i j) := by
  rcases le_total i j with h | h
  · rw [max_eq_left (rad_anti hS h), min_eq_left h, log_rad]
  · rw [max_eq_right (rad_anti hS h), min_eq_right h, log_rad]

theorem ratio_rad (hS : S.Admissible) (i j : ℕ) :
    min (S.rad i) (S.rad j) / max (S.rad i) (S.rad j) = S.rad (max i j) / S.rad (min i j) := by
  rcases le_total i j with h | h
  · rw [max_eq_left (rad_anti hS h), min_eq_right (rad_anti hS h), max_eq_right h, min_eq_left h]
  · rw [max_eq_right (rad_anti hS h), min_eq_left (rad_anti hS h), max_eq_left h, min_eq_right h]

/-! ### Summability of the auxiliary series -/

theorem auxSer_summable (hε : 0 < S.eps) (ph : ℝ) {τ : ℝ} (hτ : |τ| ≤ 1) (θ : ℝ) :
    Summable fun k : ℕ => S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
  refine Summable.of_norm_bounded (cubeK_summable hε) fun k => ?_
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hc : |S.coef (k + 1)| ≤ |cubeK S (k + 1)| := by
    have : S.coef (k + 1) = -(cubeK S (k + 1) / ((k + 1 : ℕ) : ℝ)) := rfl
    rw [this, abs_neg, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
    exact div_le_self (abs_nonneg _) hk
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow]
  have h1 := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * ph)
  have h2 := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * θ)
  have h3 : |τ| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  calc _ ≤ |cubeK S (k + 1)| * 1 * 1 * 1 := by gcongr
    _ = _ := by ring

/-! ### Angular fields -/

theorem exact_sum (f : ℕ → ℝ) : Trunc.exact.sum f = ∑' k : ℕ, f (k + 1) := rfl

theorem ang_series_pos (ph a b θ : ℝ) :
    Trunc.exact.sum (fun k => S.coef k * (a ^ k + (if Sign.pos = Sign.neg then b ^ k else 0)) *
      Real.cos (k * ph) * Real.cos (k * θ)) = auxSer S ph a θ := by
  rw [exact_sum]
  unfold auxSer
  refine tsum_congr fun k => ?_
  simp

theorem ang_series_neg (hε : 0 < S.eps) (ph : ℝ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (θ : ℝ) :
    Trunc.exact.sum (fun k => S.coef k * (a ^ k + b ^ k) *
      Real.cos (k * ph) * Real.cos (k * θ)) = auxSer S ph a θ + auxSer S ph b θ := by
  rw [exact_sum]
  unfold auxSer
  rw [← (auxSer_summable hε ph ha θ).tsum_add (auxSer_summable hε ph hb θ)]
  refine tsum_congr fun k => ?_
  ring

theorem qP_angular (hS : S.Admissible) (i : ℕ) (θ : ℝ) :
    planarPot (qP S) (circ (S.rad i) θ) =
      S.angular Trunc.exact Sign.pos i θ - (53 * S.sigma i - S.radial i / 2) / 58 := by
  rw [qP_pot hS]
  unfold CapSource.angular
  simp only [cell_circ_pot]
  have h2 : ((S.aux Sign.pos).map fun e => planarPot (auxP S e) (circ (S.rad i) θ)) =
      (S.aux Sign.pos).map fun e => e.w * (-S.sigma (min i e.rad) +
        Trunc.exact.sum (fun k => S.coef k *
          ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
            (if Sign.pos = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)) *
          Real.cos (k * e.phase) * Real.cos (k * θ))) := by
    refine List.map_congr_left fun e _ => ?_
    rw [aux_direct hS.eps_pos e (rad_pos S i), log_max_rad hS, ratio_rad hS, ang_series_pos]
  rw [h2]
  simp [physL, CapSource.auxTail]

/-- The logarithmic moment of the negative reference. -/
def cM (S : CapSource) : ℝ :=
  physL (S.gas Sign.neg) (fun u => Real.log |u|) +
    ((S.aux Sign.neg).map fun e => e.w * Real.log (S.rad e.rad)).sum

theorem cells_fold_sum {l : List YCell} (hl : ∀ c ∈ l, RowCell c) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    (l.map fun c => planarPot (cellJ c) (joukowski (circ ρ θ))).sum =
      physL l (fun x => (1 / 2) * Real.log (ρ ^ 2 - 2 * ρ * x * Real.cos θ + x ^ 2)) +
      physL l (fun x => (1 / 2) * Real.log (1 - 2 * ρ * x * Real.cos θ + ρ ^ 2 * x ^ 2)) -
      massL l * (Real.log 2 + Real.log ρ) - physL l (fun u => Real.log |u|) := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, physL_cons, massL_cons]
    rw [cell_circ_fold (hl c (by simp)) hρ, ih fun d hd => hl d (by simp [hd])]
    ring

theorem aux_fold_sum (hS : S.Admissible) (l : List AuxEntry) (i : ℕ) (θ : ℝ) :
    (l.map fun e => planarPot (auxJ S e) (joukowski (circ (S.rad i) θ))).sum =
      (l.map fun e => e.w * (-S.sigma (min i e.rad) +
        Trunc.exact.sum (fun k => S.coef k *
          ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
            (S.rad i * S.rad e.rad) ^ k) *
          Real.cos (k * e.phase) * Real.cos (k * θ)))).sum -
      (l.map fun e => e.w).sum * (Real.log 2 + Real.log (S.rad i)) -
      (l.map fun e => e.w * Real.log (S.rad e.rad)).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hr1 := rad_le_one hS i
    have hr2 := rad_le_one hS e.rad
    have p1 := rad_pos S i
    have p2 := rad_pos S e.rad
    have hprod : S.rad i * S.rad e.rad ≤ 1 := by nlinarith
    have ha : |S.rad (max i e.rad) / S.rad (min i e.rad)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (rad_pos S _).le (rad_pos S _).le)]
      exact (div_le_one (rad_pos S _)).mpr (rad_anti hS (by omega))
    have hb : |S.rad i * S.rad e.rad| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact hprod
    have hser := ang_series_neg (S := S) hS.eps_pos e.phase ha hb θ
    rw [aux_fold hS.eps_pos e p1 hprod, ih, log_max_rad hS, ratio_rad hS, hser]
    ring

theorem qM_angular (hS : S.Admissible) (i : ℕ) (θ : ℝ) :
    planarPot (qM S) (joukowski (circ (S.rad i) θ)) =
      S.angular Trunc.exact Sign.neg i θ - (53 * S.sigma i - S.radial i / 2) / 58 -
        53 / 58 * (Real.log 2 + Real.log (S.rad i)) - cM S := by
  rw [qM_pot hS, cells_fold_sum (fun c hc => Or.inr (hS.gas_neg c hc)) (rad_pos S i),
    aux_fold_sum hS]
  have hm := hS.aux_neg_mass
  have e1 : ((S.aux Sign.neg).map fun e => e.w).sum = 53 / 58 - massL (S.gas Sign.neg) := hm
  rw [e1]
  unfold CapSource.angular cM
  simp only [if_true]
  simp only [CapSource.auxTail]
  ring

/-! ### Real points -/

/-- The angle of a nonzero real number. -/
def realAngle (x : ℝ) : ℝ := if x < 0 then π else 0

theorem circ_real {x : ℝ} : circ |x| (realAngle x) = (x : ℂ) := by
  unfold circ realAngle
  by_cases h : x < 0
  · rw [if_pos h, abs_of_neg h, Complex.exp_pi_mul_I]
    push_cast
    ring
  · rw [if_neg h, abs_of_nonneg (not_lt.mp h)]
    simp

theorem psi_pow {x r : ℝ} (hx : x ≠ 0) (hr : 0 < r) (n : ℕ) :
    (min |x| r / max |x| r) ^ n * Real.cos ((n : ℝ) * realAngle x) = CapSource.psi r x ^ n := by
  unfold CapSource.psi realAngle
  have hxa : 0 < |x| := abs_pos.mpr hx
  by_cases h : x < 0
  · rw [if_pos h, Real.cos_nat_mul_pi]
    have hax : x = -|x| := by rw [abs_of_neg h]; ring
    by_cases h2 : r < |x|
    · rw [if_pos h2, min_eq_right h2.le, max_eq_left h2.le]
      have : r / x = -(r / |x|) := by
        conv_lhs => rw [hax]
        rw [div_neg]
      rw [this, neg_pow]
      ring
    · have h3 := not_lt.mp h2
      rw [if_neg h2, min_eq_left h3, max_eq_right h3]
      have : x / r = -(|x| / r) := by
        conv_lhs => rw [hax]
        rw [neg_div]
      rw [this, neg_pow]
      ring
  · have h0 : 0 < x := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hx)
    rw [if_neg h, abs_of_pos h0]
    simp only [mul_zero, Real.cos_zero, mul_one]
    by_cases h2 : r < x
    · rw [if_pos h2, min_eq_right h2.le, max_eq_left h2.le]
    · have h3 := not_lt.mp h2
      rw [if_neg h2, min_eq_left h3, max_eq_right h3]

theorem mirror_pow {x : ℝ} (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (|x| * r) ^ n * Real.cos ((n : ℝ) * realAngle x) = (r * x) ^ n := by
  unfold realAngle
  by_cases h : x < 0
  · rw [if_pos h, Real.cos_nat_mul_pi, abs_of_neg h]
    rw [← mul_pow]
    congr 1
    ring
  · rw [if_neg h, abs_of_nonneg (not_lt.mp h)]
    simp only [mul_zero, Real.cos_zero, mul_one]
    rw [mul_comm]

theorem auxSer_row {x r : ℝ} (hx : x ≠ 0) (hr : 0 < r) (ph : ℝ) :
    auxSer S ph (min |x| r / max |x| r) (realAngle x) =
      Trunc.exact.sum (fun k => S.coef k * (CapSource.psi r x) ^ k * Real.cos (k * ph)) := by
  rw [exact_sum]
  unfold auxSer
  refine tsum_congr fun k => ?_
  rw [← psi_pow hx hr]
  ring

theorem auxSer_mirror {x r : ℝ} (hr : 0 < r) (ph : ℝ) :
    auxSer S ph (|x| * r) (realAngle x) =
      Trunc.exact.sum (fun k => S.coef k * (r * x) ^ k * Real.cos (k * ph)) := by
  rw [exact_sum]
  unfold auxSer
  refine tsum_congr fun k => ?_
  rw [← mirror_pow r hr]
  ring

theorem aux_row_pos (hS : S.Admissible) {x : ℝ} (hx : x ≠ 0) :
    ((S.aux Sign.pos).map fun e => planarPot (auxP S e) (x : ℂ)).sum =
      S.radialA Trunc.exact Sign.pos x := by
  unfold CapSource.radialA
  have h : ((S.aux Sign.pos).map fun e => planarPot (auxP S e) (x : ℂ)) =
      (S.aux Sign.pos).map fun e => e.w * (Real.log (max |x| (S.rad e.rad)) +
        Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k *
          Real.cos (k * e.phase)) +
        (if Sign.pos = Sign.neg then
          Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
         else 0)) := by
    refine List.map_congr_left fun e _ => ?_
    conv_lhs => rw [← circ_real (x := x)]
    rw [aux_direct hS.eps_pos e (abs_pos.mpr hx), auxSer_row hx (rad_pos S _)]
    simp
  rw [h]

theorem joukowski_real {x : ℝ} : joukowski (x : ℂ) = (((x + 1 / x) / 2 : ℝ) : ℂ) := by
  unfold joukowski
  push_cast
  rw [one_div]

theorem aux_row_neg (hS : S.Admissible) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1) (l : List AuxEntry) :
    (l.map fun e => planarPot (auxJ S e) (((x + 1 / x) / 2 : ℝ) : ℂ)).sum =
      (l.map fun e => e.w * (Real.log (max |x| (S.rad e.rad)) +
        Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k *
          Real.cos (k * e.phase)) +
        (if Sign.neg = Sign.neg then
          Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
         else 0))).sum -
      (l.map fun e => e.w).sum * (Real.log 2 + Real.log |x|) -
      (l.map fun e => e.w * Real.log (S.rad e.rad)).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hr1 := rad_le_one hS e.rad
    have p2 := rad_pos S e.rad
    have hxa := abs_pos.mpr hx
    have hprod : |x| * S.rad e.rad ≤ 1 := by nlinarith
    have h1 : planarPot (auxJ S e) (((x + 1 / x) / 2 : ℝ) : ℂ) =
        planarPot (auxJ S e) (joukowski (circ |x| (realAngle x))) := by
      rw [circ_real, joukowski_real]
    rw [h1, aux_fold hS.eps_pos e hxa hprod, ih, auxSer_row hx p2, auxSer_mirror p2]
    simp only [if_true]
    ring

/-- The negative row potential. -/
theorem qM_row (hS : S.Admissible) {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1) :
    planarPot (qM S) (((x + 1 / x) / 2 : ℝ) : ℂ) =
      potL (S.gas Sign.neg) (x + 1 / x) + physL (S.gas Sign.neg) (fun u => Real.log |u|) +
        massL (S.gas Sign.neg) * Real.log |x| + S.radialA Trunc.exact Sign.neg x -
        53 / 58 * (Real.log 2 + Real.log |x|) - cM S := by
  have hc : ((S.gas Sign.neg).map fun c => planarPot (cellJ c) (((x + 1 / x) / 2 : ℝ) : ℂ)).sum =
      potL (S.gas Sign.neg) (x + 1 / x) - massL (S.gas Sign.neg) * Real.log 2 := by
    generalize S.gas Sign.neg = l
    induction l with
    | nil => simp [potL, massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, potL_cons, massL_cons]
      rw [cell_fold_row, ih]
      ring
  have hm : ((S.aux Sign.neg).map fun e => e.w).sum = 53 / 58 - massL (S.gas Sign.neg) :=
    hS.aux_neg_mass
  rw [qM_pot hS, hc, aux_row_neg hS hx hx1, hm]
  unfold CapSource.radialA cM
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

variable {S : CapSource}

/-! ### The reflection tail -/

/-- The primitive in `reflTail` (cut `e + 1`). -/
def reflPrim (e : ℕ) (x : ℝ) : ℝ := x ^ (e + 1) / ((e : ℝ) + 1) + x ^ (e + 2) / ((e : ℝ) + 2)

theorem phys_pow_nonneg {c : YCell} (hc : 2 ≤ c.lo) (k : ℕ) : 0 ≤ c.phys fun u => u ^ k := by
  rw [cell_phys_eq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [cell_ae_mem c] with Y hY
  exact pow_nonneg (physX_spec_pos (hc.trans hY.1)).1.le k

theorem physX_anti {c : YCell} (hc : 2 ≤ c.lo) : physX c.hi ≤ physX c.lo := by
  obtain ⟨a0, a1, a2⟩ := physX_spec_pos hc
  obtain ⟨b0, b1, b2⟩ := physX_spec_pos (hc.trans c.lo_lt.le)
  by_contra h
  have hlt := not_le.mp h
  set a := physX c.lo
  set b := physX c.hi
  have e : (a + 1 / a) - (b + 1 / b) = (b - a) * (1 - a * b) / (a * b) := by
    field_simp
    ring
  have h1 : 0 ≤ (b - a) * (1 - a * b) / (a * b) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith)
    nlinarith
  have := c.lo_lt
  linarith

theorem geom_tail {t : ℝ} {e K : ℕ} (hK : e + 1 ≤ K) :
    (∑ n ∈ Finset.Ico (e + 1) K, t ^ (n + 1)) * (1 - t) = t ^ (e + 2) - t ^ (K + 1) := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Finset.sum_Ico_succ_top hK, add_mul, ih]
    ring

theorem tail_kernel {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) {e K : ℕ} (hK : e + 1 ≤ K) :
    -((∑ n ∈ Finset.Ico (e + 1) K, t ^ (n + 1)) * yDer t) ≤ t ^ e + t ^ (e + 1) := by
  have hg := geom_tail (t := t) hK
  have e' : -((∑ n ∈ Finset.Ico (e + 1) K, t ^ (n + 1)) * yDer t) =
      ((∑ n ∈ Finset.Ico (e + 1) K, t ^ (n + 1)) * (1 - t)) * (1 + t) / t ^ 2 := by
    unfold yDer
    field_simp
    ring
  rw [e', hg, div_le_iff₀ (by positivity)]
  have hp : 0 ≤ t ^ (K + 1) := by positivity
  have : (t ^ (e + 2) - t ^ (K + 1)) * (1 + t) ≤ t ^ (e + 2) * (1 + t) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith
  calc _ ≤ t ^ (e + 2) * (1 + t) := this
    _ = _ := by ring

theorem yDer_continuousOn {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) : ContinuousOn yDer (uIcc b a) := by
  unfold yDer
  rw [uIcc_of_le hab]
  refine continuousOn_const.sub (continuousOn_const.div (by fun_prop) fun t ht => ?_)
  have : 0 < t := hb.trans_le ht.1
  positivity

theorem tail_cell {c : YCell} (hc : 2 ≤ c.lo) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {e K : ℕ}
    (hK : e + 1 ≤ K) :
    ∑ n ∈ Finset.Ico (e + 1) K, (c.phys fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤
      c.w / (c.hi - c.lo) * (reflPrim e (physX c.lo) - reflPrim e (physX c.hi)) / ((e : ℝ) + 2) := by
  have hrc : RowCell c := Or.inl hc
  have hs := cell_scale_nonneg c
  set a := physX c.lo with ha
  set b := physX c.hi with hb
  obtain ⟨a0, a1, -⟩ := physX_spec_pos hc
  obtain ⟨b0, b1, -⟩ := physX_spec_pos (hc.trans c.lo_lt.le)
  have hab : b ≤ a := physX_anti hc
  set F : ℝ → ℝ := fun t => ∑ n ∈ Finset.Ico (e + 1) K, t ^ (n + 1) with hF
  have hFc : Continuous F := by
    simp only [hF]
    fun_prop
  have step1 : ∑ n ∈ Finset.Ico (e + 1) K, (c.phys fun u => u ^ (n + 1)) * x ^ (n + 1) /
      ((n + 1 : ℕ) : ℝ) ≤ (∑ n ∈ Finset.Ico (e + 1) K, (c.phys fun u => u ^ (n + 1))) / ((e : ℝ) + 2) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := (Finset.mem_Ico.mp hn).1
    have hm := phys_pow_nonneg hc (n + 1)
    have hx1 : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
    have hd : ((e : ℝ) + 2) ≤ ((n + 1 : ℕ) : ℝ) := by
      have : e + 2 ≤ n + 1 := by omega
      exact_mod_cast this
    calc _ ≤ (c.phys fun u => u ^ (n + 1)) * 1 / ((n + 1 : ℕ) : ℝ) := by gcongr
      _ ≤ (c.phys fun u => u ^ (n + 1)) * 1 / ((e : ℝ) + 2) := by gcongr
      _ = _ := by ring
  have step2 : ∑ n ∈ Finset.Ico (e + 1) K, (c.phys fun u => u ^ (n + 1)) = c.phys F := by
    simp only [cell_phys_eq, hF]
    rw [integral_finset_sum]
    intro n _
    exact cell_integrable_of_continuousOn c ((physX_continuousOn_cell hrc).pow _)
  have step3 : c.phys F = c.w / (c.hi - c.lo) * ∫ t in a..b, F t * yDer t := by
    unfold YCell.phys YCell.avg
    rw [cell_change_of_variable hrc hFc]
  have step4 : ∫ t in a..b, F t * yDer t ≤ reflPrim e a - reflPrim e b := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    have hyc := yDer_continuousOn b0 hab
    have i1 : IntervalIntegrable (fun t => -(F t * yDer t)) volume b a :=
      ((hFc.continuousOn.mul hyc).neg).intervalIntegrable
    have i2 : IntervalIntegrable (fun t : ℝ => t ^ e + t ^ (e + 1)) volume b a :=
      (by fun_prop : Continuous fun t : ℝ => t ^ e + t ^ (e + 1)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on hab i1 i2 fun t ht =>
      tail_kernel (b0.trans_le ht.1) (ht.2.trans a1) hK
    refine hm.trans_eq ?_
    have c1 : IntervalIntegrable (fun t : ℝ => t ^ e) volume b a :=
      (by fun_prop : Continuous fun t : ℝ => t ^ e).intervalIntegrable _ _
    have c2 : IntervalIntegrable (fun t : ℝ => t ^ (e + 1)) volume b a :=
      (by fun_prop : Continuous fun t : ℝ => t ^ (e + 1)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add c1 c2, integral_pow, integral_pow]
    unfold reflPrim
    push_cast
    ring
  rw [step2, step3] at step1
  exact step1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left step4 hs) (by positivity))

theorem tail_list {l : List YCell} (hl : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {e K : ℕ} (hK : e + 1 ≤ K) :
    ∑ n ∈ Finset.Ico (e + 1) K, physL l (fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ≤
      (l.map fun c => c.w / (c.hi - c.lo) *
        (reflPrim e (physX c.lo) - reflPrim e (physX c.hi)) / ((e : ℝ) + 2)).sum := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    simp only [physL_cons, List.map_cons, List.sum_cons, add_mul, add_div, Finset.sum_add_distrib]
    exact add_le_add (tail_cell (hl c (by simp)) hx hK) (ih fun d hd => hl d (by simp [hd]))

theorem refl_hasSum {l : List YCell} (hl : ∀ c ∈ l, RowCell c) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun n : ℕ => physL l (fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
      (-(l.map fun c => ∫ Y, Real.log |1 - x * physX Y| ∂cellM c).sum) := by
  induction l with
  | nil => simpa [physL] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons c l ih =>
    simp only [physL_cons, List.map_cons, List.sum_cons, add_mul, add_div, neg_add]
    exact (cell_reflection (hl c (by simp)) hx).add (ih fun d hd => hl d (by simp [hd]))

theorem physL_pow_nonneg {l : List YCell} (hl : ∀ c ∈ l, 2 ≤ c.lo) (k : ℕ) :
    0 ≤ physL l fun u => u ^ k := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    rw [physL_cons]
    exact add_nonneg (phys_pow_nonneg (hl c (by simp)) k) (ih fun d hd => hl d (by simp [hd]))

theorem reflPoly_eq (x : ℝ) :
    S.reflPoly x = ∑ n ∈ Finset.range (S.reflDeg + 1),
      physL (S.gas Sign.pos) (fun u => u ^ (n + 1)) * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  unfold CapSource.reflPoly CapSource.reflMoment
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  rfl

theorem Eref_eq : S.reflTail = ((S.gas Sign.pos).map fun c => c.w / (c.hi - c.lo) *
    (reflPrim S.reflDeg (physX c.lo) - reflPrim S.reflDeg (physX c.hi)) /
      ((S.reflDeg : ℝ) + 2)).sum := rfl

theorem reflection_le (hS : S.Admissible) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -((S.gas Sign.pos).map fun c => ∫ Y, Real.log |1 - x * physX Y| ∂cellM c).sum ≤
      S.reflPoly x + S.reflTail := by
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hs := refl_hasSum (l := S.gas Sign.pos) (fun c hc => Or.inl (hS.gas_pos c hc)) hx'
  refine le_of_tendsto hs.tendsto_sum_nat ?_
  filter_upwards [eventually_ge_atTop (S.reflDeg + 1)] with K hK
  rw [← Finset.sum_range_add_sum_Ico _ hK, ← reflPoly_eq, Eref_eq]
  exact add_le_add le_rfl (tail_list hS.gas_pos hx hK)

theorem reflection_ge (hS : S.Admissible) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ((S.gas Sign.pos).map fun c => ∫ Y, Real.log |1 - y * physX Y| ∂cellM c).sum ≤ -S.reflPoly y := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hs := refl_hasSum (l := S.gas Sign.pos) (fun c hc => Or.inl (hS.gas_pos c hc)) hy'
  have h := sum_le_hasSum (Finset.range (S.reflDeg + 1)) (fun n _ => div_nonneg
    (mul_nonneg (physL_pow_nonneg hS.gas_pos _) (pow_nonneg hy.1.le _)) (Nat.cast_nonneg _)) hs
  rw [← reflPoly_eq] at h
  linarith

/-- The positive row potential. -/
theorem qP_row (hS : S.Admissible) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    planarPot (qP S) (x : ℂ) ≤
      physL (S.gas Sign.pos) (fun u => Real.log |u|) + potL (S.gas Sign.pos) (x + 1 / x) +
        massL (S.gas Sign.pos) * Real.log |x| + S.reflPoly x + S.reflTail +
        S.radialA Trunc.exact Sign.pos x := by
  have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hx0 : x ≠ 0 := hx.1.ne'
  have hc : ∀ l : List YCell, (∀ c ∈ l, RowCell c) →
      (l.map fun c => planarPot (cellP c) (x : ℂ)).sum =
        physL l (fun u => Real.log |u|) + potL l (x + 1 / x) + massL l * Real.log |x| -
          (l.map fun c => ∫ Y, Real.log |1 - x * physX Y| ∂cellM c).sum := by
    intro l hl
    induction l with
    | nil => simp [physL, potL, massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, physL_cons, potL_cons, massL_cons]
      rw [cell_row_pot (hl c (by simp)) hx' hx0, ih fun d hd => hl d (by simp [hd])]
      ring
  rw [qP_pot hS, hc _ fun c h => Or.inl (hS.gas_pos c h), aux_row_pos hS hx0]
  have := reflection_le hS hx
  linarith

theorem circ_zero (r : ℝ) : circ r 0 = (r : ℂ) := by
  unfold circ
  simp

/-- The potential at the reciprocal of a selected row. -/
theorem qP_near (hS : S.Admissible) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    planarPot (qP S) ((1 / y : ℝ) : ℂ) ≤ -Real.log y - S.reflPoly y +
      ((S.aux Sign.pos).map fun e => e.w * Trunc.exact.sum (fun k => S.coef k *
        (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))).sum := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hy0 := hy.1
  have hc : ∀ l : List YCell, (∀ c ∈ l, RowCell c) →
      (l.map fun c => planarPot (cellP c) ((1 / y : ℝ) : ℂ)).sum =
        -(massL l * Real.log y) + (l.map fun c => ∫ Y, Real.log |1 - y * physX Y| ∂cellM c).sum := by
    intro l hl
    induction l with
    | nil => simp [massL]
    | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, massL_cons]
      rw [cell_near_pot (hl c (by simp)) hy, ih fun d hd => hl d (by simp [hd])]
      ring
  have ha : ∀ l : List AuxEntry,
      (l.map fun e => planarPot (auxP S e) ((1 / y : ℝ) : ℂ)).sum =
        -((l.map fun e => e.w).sum * Real.log y) +
        (l.map fun e => e.w * Trunc.exact.sum (fun k => S.coef k *
          (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hr := rad_pos S e.rad
      have hr1 := rad_le_one hS e.rad
      have hgt : S.rad e.rad ≤ 1 / y := by
        have : 1 ≤ 1 / y := (one_le_div hy0).mpr hy.2.le
        linarith
      have hp : 0 < 1 / y := by positivity
      have hser : auxSer S e.phase (S.rad e.rad * y) 0 = Trunc.exact.sum (fun k => S.coef k *
          (S.rad e.rad * y) ^ k * Real.cos (k * e.phase)) := by
        rw [exact_sum]
        unfold auxSer
        refine tsum_congr fun k => ?_
        simp
      have hτ : min (1 / y) (S.rad e.rad) / max (1 / y) (S.rad e.rad) = S.rad e.rad * y := by
        rw [min_eq_right hgt, max_eq_left hgt]
        field_simp
      have hpot := aux_direct hS.eps_pos e hp 0
      rw [circ_zero, hτ, hser, max_eq_left hgt, one_div, Real.log_inv, ← one_div] at hpot
      rw [hpot, ih]
      ring
  rw [qP_pot hS, hc _ fun c h => Or.inl (hS.gas_pos c h), ha]
  have h1 := reflection_ge hS hy
  have hm : ((S.aux Sign.pos).map fun e => e.w).sum = 1 - massL (S.gas Sign.pos) :=
    hS.aux_pos_mass
  rw [hm]
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology ComplexConjugate
open CapFields YCell

noncomputable section

local notation "π" => Real.pi

variable {S : CapSource}

/-! ### The radial reference -/

/-- The radial seed has an atom at the unit circle and dominates the fold band. -/
structure FoldSeed (S : CapSource) : Prop where
  atom : ∃ j, j < S.nRad ∧ S.sigma j = 0 ∧ S.radial j = 0
  dom : ∀ j, j < S.nRad → 10 * S.sigma j ≤ S.radial j

/-- The radii. -/
def seedR (S : CapSource) (j : Fin S.nRad) : ℝ := S.rad j

/-- The radial weights at size `N`. -/
def seedW (S : CapSource) (N : ℕ) (j : Fin S.nRad) : ℝ := Real.exp (-((N : ℝ) * S.radial j))

/-- The radial moments at size `N`. -/
def seedA (S : CapSource) (N : ℕ) : ℤ → ℝ := radialA2 (seedR S) (seedW S N)

theorem seedR_pos (j : Fin S.nRad) : 0 < seedR S j := rad_pos S j

theorem seedR_zpow (j : Fin S.nRad) (c : ℤ) :
    seedR S j ^ c = Real.exp (-((c : ℝ) * S.sigma j)) := by
  unfold seedR CapSource.rad
  rw [← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  ring

theorem seed_nonempty (hF : FoldSeed S) : 0 < S.nRad := by
  obtain ⟨j, hj, -⟩ := hF.atom
  omega

theorem seedA_pos (hF : FoldSeed S) (N : ℕ) (c : ℤ) : 0 < seedA S N c := by
  unfold seedA radialA2
  haveI : Nonempty (Fin S.nRad) := ⟨⟨0, seed_nonempty hF⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (zpow_pos (seedR_pos j) _))
    Finset.univ_nonempty

theorem seedA_mono (hS : S.Admissible) (N : ℕ) (c : ℤ) (hc : 0 ≤ c) :
    seedA S N c ≤ seedA S N (-c) := by
  unfold seedA radialA2
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [seedR_zpow, seedR_zpow, Real.exp_le_exp]
  have := hS.sigma_nonneg j
  push_cast
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  nlinarith

theorem seedA_ge_one (hF : FoldSeed S) (N : ℕ) (c : ℤ) : 1 ≤ seedA S N c := by
  obtain ⟨j, hj, h0, h1⟩ := hF.atom
  unfold seedA radialA2
  have hle := Finset.single_le_sum (f := fun j : Fin S.nRad => seedW S N j * seedR S j ^ (2 * c))
    (fun j _ => mul_nonneg (Real.exp_pos _).le (zpow_pos (seedR_pos j) _).le)
    (Finset.mem_univ (⟨j, hj⟩ : Fin S.nRad))
  refine le_trans ?_ hle
  simp only [seedW, seedR_zpow, h0, h1]
  simp

theorem seedA_neg_le (hS : S.Admissible) (hF : FoldSeed S) {N : ℕ} {c : ℤ} (h1 : 0 ≤ c)
    (h2 : c ≤ 5 * N) : seedA S N (-c) ≤ S.nRad := by
  unfold seedA radialA2
  calc _ ≤ ∑ _j : Fin S.nRad, (1 : ℝ) := Finset.sum_le_sum fun j _ => ?_
    _ = S.nRad := by simp
  unfold seedW
  rw [seedR_zpow, ← Real.exp_add, Real.exp_le_one_iff]
  have hd := hF.dom j j.2
  have hs := hS.sigma_nonneg j
  have hc : (c : ℝ) ≤ 5 * N := by exact_mod_cast h2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  nlinarith

theorem theta_le (hS : S.Admissible) (hF : FoldSeed S) (N : ℕ) (c : ℤ) :
    foldTheta (seedA S N) (5 * N) c ≤ S.nRad := by
  have hJ : (1 : ℝ) ≤ S.nRad := by exact_mod_cast seed_nonempty hF
  unfold foldTheta
  split_ifs with h
  · have a1 := seedA_ge_one hF N c
    have a2 := seedA_mono hS N c (by omega)
    have a3 := seedA_neg_le hS hF (N := N) (c := c) (by omega) (by exact_mod_cast h.2)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · exact hJ

/-- The product of the fold factors. -/
theorem theta_prod_le (hS : S.Admissible) (hF : FoldSeed S) {N D n : ℕ} :
    ∏ d : Fin n, foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) ≤ (S.nRad : ℝ) ^ (5 * N) := by
  have hJ : (1 : ℝ) ≤ S.nRad := by exact_mod_cast seed_nonempty hF
  set T := Finset.univ.filter (fun d : Fin n => 1 ≤ (d : ℤ) - D ∧ (d : ℤ) - D ≤ 5 * N) with hT
  have hsplit : ∏ d : Fin n, foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) =
      ∏ d ∈ T, foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro d _ hd
    have : ¬(1 ≤ (d : ℤ) - D ∧ (d : ℤ) - D ≤ (5 : ℤ) * N) := by simpa [hT] using hd
    unfold foldTheta
    push_cast
    rw [if_neg this]
  have hcard : T.card ≤ 5 * N := by
    have hmap : T.card ≤ (Finset.Icc (1 : ℤ) (5 * N)).card := by
      refine Finset.card_le_card_of_injOn (fun d => (d : ℤ) - D) (fun d hd => ?_) ?_
      · have := (Finset.mem_filter.mp hd).2
        simpa using this
      · intro a _ b _ h
        apply Fin.ext
        simp only at h
        omega
    rw [Int.card_Icc] at hmap
    omega
  rw [hsplit]
  calc _ ≤ ∏ _d ∈ T, (S.nRad : ℝ) := Finset.prod_le_prod₀
        (fun d _ => (lt_of_lt_of_le one_pos (foldTheta_ge_one (seedA_pos hF N)
          (seedA_mono hS N) _ _)).le) (fun d _ => theta_le hS hF N _)
    _ = (S.nRad : ℝ) ^ T.card := by simp
    _ ≤ _ := pow_le_pow_right₀ hJ hcard

/-! ### The quadrature sums -/

theorem quadNode_circ {L : ℕ} (hL : L ≠ 0) (r : Fin S.nRad → ℝ) (p : Fin S.nRad × Fin L) :
    quadNode L r p = circ (r p.1) (2 * π * (p.2 : ℕ) / L) := by
  unfold quadNode circ rootZ
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  field_simp

theorem pos_node_le (hS : S.Admissible) {N D : ℕ} (hD : D + 1 = 53 * N) {κ : ℝ}
    (hang : S.AngCap Trunc.exact Sign.pos κ) {L : ℕ} (hL : L ≠ 0) (p : Fin S.nRad × Fin L) :
    (quadWeight L (seedW S N) p * ‖quadNode L (seedR S) p ^ (-(D : ℤ))‖ ^ 2) *
        Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) p)) ≤
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * κ) / L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  set j := p.1
  have hr := seedR_pos j
  have hn : ‖quadNode L (seedR S) p‖ = seedR S j := by
    rw [quadNode_circ hL, circ_norm hr.le]
  have hnorm : ‖quadNode L (seedR S) p ^ (-(D : ℤ))‖ ^ 2 = Real.exp (2 * (D : ℝ) * S.sigma j) := by
    rw [norm_zpow, hn, seedR_zpow, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpot : planarPot (qP S) (quadNode L (seedR S) p) ≤
      κ - (53 * S.sigma j - S.radial j / 2) / 58 := by
    rw [quadNode_circ hL]
    unfold seedR
    rw [qP_angular hS]
    have := hang j j.2 (2 * π * (p.2 : ℕ) / L)
    linarith
  unfold quadWeight seedW
  rw [hnorm]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hDr : (D : ℝ) + 1 = 53 * N := by exact_mod_cast hD
  have hs := hS.sigma_nonneg j
  have e1 : Real.exp (-((N : ℝ) * S.radial j)) / L * Real.exp (2 * (D : ℝ) * S.sigma j) *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) p)) =
      Real.exp (-((N : ℝ) * S.radial j) + 2 * (D : ℝ) * S.sigma j +
        2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) p)) / L := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ hL0.le
  apply Real.exp_le_exp.mpr
  push_cast
  have hmul := mul_le_mul_of_nonneg_left hpot (by positivity : (0 : ℝ) ≤ 2 * (58 * N))
  have e2 : 2 * (58 * (N : ℝ)) * (κ - (53 * S.sigma j - S.radial j / 2) / 58) =
      2 * (58 * N) * κ - 106 * N * S.sigma j + N * S.radial j := by ring
  have hDe : (D : ℝ) = 53 * N - 1 := by linarith
  rw [hDe]
  nlinarith

theorem neg_node_le (hS : S.Admissible) {N : ℕ} {κ : ℝ}
    (hang : S.AngCap Trunc.exact Sign.neg κ) {L : ℕ} (hL : L ≠ 0) (p : Fin S.nRad × Fin L) :
    quadWeight L (seedW S N) p *
        Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qM S) (joukowski (quadNode L (seedR S) p))) ≤
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * (κ - 53 / 58 * Real.log 2 - cM S)) / L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
  set j := p.1
  have hpot : planarPot (qM S) (joukowski (quadNode L (seedR S) p)) ≤
      κ - (53 * S.sigma j - S.radial j / 2) / 58 -
        53 / 58 * (Real.log 2 + Real.log (S.rad j)) - cM S := by
    rw [quadNode_circ hL]
    unfold seedR
    rw [qM_angular hS]
    have := hang j j.2 (2 * π * (p.2 : ℕ) / L)
    linarith
  rw [log_rad] at hpot
  unfold quadWeight seedW
  have e1 : Real.exp (-((N : ℝ) * S.radial j)) / L *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qM S) (joukowski (quadNode L (seedR S) p))) =
      Real.exp (-((N : ℝ) * S.radial j) +
        2 * ((58 * N : ℕ) : ℝ) * planarPot (qM S) (joukowski (quadNode L (seedR S) p))) / L := by
    rw [Real.exp_add]
    ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ hL0.le
  apply Real.exp_le_exp.mpr
  push_cast
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hmul := mul_le_mul_of_nonneg_left hpot (by positivity : (0 : ℝ) ≤ 2 * (58 * N))
  nlinarith

theorem node_sum_le {L : ℕ} (hL : L ≠ 0) {f : Fin S.nRad × Fin L → ℝ} {B : ℝ}
    (h : ∀ p, f p ≤ B / L) : ∑ p, f p ≤ S.nRad * B := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  calc ∑ p, f p ≤ ∑ _p : Fin S.nRad × Fin L, B / L := Finset.sum_le_sum fun p _ => h p
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      field_simp

/-- **The completed-gas determinant bound with the radial quadrature.** -/
theorem gas_quad_bound (hS : S.Admissible) (hF : FoldSeed S) {κp κm : ℝ}
    (hp : S.AngCap Trunc.exact Sign.pos κp) (hm : S.AngCap Trunc.exact Sign.neg κm)
    {η : ℝ} (hη : 0 < η) :
    ∃ Lp Lm : ℕ, ∀ (N kp k s D : ℕ), 0 < N → kp + k = 58 * N → k + s = 53 * N → D + 1 = 53 * N →
      ∀ (ξ : Fin kp → ℝ) (x : Fin k → ℝ), (∀ p, ξ p ≠ 0) → (∀ b, x b ≠ 0) →
      (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a)) ≤
        (∏ p, ξ p ^ (-(D : ℤ))) ^ 2 * (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) ^ 2 *
          (S.nRad : ℝ) ^ (5 * N) *
          (Real.exp (2 * ((58 * N : ℕ) : ℝ) * ∑ p, planarPot (qP S) (ξ p) -
              ((58 * N : ℕ) : ℝ) ^ 2 * planarEnergy (qP S) +
              2 * ((58 * N : ℕ) : ℝ) * ((58 * N : ℕ) : ℝ) * η +
              ((58 * N : ℕ) : ℝ) / 2 * harm Lp) *
            (S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * κp)) ^ k) *
          (Real.exp (2 * ((58 * N : ℕ) : ℝ) * ∑ b, planarPot (qM S) (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ) -
              ((58 * N : ℕ) : ℝ) ^ 2 * planarEnergy (qM S) +
              2 * ((58 * N : ℕ) : ℝ) * ((53 * N : ℕ) : ℝ) * η +
              ((53 * N : ℕ) : ℝ) / 2 * harm Lm) *
            (S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * (κm - 53 / 58 * Real.log 2 - cM S))) ^ s) := by
  obtain ⟨fp, ⟨Cp, hCp, hbp⟩, hhp⟩ := qP_good hS
  obtain ⟨fm, ⟨Cm, hCm, hbm⟩, hhm⟩ := qM_good hS
  obtain ⟨Lp, Lm, H⟩ := gas_det_bound hCp hCm hbp hbm hhp hhm hη
  refine ⟨Lp, Lm, fun N kp k s D hN hkp hks hD ξ x hξ hx => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set L := 2 * D + 1 with hLdef
  have hL : L ≠ 0 := by omega
  have hmp : ((58 * N : ℕ) : ℝ) * (qP S).real Set.univ = ((kp + k : ℕ) : ℝ) := by
    rw [qP_mass hS, hkp, mul_one]
  have hmm : ((58 * N : ℕ) : ℝ) * (qM S).real Set.univ = ((k + s : ℕ) : ℝ) := by
    rw [qM_mass hS, hks]
    push_cast
    ring
  have hnD : kp + k = D + 5 * N + 1 := by omega
  have hθ1 : ∀ d : Fin (kp + k), 1 ≤ foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) := fun d =>
    foldTheta_ge_one (seedA_pos hF N) (seedA_mono hS N) _ _
  have main := H kp k s D ((58 * N : ℕ) : ℝ) (Nat.cast_nonneg _) hmp hmm (by omega) (by omega)
    ξ x hξ hx (X := Fin S.nRad × Fin L) (w := quadWeight L (seedW S N))
    (γ := quadNode L (seedR S)) (A := seedA S N)
    (fun p => div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
    (quadNode_ne_zero hL seedR_pos) (seedA_pos hF N)
    (quad_ortho (by omega) (seedR S) (seedW S N) seedR_pos)
    (fun d => foldTheta (seedA S N) (5 * N) ((d : ℤ) - D)) hθ1
    (fun a _ => by
      have := foldTheta_fibre (seedA_pos hF N) (seedA_mono hS N) (n := kp + k) (D := D)
        (g := 5 * N) hnD a
      exact this)
  have hfact : (1 : ℝ) ≤ (k.factorial : ℝ) * (s.factorial : ℝ) := by
    have h1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h2 : (1 : ℝ) ≤ s.factorial := by exact_mod_cast Nat.factorial_pos s
    nlinarith
  have hG : 0 ≤ ∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a) :=
    Finset.prod_nonneg fun a _ => (foldG_pos (seedA_pos hF N) _).le
  have hlhs : (laurentM (-(D : ℤ)) ξ x).det ^ 2 *
      (∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a)) ≤
      (laurentM (-(D : ℤ)) ξ x).det ^ 2 * (∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a)) *
        ((k.factorial : ℝ) * (s.factorial : ℝ)) :=
    le_mul_of_one_le_right (by positivity) hfact
  refine hlhs.trans (main.trans ?_)
  have s1 : ∑ y, (quadWeight L (seedW S N) y * ‖quadNode L (seedR S) y ^ (-(D : ℤ))‖ ^ 2) *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) y)) ≤
      S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * κp) :=
    node_sum_le hL fun p => pos_node_le hS hD hp hL p
  have s2 : ∑ y, quadWeight L (seedW S N) y * Real.exp (2 * ((58 * N : ℕ) : ℝ) *
      planarPot (qM S) (joukowski (quadNode L (seedR S) y))) ≤
      S.nRad * Real.exp (2 * ((58 * N : ℕ) : ℝ) * (κm - 53 / 58 * Real.log 2 - cM S)) :=
    node_sum_le hL fun p => neg_node_le hS hm hL p
  have nn1 : 0 ≤ ∑ y, (quadWeight L (seedW S N) y * ‖quadNode L (seedR S) y ^ (-(D : ℤ))‖ ^ 2) *
      Real.exp (2 * ((58 * N : ℕ) : ℝ) * planarPot (qP S) (quadNode L (seedR S) y)) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg
      (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (sq_nonneg _)) (Real.exp_pos _).le
  have nn2 : 0 ≤ ∑ y, quadWeight L (seedW S N) y * Real.exp (2 * ((58 * N : ℕ) : ℝ) *
      planarPot (qM S) (joukowski (quadNode L (seedR S) y))) :=
    Finset.sum_nonneg fun y _ => mul_nonneg
      (div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hθ := theta_prod_le hS hF (N := N) (D := D) (n := kp + k)
  have hθ0 : 0 ≤ ∏ d : Fin (kp + k), foldTheta (seedA S N) (5 * N) ((d : ℤ) - D) :=
    Finset.prod_nonneg fun d _ => zero_le_one.trans (hθ1 d)
  have hJ0 : (0 : ℝ) ≤ S.nRad := Nat.cast_nonneg _
  have e1 : ((kp + k : ℕ) : ℝ) = ((58 * N : ℕ) : ℝ) := by rw [hkp]
  have e2 : ((k + s : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hks]
  rw [e1, e2]
  gcongr

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset Filter Set
open scoped BigOperators
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

theorem abs_det_submatrix {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix α α ℝ) (e c : β ≃ α) : |(M.submatrix e c).det| = |M.det| := by
  have h : M.submatrix e c = (M.submatrix id (e.symm.trans c).symm.symm).submatrix e e := by
    ext i j
    simp
  rw [h, Matrix.det_submatrix_equiv_self]
  have hp := Matrix.det_permute' (e.symm.trans c) M
  have e2 : M.submatrix id (e.symm.trans c).symm.symm = M.submatrix id (e.symm.trans c) := rfl
  rw [e2, hp, abs_mul]
  have : |((Equiv.Perm.sign (e.symm.trans c) : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (e.symm.trans c)) with h | h <;> simp [h]
  rw [this, one_mul]

/-- With more than `D+1` negative rows the folded rows are dependent. -/
theorem laurentM_det_zero {kp k D g : ℕ} (hn : kp + k = D + g + 1) (hg : g ≤ D) (ξ : Fin kp → ℝ)
    (x : Fin k → ℝ) (hk : D + 1 < k) : (laurentM (-(D : ℤ)) ξ x).det = 0 := by
  set u : Fin (D + 1) → Fin k → ℝ := fun d b =>
    (1 / 2 : ℝ) * x b ^ ((d : ℕ) : ℤ) + (1 / 2 : ℝ) * x b ^ (-(((d : ℕ) : ℤ))) with hu
  set f := Matrix.mulVecLin (Matrix.of u) with hf
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hrel : ∀ d : Fin (D + 1), ∑ b, u d b * l b = 0 := by
    intro d
    have := congrFun (LinearMap.mem_ker.mp hl) d
    simpa [hf, Matrix.mulVec, dotProduct] using this
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨Sum.elim 0 l, ?_, ?_⟩
  · intro h
    apply hl0
    funext b
    exact congrFun h (Sum.inr b)
  · funext a
    have ha := colDeg_lt a
    set c : ℤ := (colDeg a : ℤ) + (-(D : ℤ)) with hc
    have hb : c.natAbs < D + 1 := by omega
    have key : ∀ b, (1 / 2 : ℝ) * x b ^ c + (1 / 2 : ℝ) * x b ^ (-c) =
        u ⟨c.natAbs, hb⟩ b := by
      intro b
      simp only [hu]
      rcases Int.natAbs_eq c with h | h
      · rw [← h]
      · have h2 : (c.natAbs : ℤ) = -c := by omega
        rw [h2, neg_neg]
        ring
    have := hrel ⟨c.natAbs, hb⟩
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, laurentM, Matrix.of_apply]
    calc _ = ∑ b, u ⟨c.natAbs, hb⟩ b * l b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← key b, mul_comm]
      _ = 0 := this

/-- Reindex of the comparison matrix to the split matrix. -/
theorem comparison_split {n g D : ℕ} (hn : n = D + g + 1) (z : Fin n → ℝ) (hz : ∀ i, z i ≠ 0)
    (T : Finset (Fin n)) :
    ∃ (kp k : ℕ) (e : Fin kp ⊕ Fin k ≃ Fin n) (ξ : Fin kp → ℝ) (x : Fin k → ℝ),
      kp + k = n ∧
      (∀ p, (e (Sum.inl p) ∈ T ∧ ξ p = (z (e (Sum.inl p)))⁻¹) ∨
        (e (Sum.inl p) ∉ T ∧ 0 ≤ z (e (Sum.inl p)) ∧ ξ p = z (e (Sum.inl p)))) ∧
      (∀ b, e (Sum.inr b) ∉ T ∧ z (e (Sum.inr b)) < 0 ∧ x b = z (e (Sum.inr b))) ∧
      |(comparisonLaurent g z T).det| = |(laurentM (-(D : ℤ)) ξ x).det| := by
  classical
  set pr : Fin n → Prop := fun i => i ∈ T ∨ 0 ≤ z i with hpr
  set kp := Fintype.card {i // pr i} with hkp
  set k := Fintype.card {i // ¬pr i} with hk
  have hsum : kp + k = n := by
    have := Fintype.card_subtype_compl pr
    have h2 := Fintype.card_subtype_le pr
    have h3 : Fintype.card (Fin n) = n := Fintype.card_fin n
    rw [hkp, hk]
    omega
  set e1 : Fin kp ≃ {i // pr i} := (Fintype.equivFin _).symm with he1
  set e2 : Fin k ≃ {i // ¬pr i} := (Fintype.equivFin _).symm with he2
  set e : Fin kp ⊕ Fin k ≃ Fin n := (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl pr) with he
  have heL : ∀ p, pr (e (Sum.inl p)) := fun p => by
    simpa [he] using (e1 p).2
  have heR : ∀ b, ¬pr (e (Sum.inr b)) := fun b => by
    simpa [he] using (e2 b).2
  set ξ : Fin kp → ℝ := fun p =>
    if e (Sum.inl p) ∈ T then (z (e (Sum.inl p)))⁻¹ else z (e (Sum.inl p)) with hξ
  set x : Fin k → ℝ := fun b => z (e (Sum.inr b)) with hx
  refine ⟨kp, k, e, ξ, x, hsum, fun p => ?_, fun b => ?_, ?_⟩
  · by_cases h : e (Sum.inl p) ∈ T
    · exact Or.inl ⟨h, by simp [hξ, h]⟩
    · have := (heL p).resolve_left h
      exact Or.inr ⟨h, this, by simp [hξ, h]⟩
  · have h := heR b
    simp only [hpr, not_or, not_le] at h
    exact ⟨h.1, h.2, rfl⟩
  · set c : Fin kp ⊕ Fin k ≃ Fin n :=
      (finSumFinEquiv.trans (finCongr hsum)).trans Fin.revPerm with hc
    have hcv : ∀ a, ((c a : ℕ) : ℤ) = (n : ℤ) - 1 - (colDeg a : ℤ) := by
      intro a
      have h1 : ((finSumFinEquiv a : Fin (kp + k)) : ℕ) = colDeg a := (colDeg_eq a).symm
      have h2 : colDeg a < n := by
        have := colDeg_lt a
        omega
      have h3 : ((c a : Fin n) : ℕ) = n - (colDeg a + 1) := by
        simp [hc, Fin.revPerm, Fin.val_rev, h1]
      omega
    have hm : (comparisonLaurent g z T).submatrix e c = laurentM (-(D : ℤ)) ξ x := by
      ext r a
      have e1' : (g : ℤ) - ((c a : ℕ) : ℤ) = (colDeg a : ℤ) + (-(D : ℤ)) := by
        rw [hcv a]
        omega
      have e2' : ((c a : ℕ) : ℤ) - (g : ℤ) = -((colDeg a : ℤ) + (-(D : ℤ))) := by
        rw [hcv a]
        omega
      rcases r with p | b
      · simp only [Matrix.submatrix_apply, comparisonLaurent, laurentM, Matrix.of_apply]
        by_cases h : e (Sum.inl p) ∈ T
        · simp only [if_pos h, hξ]
          rw [e2', zpow_neg, inv_zpow]
        · have h0 := (heL p).resolve_left h
          have h1 : ¬z (e (Sum.inl p)) < 0 := not_lt.mpr h0
          simp only [if_neg h, if_neg h1, hξ]
          rw [e1']
      · have hb := heR b
        simp only [hpr, not_or, not_le] at hb
        simp only [Matrix.submatrix_apply, comparisonLaurent, laurentM, Matrix.of_apply,
          if_neg hb.1, if_pos hb.2, actualLaurentEntry, hx]
        rw [e1', e2']
    rw [← hm, abs_det_submatrix]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields

noncomputable section

variable {S : CapSource}

/-! ### The fold denominator -/

/-- The Legendre transform of the radial law. -/
def seedTau (S : CapSource) (q : ℝ) : ℝ :=
  ⨆ j : Fin S.nRad, (2 * q * S.sigma j - S.radial j)

theorem seedTau_ge (q : ℝ) (j : Fin S.nRad) : 2 * q * S.sigma j - S.radial j ≤ seedTau S q :=
  le_ciSup (f := fun j : Fin S.nRad => 2 * q * S.sigma j - S.radial j)
    (Set.finite_range _).bddAbove j

theorem seedTau_mono (hS : S.Admissible) (hF : FoldSeed S) : Monotone (seedTau S) := by
  intro a b hab
  haveI : Nonempty (Fin S.nRad) := ⟨⟨0, seed_nonempty hF⟩⟩
  refine ciSup_mono (Set.finite_range _).bddAbove fun j => ?_
  have := hS.sigma_nonneg j
  nlinarith

theorem seedTau_attained (hF : FoldSeed S) (q : ℝ) :
    ∃ j : Fin S.nRad, seedTau S q = 2 * q * S.sigma j - S.radial j := by
  haveI : Nonempty (Fin S.nRad) := ⟨⟨0, seed_nonempty hF⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite
    (f := fun j : Fin S.nRad => 2 * q * S.sigma j - S.radial j)
  exact ⟨j, hj.symm⟩

theorem seedA_neg_ge (hF : FoldSeed S) {N : ℕ} (hN : 0 < N) (a : ℕ) :
    Real.exp ((N : ℝ) * seedTau S ((a : ℝ) / N)) ≤ seedA S N (-(a : ℤ)) := by
  obtain ⟨j, hj⟩ := seedTau_attained hF ((a : ℝ) / N)
  unfold seedA radialA2
  have hle := Finset.single_le_sum (f := fun j : Fin S.nRad =>
    seedW S N j * seedR S j ^ (2 * (-(a : ℤ))))
    (fun j _ => mul_nonneg (Real.exp_pos _).le (zpow_pos (seedR_pos j) _).le) (Finset.mem_univ j)
  refine le_trans (le_of_eq ?_) hle
  simp only [seedW]
  rw [seedR_zpow, ← Real.exp_add, hj]
  congr 1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp
  ring

theorem cheb_factor (hF : FoldSeed S) {N : ℕ} (hN : 0 < N) (a : ℕ) :
    chebLead (a + 1) ^ 2 ≤
      Real.exp (2 * ((a : ℝ) + 1) * Real.log 2 -
        (N : ℝ) * seedTau S (((a + 1 : ℕ) : ℝ) / N)) * foldG (seedA S N) (a + 1) := by
  have h1 : chebLead (a + 1) = 2 ^ a := by
    unfold chebLead
    rw [Polynomial.Chebyshev.leadingCoeff_T]
    have : (((a + 1 : ℕ) : ℤ)).natAbs - 1 = a := by omega
    rw [this]
  have h2 : foldG (seedA S N) (a + 1) =
      (seedA S N ((a + 1 : ℕ) : ℤ) + seedA S N (-((a + 1 : ℕ) : ℤ))) / 4 := by
    simp [foldG]
  set E := Real.exp ((N : ℝ) * seedTau S (((a + 1 : ℕ) : ℝ) / N)) with hE
  have hEp : 0 < E := Real.exp_pos _
  have h3 : E / 4 ≤ foldG (seedA S N) (a + 1) := by
    rw [h2]
    have := seedA_neg_ge hF hN (a + 1)
    have h4 := seedA_pos hF N ((a + 1 : ℕ) : ℤ)
    linarith
  have h5 : Real.exp (2 * ((a : ℝ) + 1) * Real.log 2 -
      (N : ℝ) * seedTau S (((a + 1 : ℕ) : ℝ) / N)) = 4 * (2 ^ a) ^ 2 / E := by
    rw [Real.exp_sub, hE]
    congr 1
    have : 2 * ((a : ℝ) + 1) * Real.log 2 = Real.log (4 * (2 ^ a) ^ 2) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [this]
      push_cast
      ring
    rw [this, Real.exp_log (by positivity)]
  rw [h1, h5]
  calc ((2 : ℝ) ^ a) ^ 2 = 4 * (2 ^ a) ^ 2 / E * (E / 4) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem cheb_prod_range (hF : FoldSeed S) {N : ℕ} (hN : 0 < N) (D : ℕ) :
    (∏ a ∈ Finset.range (D + 1), chebLead a) ^ 2 ≤
      Real.exp ((D : ℝ) * ((D : ℝ) + 1) * Real.log 2 -
        (N : ℝ) * ∑ i ∈ Finset.range D, seedTau S (((i + 1 : ℕ) : ℝ) / N)) *
      ∏ a ∈ Finset.range (D + 1), foldG (seedA S N) a := by
  induction D with
  | zero =>
    have h1 : chebLead 0 = 1 := by simp [chebLead]
    have h2 : foldG (seedA S N) 0 = seedA S N 0 := by simp [foldG]
    have h3 := seedA_ge_one hF N 0
    simpa [h1, h2] using h3
  | succ D ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ _ (D + 1), Finset.sum_range_succ, mul_pow]
    have hc := cheb_factor hF hN D
    have hp : 0 ≤ (∏ a ∈ Finset.range (D + 1), chebLead a) ^ 2 := by positivity
    have hq : 0 ≤ chebLead (D + 1) ^ 2 := by positivity
    calc _ ≤ _ := mul_le_mul ih hc hq (by
            refine mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun a _ => ?_)
            exact (foldG_pos (seedA_pos hF N) a).le)
      _ = _ := by
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 2
        push_cast
        ring

/-- A right Riemann sum of a monotone function dominates its integral. -/
theorem right_riemann_ge {f : ℝ → ℝ} (hf : Monotone f) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    (N : ℝ) ^ 2 * ∫ q in (0 : ℝ)..(M : ℝ) / N, f q ≤
      (N : ℝ) * ∑ i ∈ Finset.range M, f (((i + 1 : ℕ) : ℝ) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  induction M with
  | zero => simp
  | succ M ih =>
    have hab : ((M : ℝ) / N) ≤ ((M + 1 : ℕ) : ℝ) / N := by
      push_cast
      gcongr
      linarith
    have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
      hf.intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 ((M : ℝ) / N))
      (hint ((M : ℝ) / N) (((M + 1 : ℕ) : ℝ) / N))
    have hlast : ∫ q in ((M : ℝ) / N)..(((M + 1 : ℕ) : ℝ) / N), f q ≤
        f (((M + 1 : ℕ) : ℝ) / N) / N := by
      have h1 := intervalIntegral.integral_mono_on hab (hint _ _)
        (intervalIntegrable_const (c := f (((M + 1 : ℕ) : ℝ) / N)))
        (fun x hx => hf hx.2)
      refine h1.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [← hsplit, Finset.sum_range_succ, mul_add, mul_add]
    have h2 : (N : ℝ) ^ 2 * ∫ q in ((M : ℝ) / N)..(((M + 1 : ℕ) : ℝ) / N), f q ≤
        (N : ℝ) * f (((M + 1 : ℕ) : ℝ) / N) := by
      calc _ ≤ (N : ℝ) ^ 2 * (f (((M + 1 : ℕ) : ℝ) / N) / N) :=
            mul_le_mul_of_nonneg_left hlast (by positivity)
        _ = _ := by
            field_simp
    linarith

/-- The total Legendre integral. -/
def tauInt (S : CapSource) : ℝ := ∫ q in (0 : ℝ)..53, seedTau S q

theorem prod_colDeg {k s : ℕ} (F : ℕ → ℝ) :
    ∏ a : Fin k ⊕ Fin s, F (colDeg a) = ∏ d ∈ Finset.range (k + s), F d := by
  simp only [Fintype.prod_sum_type, colDeg]
  rw [Finset.prod_range_add, Fin.prod_univ_eq_prod_range (fun j => F j) k,
    Fin.prod_univ_eq_prod_range (fun i => F (k + i)) s]

/-- The fold denominator in the Legendre integral. -/
theorem den_bound (hS : S.Admissible) (hF : FoldSeed S) {N k s D : ℕ} (hN : 0 < N)
    (hks : k + s = 53 * N) (hD : D + 1 = 53 * N) :
    (∏ a : Fin k ⊕ Fin s, chebLead (colDeg a)) ^ 2 ≤
      Real.exp ((D : ℝ) * ((D : ℝ) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S +
        (N : ℝ) * seedTau S 53) * ∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [prod_colDeg, prod_colDeg, hks, ← hD]
  refine (cheb_prod_range hF hN D).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.prod_nonneg fun a _ => (foldG_pos (seedA_pos hF N) a).le)
  rw [Real.exp_le_exp]
  have hr := right_riemann_ge (seedTau_mono hS hF) hN (D + 1)
  have e1 : (((D + 1 : ℕ) : ℝ)) / N = 53 := by
    rw [hD]
    push_cast
    field_simp
  rw [e1, Finset.sum_range_succ, e1] at hr
  unfold tauInt
  rw [mul_add] at hr
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields
open CatalanMeasure.GenD.Signed.PhysicalPick

noncomputable section

variable {S : CapSource}

/-! ### The completed-gas master inequality -/

/-- The gas contribution of a positive-gas row at the point `ξ`. -/
def pRow (S : CapSource) (κ : ℝ) (D N : ℕ) (ξ : ℝ) : ℝ :=
  -(D : ℝ) * Real.log |ξ| + ((58 * N : ℕ) : ℝ) * (planarPot (qP S) (ξ : ℂ) - κ)

/-- The gas contribution of a negative-gas row at the point `x`. -/
def mRow (S : CapSource) (c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ((58 * N : ℕ) : ℝ) * (planarPot (qM S) (((x + x⁻¹) / 2 : ℝ) : ℂ) - c)

/-- The gas contribution of a row of the comparison matrix. -/
def gasRow (S : CapSource) (κ c : ℝ) (D N : ℕ) {n : ℕ} (z : Fin n → ℝ) (T : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if i ∈ T then pRow S κ D N (z i)⁻¹
  else if 0 ≤ z i then pRow S κ D N (z i) else mRow S c N (z i)

/-- The configuration-independent part of the master inequality. -/
def gasK (S : CapSource) (κ c : ℝ) (D N : ℕ) : ℝ :=
  2 * ((58 * N : ℕ) : ℝ) ^ 2 * κ + 2 * ((53 * N : ℕ) : ℝ) * ((58 * N : ℕ) : ℝ) * c +
    (D : ℝ) * ((D : ℝ) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S -
    ((58 * N : ℕ) : ℝ) ^ 2 * (planarEnergy (qP S) + planarEnergy (qM S))

theorem log_bound_aux {M X J Q e1 e2 a b : ℝ} {k s f : ℕ} (hM : M ≠ 0) (hX : X ≠ 0) (hJ : 0 < J)
    (h : M ^ 2 ≤ X ^ 2 * Real.exp Q * J ^ f * (Real.exp e1 * (J * Real.exp a) ^ k) *
      (Real.exp e2 * (J * Real.exp b) ^ s)) :
    2 * Real.log |M| ≤ 2 * Real.log |X| + Q + (f : ℝ) * Real.log J + e1 +
      (k : ℝ) * (Real.log J + a) + e2 + (s : ℝ) * (Real.log J + b) := by
  have hl := Real.log_le_log (by positivity) h
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero _ hX
  have hJf : J ^ f ≠ 0 := pow_ne_zero _ hJ.ne'
  have hE : ∀ t : ℝ, Real.exp t ≠ 0 := Real.exp_ne_zero
  have hJa : ∀ (t : ℝ) (m : ℕ), (J * Real.exp t) ^ m ≠ 0 := fun t m =>
    pow_ne_zero _ (mul_ne_zero hJ.ne' (hE t))
  rw [Real.log_pow] at hl
  rw [Real.log_mul (by simp only [ne_eq, mul_eq_zero, not_or]; exact
        ⟨⟨⟨hX2, hE _⟩, hJf⟩, hE _, hJa _ _⟩) (mul_ne_zero (hE _) (hJa _ _)),
    Real.log_mul (by simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨⟨hX2, hE _⟩, hJf⟩)
      (mul_ne_zero (hE _) (hJa _ _)),
    Real.log_mul (mul_ne_zero hX2 (hE _)) hJf, Real.log_mul hX2 (hE _),
    Real.log_mul (hE _) (hJa _ _), Real.log_mul (hE _) (hJa _ _),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul hJ.ne' (hE _), Real.log_mul hJ.ne' (hE _),
    Real.log_exp, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_exp] at hl
  rw [Real.log_abs, Real.log_abs]
  push_cast at hl
  linarith

theorem log_abs_prod_zpow {kp : ℕ} (D : ℕ) (ξ : Fin kp → ℝ) (hξ : ∀ p, ξ p ≠ 0) :
    Real.log |∏ p, ξ p ^ (-(D : ℤ))| = -(D : ℝ) * ∑ p, Real.log |ξ p| := by
  rw [Real.log_abs, Real.log_prod (fun p _ => zpow_ne_zero _ (hξ p)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_zpow, Real.log_abs]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **The completed-gas master inequality** for the comparison matrix: the squared determinant is
at most the rows' gas potentials, the configuration-independent constant and an error of size
`4 η n² + C n`, with `C` fixed before `N` and the configuration. -/
theorem gas_master (hS : S.Admissible) (hF : FoldSeed S) {κp κm : ℝ}
    (hp : S.AngCap Trunc.exact Sign.pos κp) (hm : S.AngCap Trunc.exact Sign.neg κm)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N D : ℕ), 0 < N → D + 1 = 53 * N →
      ∀ (z : Fin (58 * N) → ℝ) (T : Finset (Fin (58 * N))), (∀ i, z i ≠ 0) →
      (comparisonLaurent (5 * N) z T).det ≠ 0 →
      2 * Real.log |(comparisonLaurent (5 * N) z T).det| ≤
        2 * ∑ i, gasRow S κp (κm - 53 / 58 * Real.log 2 - cM S) D N z T i +
        gasK S κp (κm - 53 / 58 * Real.log 2 - cM S) D N +
        4 * ((58 * N : ℕ) : ℝ) ^ 2 * η + C * ((58 * N : ℕ) : ℝ) := by
  obtain ⟨Lp, Lm, H⟩ := gas_quad_bound hS hF hp hm hη
  have hJ1 : (1 : ℝ) ≤ S.nRad := by exact_mod_cast seed_nonempty hF
  have hJ0 : (0 : ℝ) < S.nRad := by linarith
  have hlJ : 0 ≤ Real.log S.nRad := Real.log_nonneg hJ1
  refine ⟨Real.log S.nRad + |seedTau S 53| + |harm Lp| + |harm Lm|, by positivity,
    fun N D hN hD z T hz hdet => ?_⟩
  set c : ℝ := κm - 53 / 58 * Real.log 2 - cM S with hc
  have hn' : 58 * N = D + 5 * N + 1 := by omega
  obtain ⟨kp, k, e, ξ, x, hsum, hL, hR, habs⟩ := comparison_split hn' z hz T
  have hsum' : kp + k = D + 5 * N + 1 := by omega
  have hM : (laurentM (-(D : ℤ)) ξ x).det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact hdet (abs_eq_zero.mp habs)
  have hk : k ≤ 53 * N := by
    by_contra hcon
    exact hM (laurentM_det_zero hsum' (by omega) ξ x (by omega))
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hk
  have hks : k + s = 53 * N := hs.symm
  have hξ : ∀ p, ξ p ≠ 0 := by
    intro p
    rcases hL p with ⟨-, h⟩ | ⟨-, -, h⟩
    · rw [h]
      exact inv_ne_zero (hz _)
    · rw [h]
      exact hz _
  have hx : ∀ b, x b ≠ 0 := fun b => by
    rw [(hR b).2.2]
    exact hz _
  have main := H N kp k s D hN hsum hks hD ξ x hξ hx
  have den := den_bound hS hF (k := k) (s := s) (D := D) hN hks hD
  set F := ∏ a : Fin k ⊕ Fin s, foldG (seedA S N) (colDeg a) with hFdef
  have hF0 : 0 < F := Finset.prod_pos fun a _ => foldG_pos (seedA_pos hF N) _
  set X := ∏ p, ξ p ^ (-(D : ℤ)) with hX
  have hX0 : X ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => zpow_ne_zero _ (hξ p)
  set Q : ℝ := (D : ℝ) * ((D : ℝ) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S +
    (N : ℝ) * seedTau S 53 with hQ
  set n : ℝ := ((58 * N : ℕ) : ℝ) with hn
  set w : ℝ := ((53 * N : ℕ) : ℝ) with hw
  set Bp : ℝ := ∑ p, planarPot (qP S) (ξ p) with hBp
  set Bm : ℝ := ∑ b, planarPot (qM S) (((x b + (x b)⁻¹) / 2 : ℝ) : ℂ) with hBm
  set e1 : ℝ := 2 * n * Bp - n ^ 2 * planarEnergy (qP S) + 2 * n * n * η + n / 2 * harm Lp with he1
  set e2 : ℝ := 2 * n * Bm - n ^ 2 * planarEnergy (qM S) + 2 * n * w * η + w / 2 * harm Lm with he2
  have hnn : 0 ≤ n := Nat.cast_nonneg _
  have step : (laurentM (-(D : ℤ)) ξ x).det ^ 2 ≤
      X ^ 2 * Real.exp Q * (S.nRad : ℝ) ^ (5 * N) *
        (Real.exp e1 * (S.nRad * Real.exp (2 * n * κp)) ^ k) *
        (Real.exp e2 * (S.nRad * Real.exp (2 * n * c)) ^ s) := by
    refine le_of_mul_le_mul_right ?_ hF0
    refine main.trans ?_
    calc _ ≤ X ^ 2 * (Real.exp Q * F) * (S.nRad : ℝ) ^ (5 * N) *
          (Real.exp e1 * (S.nRad * Real.exp (2 * n * κp)) ^ k) *
          (Real.exp e2 * (S.nRad * Real.exp (2 * n * c)) ^ s) := by
          gcongr
      _ = _ := by ring
  have hlog := log_bound_aux hM hX0 hJ0 step
  rw [hX, log_abs_prod_zpow D ξ hξ] at hlog
  rw [habs]
  have hrow : ∑ i, gasRow S κp c D N z T i =
      ∑ p, pRow S κp D N (ξ p) + ∑ b, mRow S c N (x b) := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      unfold gasRow
      rcases hL p with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [if_pos h1, h2]
      · rw [if_neg h1, if_pos h2, h3]
    · refine Finset.sum_congr rfl fun b _ => ?_
      obtain ⟨h1, h2, h3⟩ := hR b
      unfold gasRow
      rw [if_neg h1, if_neg (not_le.mpr h2), h3]
  have hP : ∑ p, pRow S κp D N (ξ p) =
      -(D : ℝ) * (∑ p, Real.log |ξ p|) + n * (Bp - (kp : ℝ) * κp) := by
    simp only [pRow, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hMm : ∑ b, mRow S c N (x b) = n * (Bm - (k : ℝ) * c) := by
    simp only [mRow, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  rw [hrow, hP, hMm]
  unfold gasK
  rw [← hn, ← hw]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnN : n = 58 * (N : ℝ) := by rw [hn]; push_cast; ring
  have hwN : w = 53 * (N : ℝ) := by rw [hw]; push_cast; ring
  have hkp : (kp : ℝ) = n - k := by
    have : ((kp + k : ℕ) : ℝ) = n := by rw [hsum]
    push_cast at this
    linarith
  have hsr : (s : ℝ) = w - k := by
    have : ((k + s : ℕ) : ℝ) = w := by rw [hks]
    push_cast at this
    linarith
  have hNn : (N : ℝ) ≤ n := by rw [hnN]; linarith
  have hwn : w ≤ n := by rw [hwN, hnN]; linarith
  have ht : (N : ℝ) * seedTau S 53 ≤ n * |seedTau S 53| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hNr.le).trans
      (mul_le_mul_of_nonneg_right hNn (abs_nonneg _))
  have h1 : n / 2 * harm Lp ≤ n * |harm Lp| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have h2 : w / 2 * harm Lm ≤ n * |harm Lm| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by rw [hwN]; positivity)).trans
      (mul_le_mul_of_nonneg_right (by rw [hwN, hnN]; linarith) (abs_nonneg _))
  have h3 : 2 * n * w * η ≤ 2 * n ^ 2 * η := by
    have : n * w ≤ n * n := mul_le_mul_of_nonneg_left hwn hnn
    have e1' : 2 * n * w * η = 2 * η * (n * w) := by ring
    have e2' : 2 * n ^ 2 * η = 2 * η * (n * n) := by ring
    rw [e1', e2']
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hJc : ((5 * N : ℕ) : ℝ) * Real.log S.nRad + (k : ℝ) * Real.log S.nRad +
      (s : ℝ) * Real.log S.nRad = n * Real.log S.nRad := by
    rw [hsr, hnN, hwN]
    push_cast
    ring
  have hid : 2 * (-(D : ℝ) * (∑ p, Real.log |ξ p|)) + Q +
      ((5 * N : ℕ) : ℝ) * Real.log S.nRad + e1 + (k : ℝ) * (Real.log S.nRad + 2 * n * κp) + e2 +
      (s : ℝ) * (Real.log S.nRad + 2 * n * c) =
      2 * (-(D : ℝ) * (∑ p, Real.log |ξ p|) + n * (Bp - (kp : ℝ) * κp) +
        n * (Bm - (k : ℝ) * c)) +
      (2 * n ^ 2 * κp + 2 * w * n * c + (D : ℝ) * ((D : ℝ) + 1) * Real.log 2 -
        (N : ℝ) ^ 2 * tauInt S - n ^ 2 * (planarEnergy (qP S) + planarEnergy (qM S))) +
      (n * Real.log S.nRad + (N : ℝ) * seedTau S 53 + 2 * n * n * η + 2 * n * w * η +
        n / 2 * harm Lp + w / 2 * harm Lm) := by
    rw [← hJc, hkp, hsr, he1, he2, hQ]
    ring
  have hlog2 := hlog.trans_eq hid
  have e3 : 2 * n * n * η = 2 * n ^ 2 * η := by ring
  have e4 : (Real.log S.nRad + |seedTau S 53| + |harm Lp| + |harm Lm|) * n =
      n * Real.log S.nRad + n * |seedTau S 53| + n * |harm Lp| + n * |harm Lm| := by ring
  rw [e4]
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan

noncomputable section

local notation "Tc" k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ))

variable {S : CapSource}

/-! ### Uniform bounds for the row and column fields -/

theorem trial_bound {u : ℕ → ℝ} {K : ℝ} (hu : ∀ k, k ≠ 0 → |u k| ≤ K / k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |barrierTrialT u x| ≤ M ∧ |barrierTrialS u x| ≤ M := by
  have hs := (summable_of_moment_bound hu).1
  refine ⟨∑' n, |u (n + 1)| / ((n + 1 : ℕ) : ℝ), tsum_nonneg fun n => by positivity,
    fun x hx => ⟨?_, ?_⟩⟩
  · rw [barrierTrialT_eq, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hs.hasSum fun n => ?_
    have hT : |(Tc (n + 1)).eval x| ≤ 1 :=
      Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx)
    unfold termT
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
    gcongr
    calc |u (n + 1)| * |(Tc (n + 1)).eval x| ≤ |u (n + 1)| * 1 := by gcongr
      _ = _ := mul_one _
  · rw [barrierTrialS_eq, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded hs.hasSum fun n => ?_
    have hT : |x ^ (n + 1)| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
    unfold termS
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast]
    gcongr
    calc |u (n + 1)| * |x ^ (n + 1)| ≤ |u (n + 1)| * 1 := by gcongr
      _ = _ := mul_one _

/-- The gas part of a row field is bounded above on the punctured interval. -/
theorem gas_row_bounded {L : List YCell} (hL : ∀ c ∈ L, RowCell c) :
    ∃ M : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      physL L (fun u => Real.log |u|) + potL L (x + 1 / x) + massL L * Real.log |x| ≤ M := by
  obtain ⟨K, -, hK⟩ := row_moment_bound hL
  obtain ⟨M1, h1, b1⟩ := trial_bound (u := rowT L) (fun k hk => (hK k hk).1)
  obtain ⟨M2, h2, b2⟩ := trial_bound (u := rowB L) (fun k hk => (hK k hk).2)
  refine ⟨|massL L * Real.log 2| + 2 * M1 + M2, fun x hx hx0 => ?_⟩
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hT := (termT_summable (u := rowT L) (fun k hk => (hK k hk).1) hxI).hasSum
  have hS := (termS_summable (u := rowB L) (fun k hk => (hK k hk).2) hxI).hasSum
  rw [← barrierTrialT_eq] at hT
  rw [← barrierTrialS_eq] at hS
  have hsum := (hT.mul_left 2).add hS
  have he := hsum.unique (list_row_series hL hx hx0)
  have a1 := abs_le.mp (b1 x hxI).1
  have a2 := abs_le.mp (b2 x hxI).2
  have a3 := neg_abs_le (massL L * Real.log 2)
  linarith [a1.1, a2.1]

/-- The total size of the auxiliary kernel. -/
def coefSum (S : CapSource) : ℝ := ∑' k : ℕ, |cubeK S (k + 1)|

theorem coef_abs_le (k : ℕ) : |S.coef (k + 1)| ≤ |cubeK S (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have : S.coef (k + 1) = -(cubeK S (k + 1) / ((k + 1 : ℕ) : ℝ)) := rfl
  rw [this, abs_neg, abs_div, abs_of_pos (by linarith : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
  exact div_le_self (abs_nonneg _) hk

theorem coefSum_nonneg : 0 ≤ coefSum S := tsum_nonneg fun _ => abs_nonneg _

/-- The kernel series is bounded by `coefSum` on the closed disc. -/
theorem kernel_series_bound (hε : 0 < S.eps) {τ : ℝ} (hτ : |τ| ≤ 1) (ph : ℝ) :
    |Trunc.exact.sum (fun k => S.coef k * τ ^ k * Real.cos (k * ph))| ≤ coefSum S := by
  change |∑' k : ℕ, S.coef (k + 1) * τ ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * ph)| ≤ _
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (cubeK_summable hε).hasSum fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  have h1 := coef_abs_le (S := S) k
  have h2 : |τ| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  have h3 := Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * ph)
  calc _ ≤ |cubeK S (k + 1)| * 1 * 1 := by gcongr
    _ = _ := by ring

theorem psi_abs_le {r x : ℝ} (hr : 0 < r) (hx : |x| ≤ 1) :
    |CapSource.psi r x| ≤ 1 := by
  unfold CapSource.psi
  split_ifs with h
  · rw [abs_div, abs_of_pos hr]
    have hx0 : 0 < |x| := lt_trans hr h
    rw [div_le_one hx0]
    exact h.le
  · rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact not_lt.mp h

theorem radialA_bounded (hS : S.Admissible) (σ : Sign) {x : ℝ} (hx : |x| ≤ 1) :
    S.radialA Trunc.exact σ x ≤ 2 * coefSum S * S.auxMass σ := by
  have hε := hS.eps_pos
  have hc := coefSum_nonneg (S := S)
  unfold CapSource.radialA CapSource.auxMass
  have key : ∀ e ∈ S.aux σ, e.w * (Real.log (max |x| (S.rad e.rad)) +
      Trunc.exact.sum (fun k => S.coef k * (CapSource.psi (S.rad e.rad) x) ^ k * Real.cos (k * e.phase)) +
      (if σ = Sign.neg then
        Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
       else 0)) ≤ e.w * (2 * coefSum S) := by
    intro e _
    have hr := rad_pos S e.rad
    have hr1 := rad_le_one hS e.rad
    refine mul_le_mul_of_nonneg_left ?_ e.w_nonneg
    have h1 : Real.log (max |x| (S.rad e.rad)) ≤ 0 :=
      Real.log_nonpos (le_trans hr.le (le_max_right _ _)) (max_le hx hr1)
    have h2 := (abs_le.mp (kernel_series_bound hε (psi_abs_le hr hx) e.phase)).2
    have h3 : (if σ = Sign.neg then
        Trunc.exact.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
        else 0) ≤ coefSum S := by
      split_ifs
      · refine (abs_le.mp (kernel_series_bound hε ?_ e.phase)).2
        rw [abs_mul, abs_of_pos hr]
        calc S.rad e.rad * |x| ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1
      · exact hc
    linarith
  refine (List.sum_le_sum key).trans (le_of_eq ?_)
  rw [List.sum_map_mul_right]
  ring

theorem reflPoly_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ≤ 1 → |S.reflPoly x| ≤ M := by
  refine ⟨∑ k ∈ Finset.range (S.reflDeg + 1), |S.reflMoment (k + 1)| / ((k : ℝ) + 1),
    Finset.sum_nonneg fun k _ => by positivity, fun x hx => ?_⟩
  unfold CapSource.reflPoly
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hk]
  have h2 : |x| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  gcongr
  calc _ ≤ |S.reflMoment (k + 1)| * 1 := by gcongr
    _ = _ := mul_one _

/-! ### Row fields in anchor form -/

/-- The anchor mass. -/
def aB (S : CapSource) (a : Fin 2) : ℝ := massL (S.refRow a)
/-- The anchor row moments. -/
def aT (S : CapSource) (a : Fin 2) : ℕ → ℝ := rowT (S.refRow a)
/-- The anchor cross moments `B - 2C`. -/
def aV (S : CapSource) (a : Fin 2) : ℕ → ℝ := anchorV (S.refRow a) (S.refCol a)

theorem anchor_mass (hS : S.Admissible) (a : Fin 2) :
    massL (S.refRow a) = massL (S.refCol a) := by
  fin_cases a
  · change massL (S.refRow 0) = massL (S.refCol 0)
    rw [hS.ref_row_mass0, hS.ref_col_mass0]
  · change massL (S.refRow 1) = massL (S.refCol 1)
    rw [hS.ref_row_mass1, hS.ref_col_mass1]

theorem gas_cell (hS : S.Admissible) (σ : Sign) : ∀ c ∈ S.gas σ, RowCell c := by
  intro c hc
  cases σ
  · exact Or.inr (hS.gas_neg c hc)
  · exact Or.inl (hS.gas_pos c hc)

theorem ref_cell (hS : S.Admissible) (a : Fin 2) : ∀ c ∈ S.refRow a, RowCell c :=
  fun c hc => hS.ref_away a c hc

variable (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)

include hcol in
theorem anchor_free (hS : S.Admissible) (a : Fin 2) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hx0 : x ≠ 0) :
    physL (S.refRow a) (fun u => Real.log |u|) + potL (S.refRow a) (x + 1 / x) -
      potL ((S.refCol a).map YCell.dil2) (x + 1 / x) =
      anchorRowField (aB S a) (aT S a) (aV S a) x :=
  anchor_row_identity (ref_cell hS a) (hcol a) (anchor_mass hS a) hx hx0

/-- The free row field written through the anchor field. -/
theorem free_decomp (σ : Sign) (a : Fin 2) (x : ℝ) :
    S.rowField Trunc.exact σ Flavor.free (some a) x =
      (physL (S.refRow a) (fun u => Real.log |u|) + potL (S.refRow a) (x + 1 / x) -
        potL ((S.refCol a).map YCell.dil2) (x + 1 / x)) +
      (physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x|) - kappa σ +
      11 / 29 * Real.log |x| - 39 / 29 * Real.log (1 + x ^ 2) + 3 / 29 * Real.log (1 - x) +
      (if σ = Sign.pos then S.reflPoly x + S.reflTail else 0) + S.radialA Trunc.exact σ x := by
  simp only [CapSource.rowField, CapSource.refR, CapSource.refC, Flavor.free, CapSource.auxTail]
  ring

/-- The marked row field. -/
theorem ord_decomp (σ : Sign) (x : ℝ) :
    S.ordField Trunc.exact σ x =
      (physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x|) - kappa σ - 53 / 58 * Real.log (1 + x ^ 2) +
      (if σ = Sign.pos then S.reflPoly x + S.reflTail else 0) + S.radialA Trunc.exact σ x := by
  simp only [CapSource.ordField, CapSource.rowField, CapSource.refR, CapSource.refC, Flavor.marked,
    CapSource.auxTail, physL, potL, List.map_nil, List.sum_nil]
  ring

include hcol in
/-- The free row field minus its endpoint logarithms is bounded above. -/
theorem free_row_bounded (hS : S.Admissible) (a : Fin 2) :
    ∃ H : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ H := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound (ref_cell hS a) (hcol a)
  obtain ⟨M1, h1, b1⟩ := trial_bound (u := aT S a) (fun k hk => (hK k hk).1)
  obtain ⟨M2, h2, b2⟩ := trial_bound (u := aV S a) (fun k hk => (hK k hk).2)
  have hg : ∀ σ, ∃ M : ℝ, ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x| ≤ M := fun σ => gas_row_bounded (gas_cell hS σ)
  choose Mg hMg using hg
  obtain ⟨Mr, hr0, hMr⟩ := reflPoly_bounded (S := S)
  refine ⟨|aB S a * Real.log 2| + 2 * M1 + M2 + (|Mg Sign.pos| + |Mg Sign.neg|) +
    (|kappa Sign.pos| + |kappa Sign.neg|) + (Mr + |S.reflTail|) +
    (|2 * coefSum S * S.auxMass Sign.pos| + |2 * coefSum S * S.auxMass Sign.neg|),
    fun x hx hx0 => ?_⟩
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hq : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
  have ha : anchorRowField (aB S a) (aT S a) (aV S a) x ≤ |aB S a * Real.log 2| + 2 * M1 + M2 := by
    unfold anchorRowField
    have a1 := abs_le.mp (b1 x hxI).1
    have a2 := abs_le.mp (b2 x hxI).2
    have a3 := neg_abs_le (aB S a * Real.log 2)
    linarith [a1.1, a2.1]
  have hA := anchor_free hcol hS a hx hx0
  have n1 := abs_nonneg (Mg Sign.pos)
  have n2 := abs_nonneg (Mg Sign.neg)
  have n3 := abs_nonneg (kappa Sign.pos)
  have n4 := abs_nonneg (kappa Sign.neg)
  have n5 := abs_nonneg (2 * coefSum S * S.auxMass Sign.pos)
  have n6 := abs_nonneg (2 * coefSum S * S.auxMass Sign.neg)
  have n7 := abs_nonneg S.reflTail
  unfold CapSource.freeRow
  rw [free_decomp, hA]
  cases hσ : signOf x with
  | neg =>
    rw [if_neg (by intro h; cases h)]
    have g1 := hMg Sign.neg x hx hx0
    have g2 := radialA_bounded hS Sign.neg hxa
    have g3 := le_abs_self (Mg Sign.neg)
    have g4 := neg_abs_le (kappa Sign.neg)
    have g5 := le_abs_self (2 * coefSum S * S.auxMass Sign.neg)
    linarith
  | pos =>
    rw [if_pos rfl]
    have g1 := hMg Sign.pos x hx hx0
    have g2 := radialA_bounded hS Sign.pos hxa
    have g3 := le_abs_self (Mg Sign.pos)
    have g4 := neg_abs_le (kappa Sign.pos)
    have g5 := le_abs_self (2 * coefSum S * S.auxMass Sign.pos)
    have g6 := (abs_le.mp (hMr x hxa)).2
    have g7 := le_abs_self S.reflTail
    linarith

include hcol in
theorem col_anchor (hS : S.Admissible) (a : Fin 2) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    S.colField a s = anchorColumnField (aB S a) (aV S a) s + 9 / 58 * Real.log s +
      3 / 58 * Real.log (1 - s) := by
  have h := anchor_col_identity (ref_cell hS a) (hcol a) (s := s) ⟨by linarith [hs.1], hs.2.le⟩
  unfold CapSource.colField anchorColumnField
  rw [h, ← anchor_mass hS a]
  rfl

include hcol in
theorem free_col_bounded (hS : S.Admissible) (a : Fin 2) :
    ∃ H : ℝ, ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s - 3 / 58 * Real.log (1 - s) ≤ H := by
  obtain ⟨K, -, hK⟩ := anchor_moment_bound (ref_cell hS a) (hcol a)
  obtain ⟨M2, h2, b2⟩ := trial_bound (u := aV S a) (fun k hk => (hK k hk).2)
  refine ⟨|2 * aB S a * Real.log 2| + 2 * M2, fun s hs => ?_⟩
  rw [col_anchor hcol hS a hs]
  unfold anchorColumnField
  have a2 := abs_le.mp (b2 s ⟨by linarith [hs.1], hs.2.le⟩).1
  have a3 := neg_abs_le (2 * aB S a * Real.log 2)
  have a4 : Real.log s ≤ 0 := Real.log_nonpos hs.1.le hs.2.le
  linarith [a2.2]

/-! ### Endpoint transfer -/

theorem row_transfer {F c H t v n : ℝ} (hn : 29 / 6 ≤ n) (hF : F ≤ c)
    (hH : F - 3 / 29 * Real.log t - 6 / 29 * Real.log v ≤ H) :
    n * F - 1 / 2 * Real.log t - Real.log v ≤ n * c + 29 / 6 * (H - c) := by
  have e : n * F - 1 / 2 * Real.log t - Real.log v =
      (n - 29 / 6) * F + 29 / 6 * (F - 3 / 29 * Real.log t - 6 / 29 * Real.log v) := by ring
  have h1 : (n - 29 / 6) * F ≤ (n - 29 / 6) * c :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  rw [e]
  linarith

theorem col_transfer {F c H t n : ℝ} (hn : 58 / 3 ≤ n) (hF : F ≤ c)
    (hH : F - 3 / 58 * Real.log t ≤ H) :
    n * F - Real.log t ≤ n * c + 58 / 3 * (H - c) := by
  have e : n * F - Real.log t = (n - 58 / 3) * F + 58 / 3 * (F - 3 / 58 * Real.log t) := by ring
  have h1 : (n - 58 / 3) * F ≤ (n - 58 / 3) * c :=
    mul_le_mul_of_nonneg_left hF (by linarith)
  rw [e]
  linarith

/-! ### Row totals -/

section rows

variable {N D : ℕ}

theorem signOf_pos {x : ℝ} (hx : 0 < x) : signOf x = Sign.pos := by
  unfold signOf
  rw [if_neg (not_lt.mpr hx.le)]

theorem signOf_neg {x : ℝ} (hx : x < 0) : signOf x = Sign.neg := by
  unfold signOf
  rw [if_pos hx]

/-- The total of a free positive row. -/
theorem free_pos_row (hS : S.Admissible) (hD : D + 1 = 53 * N) (a : Fin 2) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hA : physL (S.refRow a) (fun u => Real.log |u|) +
      potL (S.refRow a) (x + 1 / x) - potL ((S.refCol a).map YCell.dil2) (x + 1 / x) =
      anchorRowField (aB S a) (aT S a) (aV S a) x) :
    (75 * (N : ℝ) - 1) * Real.log |x| + 6 * (N : ℝ) * Real.log (1 - x) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) (aT S a) (aV S a) x +
      pRow S (kappa Sign.pos) D N x ≤
    ((58 * N : ℕ) : ℝ) * S.freeRow Trunc.exact a x + 2 * Real.log (1 + x ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have h := qP_row hS hx
  unfold CapSource.freeRow
  rw [signOf_pos hx.1, free_decomp, hA, if_pos rfl]
  unfold pRow
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_nonneg hn0 (sub_nonneg.mpr h)
  rw [hDr]
  push_cast at this ⊢
  nlinarith [this]

/-- The total of a free negative row. -/
theorem free_neg_row (hS : S.Admissible) (hD : D + 1 = 53 * N) (a : Fin 2) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 0) (hA : physL (S.refRow a) (fun u => Real.log |u|) +
      potL (S.refRow a) (x + 1 / x) - potL ((S.refCol a).map YCell.dil2) (x + 1 / x) =
      anchorRowField (aB S a) (aT S a) (aV S a) x) :
    (75 * (N : ℝ) - 1) * Real.log |x| + 6 * (N : ℝ) * Real.log (1 - x) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) (aT S a) (aV S a) x +
      mRow S (kappa Sign.neg - 53 / 58 * Real.log 2 - cM S) N x =
    ((58 * N : ℕ) : ℝ) * S.freeRow Trunc.exact a x + 2 * Real.log (1 + x ^ 2) -
      Real.log |x| := by
  have hx0 : x ≠ 0 := hx.2.ne
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩
  have h := qM_row hS hx0 hxa
  unfold CapSource.freeRow
  rw [signOf_neg hx.2, free_decomp, hA, if_neg (by intro h; cases h)]
  unfold mRow
  rw [← one_div, h]
  push_cast
  ring

/-- The total of an unselected marked positive row. -/
theorem marked_pos_row (hS : S.Admissible) (hD : D + 1 = 53 * N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2)) +
      pRow S (kappa Sign.pos) D N y ≤
    (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * S.ordField Trunc.exact Sign.pos y +
      Real.log (1 + y ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have h := qP_row hS hy
  rw [ord_decomp, if_pos rfl]
  unfold pRow
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_nonneg hn0 (sub_nonneg.mpr h)
  rw [hDr]
  push_cast at this ⊢
  nlinarith [this]

/-- The total of a marked negative row. -/
theorem marked_neg_row (hS : S.Admissible) (hD : D + 1 = 53 * N) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 0) :
    (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2)) +
      mRow S (kappa Sign.neg - 53 / 58 * Real.log 2 - cM S) N y =
    (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * S.ordField Trunc.exact Sign.neg y -
      Real.log |y| + Real.log (1 + y ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have hy0 : y ≠ 0 := hy.2.ne
  have hya : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, by linarith [hy.2]⟩
  have h := qM_row hS hy0 hya
  rw [ord_decomp, if_neg (by intro h; cases h)]
  unfold mRow
  rw [← one_div, h, hDr]
  push_cast
  ring

/-- The total of a selected row. -/
theorem near_row (hS : S.Admissible) (hD : D + 1 = 53 * N) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2)) +
      pRow S (kappa Sign.pos) D N y⁻¹ ≤
    (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * S.nearField Trunc.exact y -
      2 * Real.log y + Real.log (1 + y ^ 2) := by
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have h := qP_near hS hy
  rw [one_div] at h
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_nonneg hn0 (sub_nonneg.mpr h)
  unfold pRow CapSource.nearField
  simp only [CapSource.auxTail]
  rw [abs_inv, Real.log_inv, abs_of_pos hy.1, hDr]
  push_cast at hm ⊢
  nlinarith [hm]

end rows

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

variable {S : CapSource}

/-- The shape of the family the cap sources are written for (GD4): `n = 58 N`, `b = 9 N`,
`q = 3 N`, `g = 5 N`, `h = 3 N` as fields of the parameter record.  The instance for the design
family lives in `RouteI.Family`. -/
class Shape58 (P : Parameters) : Prop where
  n0_eq : P.n0 = 58
  b0_eq : P.b0 = 9
  q0_eq : P.q0 = 3
  g0_eq : P.g0 = 5
  h0_eq : P.h0 = 3

namespace Shape58
variable {P : Parameters} [Shape58 P]

theorem n_eq (N : ℕ) : P.n N = 58 * N := by simp [Parameters.n, n0_eq]
theorem b_eq (N : ℕ) : P.b N = 9 * N := by simp [Parameters.b, b0_eq]
theorem q_eq (N : ℕ) : P.q N = 3 * N := by simp [Parameters.q, q0_eq]
theorem g_eq (N : ℕ) : P.g N = 5 * N := by simp [Parameters.g, g0_eq]
theorem h_eq (N : ℕ) : P.h N = 3 * N := by simp [Parameters.h, h0_eq]
theorem C_eq (N : ℕ) : P.C N = 75 * N := by
  simp only [Parameters.C, Parameters.L, n_eq, b_eq, q_eq, g_eq]; ring
theorem H_eq (N : ℕ) : P.H N = 78 * N := by
  simp only [Parameters.H, C_eq, h_eq]; ring
theorem A_eq (N : ℕ) : P.A N = 22 * N := by
  simp only [Parameters.A, b_eq, q_eq, g_eq]; ring
theorem adm : CatalanMeasure.Parametric.Admissible P := by
  unfold CatalanMeasure.Parametric.Admissible
  rw [n0_eq (P := P), b0_eq (P := P), q0_eq (P := P), g0_eq (P := P), h0_eq (P := P)]
  decide
end Shape58

variable {P : Parameters} [Shape58 P]

/-- The negative gas constant. -/
def cNeg (S : CapSource) : ℝ := kappa Sign.neg - 53 / 58 * Real.log 2 - cM S

/-- The scalar of a marked row. -/
def markScal (D : ℕ) (y : ℝ) : ℝ :=
  (D : ℝ) * (Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2))

/-- The fixed remainder of a marked row. -/
def markE : ℝ :=
  Real.log 2 - Real.log (19501 / 100000) - 2 * Real.log (98749 / 1000000)

theorem log_half_row {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.log (1 + x ^ 2) ≤ Real.log 2 := by
  refine Real.log_le_log (by positivity) ?_
  nlinarith [hx.1, hx.2]

section totals

variable {N D : ℕ}

theorem n_ge (hN : 0 < N) : (58 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  linarith

variable (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)

include hcol in
/-- The total of a free row at the moved anchor `(A, V)`, whose row field is the base anchor field
plus a bounded `fR` (GP Lemma 5.3, row part), with the fixed cap `c` of `F_R + fR`. -/
theorem free_total (hS : S.Admissible) (a : Fin 2) {c H : ℝ} {A V : ℕ → ℝ} {fR : ℝ → ℝ}
    (hcap : ∀ x ∈ CapSource.rowDom, S.freeRow Trunc.exact a x + fR x ≤ c)
    (hmv : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      anchorRowField (aB S a) A V x = anchorRowField (aB S a) (aT S a) (aV S a) x + fR x)
    (hH : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x + fR x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ H)
    (hN : 0 < N) (hD : D + 1 = 53 * N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    (75 * (N : ℝ) - 1) * Real.log |x| + 6 * (N : ℝ) * Real.log (1 - x) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) A V x -
      1 / 2 * Real.log (1 - x) +
      (if 0 ≤ x then pRow S (kappa Sign.pos) D N x else mRow S (cNeg S) N x) ≤
    ((58 * N : ℕ) : ℝ) * c + (29 / 6 * (H - c) + 2 * Real.log 2) := by
  have hn : (29 / 6 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := by
    have := n_ge hN
    linarith
  have hq := log_half_row hx
  have hA := anchor_free hcol hS a hx hx0
  have hlx : Real.log |x| ≤ 0 :=
    Real.log_nonpos (abs_nonneg _) (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  have hb := hH x hx hx0
  have hm := hmv x hx hx0
  rw [hm]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [if_neg (not_le.mpr hneg)]
    have e := free_neg_row hS hD a ⟨hx.1, hneg⟩ hA
    have hFc : S.freeRow Trunc.exact a x + fR x ≤ c := hcap x (Or.inl ⟨hx.1.le, hneg⟩)
    have t := row_transfer (t := 1 - x) (v := |x|) hn hFc (H := H) (by linarith)
    unfold cNeg
    linarith
  · rw [if_pos hpos.le]
    have e := free_pos_row hS hD a ⟨hpos, hx.2⟩ hA
    have hFc : S.freeRow Trunc.exact a x + fR x ≤ c := hcap x (Or.inr ⟨hpos, hx.2⟩)
    have t := row_transfer (t := 1 - x) (v := 1) hn hFc (H := H)
      (by rw [Real.log_one]; linarith)
    rw [Real.log_one] at t
    linarith

include hcol in
/-- The total of a free column at the moved anchor, with the column factor `γ log (1 + ζ s)`
(GP Lemma 5.3, column part and `log Z`). -/
theorem col_total (hS : S.Admissible) (a : Fin 2) {c H γ ζ : ℝ} {V : ℕ → ℝ} {fC : ℝ → ℝ}
    (hcap : ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s + fC s + γ * Real.log (1 + ζ * s) ≤ c)
    (hmv : ∀ s ∈ Ioo (0 : ℝ) 1,
      anchorColumnField (aB S a) V s = anchorColumnField (aB S a) (aV S a) s + fC s)
    (hH : ∀ s ∈ Ioo (0 : ℝ) 1,
      S.colField a s + fC s + γ * Real.log (1 + ζ * s) - 3 / 58 * Real.log (1 - s) ≤ H)
    (hN : 0 < N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    9 * (N : ℝ) * Real.log s + 3 * (N : ℝ) * Real.log (1 - s) +
      ((58 * N : ℕ) : ℝ) * anchorColumnField (aB S a) V s - Real.log (1 - s) +
      ((58 * N : ℕ) : ℝ) * (γ * Real.log (1 + ζ * s)) ≤
    ((58 * N : ℕ) : ℝ) * c + 58 / 3 * (H - c) := by
  have hn : (58 / 3 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := by
    have := n_ge hN
    linarith
  have t := col_transfer (t := 1 - s) hn (hcap s hs) (hH s hs)
  have e : ((58 * N : ℕ) : ℝ) * S.colField a s =
      9 * (N : ℝ) * Real.log s + 3 * (N : ℝ) * Real.log (1 - s) +
      ((58 * N : ℕ) : ℝ) * anchorColumnField (aB S a) (aV S a) s := by
    rw [col_anchor hcol hS a hs]
    push_cast
    ring
  rw [hmv s hs]
  linarith

/-- The total of a marked row, with the node correction `d` (GP Lemma 5.3, marks). -/
theorem mark_total (hS : S.Admissible) {M : ℝ} {d : ℝ → ℝ} {G : ℝ → Prop}
    (hp : S.OrdCap Trunc.exact Sign.pos d G M)
    (hm : S.OrdCap Trunc.exact Sign.neg d G M) (hnr : S.NearCap Trunc.exact d G M)
    (hD : D + 1 = 53 * N) {y g : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hGy : G y)
    (hdom : (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧ (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    (hg : (0 < y ∧ (g = pRow S (kappa Sign.pos) D N y ∨ g = pRow S (kappa Sign.pos) D N y⁻¹)) ∨
      (y < 0 ∧ g = mRow S (cNeg S) N y)) :
    markScal D y + g + ((58 * N : ℕ) : ℝ) * d y ≤
      (D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * M + markE := by
  have hn0 : (0 : ℝ) ≤ ((58 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hq := log_half_row hy
  have ha : Real.log (19501 / 100000) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hb : Real.log (98749 / 1000000) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  unfold markE markScal
  rcases hg with ⟨hy0, h | h⟩ | ⟨hy0, h⟩
  · have hd := hdom.1 hy0
    have e := marked_pos_row (N := N) hS hD (y := y) ⟨hy0, hy.2⟩
    have hc : S.ordField Trunc.exact Sign.pos y + d y ≤ M := by
      have := hp y hd (by simpa using hGy)
      simpa using this
    have := mul_le_mul_of_nonneg_left hc hn0
    rw [h]
    linarith
  · have hd := hdom.1 hy0
    have e := near_row (N := N) hS hD (y := y) ⟨hy0, hy.2⟩
    have hc := hnr y ⟨hy0, hy.2⟩ hGy
    have := mul_le_mul_of_nonneg_left hc hn0
    have hl : Real.log (98749 / 1000000) ≤ Real.log y := Real.log_le_log (by norm_num) hd.1
    rw [h]
    linarith
  · have hd := hdom.2 hy0
    have e := marked_neg_row (N := N) hS hD (y := y) ⟨hy.1, hy0⟩
    have hc : S.ordField Trunc.exact Sign.neg y + d y ≤ M := by
      have := hm (-y) hd (by simpa using hGy)
      simpa using this
    have := mul_le_mul_of_nonneg_left hc hn0
    have hl : Real.log (19501 / 100000) ≤ Real.log |y| := by
      refine Real.log_le_log (by norm_num) ?_
      rw [abs_of_neg hy0]
      exact hd.1
    unfold cNeg at *
    rw [h]
    linarith

end totals

/-! ### The scalar in logarithms -/

theorem log_abs_coord {y : ℝ} (hy0 : y ≠ 0) :
    Real.log |realCoordinateInv y| = Real.log 2 + Real.log |y| - Real.log (1 + y ^ 2) := by
  rw [abs_realCoordinateInv, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (abs_ne_zero.mpr hy0)]

theorem row_ratio {N D : ℕ} (hN : 0 < N) (hD : D + 1 = 53 * N) {y : ℝ}
    (hy : y ∈ Ioo (-1 : ℝ) 1) (hy0 : y ≠ 0) :
    Real.log (paramRowNodeWeight P N y) -
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv y)| = markScal D y := by
  have hR : realCoordinateInv y ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hy0) (by positivity)
  have h1 := one_sub_realCoordinateInv_pos hy
  have hRa : |realCoordinateInv y| ≠ 0 := abs_ne_zero.mpr hR
  have he : |(rowCommonFactor P N).eval (realCoordinateInv y)| =
      |realCoordinateInv y| ^ P.A N * (1 - realCoordinateInv y) ^ P.h N := by
    simp only [rowCommonFactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one, abs_mul, abs_pow, abs_of_pos h1]
  have hc : P.C N - 1 = P.A N + D := by
    rw [Shape58.C_eq, Shape58.A_eq]
    omega
  unfold paramRowNodeWeight
  rw [he, hc, Real.log_mul (pow_ne_zero _ hRa) (pow_ne_zero _ h1.ne'),
    Real.log_mul (pow_ne_zero _ hRa) (pow_ne_zero _ h1.ne'), Real.log_pow, Real.log_pow,
    Real.log_pow, log_abs_coord hy0]
  unfold markScal
  push_cast
  ring

theorem scalar_pos {N p m : ℕ} (hN : 0 < N) {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0 < selectedScalar P N x y s := by
  unfold selectedScalar
  have hR : ∀ j, realCoordinateInv (y j) ≠ 0 := fun j => by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
  refine div_pos (mul_pos (Finset.prod_pos fun j _ => paramRowNodeWeight_pos P N (hy j) (hy0 j))
    (paramPinPrincipal_pos (Shape58.adm (P := P)) hN x s hx hs hx0 hxi hsi))
    (Finset.prod_pos fun j _ => abs_pos.mpr ?_)
  simp only [rowCommonFactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  exact mul_ne_zero (pow_ne_zero _ (hR j)) (pow_ne_zero _ (one_sub_realCoordinateInv_pos (hy j)).ne')

theorem log_scalar {N D p m : ℕ} (hN : 0 < N) (hD : D + 1 = 53 * N) {x : Fin p → ℝ}
    {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (selectedScalar P N x y s) =
      ∑ j, markScal D (y j) + Real.log (paramPinPrincipal P N x s) := by
  have hR : ∀ j, realCoordinateInv (y j) ≠ 0 := fun j => by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
  have hw : ∀ j, paramRowNodeWeight P N (y j) ≠ 0 := fun j =>
    (paramRowNodeWeight_pos P N (hy j) (hy0 j)).ne'
  have he : ∀ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| ≠ 0 := fun j => by
    refine abs_ne_zero.mpr ?_
    simp only [rowCommonFactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_sub, Polynomial.eval_one]
    exact mul_ne_zero (pow_ne_zero _ (hR j))
      (pow_ne_zero _ (one_sub_realCoordinateInv_pos (hy j)).ne')
  have hp := paramPinPrincipal_pos (Shape58.adm (P := P)) hN x s hx hs hx0 hxi hsi
  unfold selectedScalar
  rw [Real.log_div (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hw j) hp.ne')
    (Finset.prod_ne_zero_iff.mpr fun j _ => he j),
    Real.log_mul (Finset.prod_ne_zero_iff.mpr fun j _ => hw j) hp.ne',
    Real.log_prod (fun j _ => hw j), Real.log_prod (fun j _ => he j)]
  have : ∑ j, markScal D (y j) = ∑ j, Real.log (paramRowNodeWeight P N (y j)) -
      ∑ j, Real.log |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (row_ratio hN hD (hy j) (hy0 j)).symm
  rw [this]
  ring

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

variable {S : CapSource} {P : Parameters} [Shape58 P]

/-! ### Final arithmetic -/

theorem final_arith {X L N α p m I Ic b r c M E1 E2 E3 C0 η εt κ κm cm Ep Em Tau Gas Gc target
    cost ε : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hp : p = 58 * N * (1 - α)) (hm : m = 58 * N * α) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1)
    (hX : X ≤ (p * (75 * N - 1) + p * (p - 1) / 2) * L +
      (58 * N) ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + εt) + p * (58 * N * r + E1) +
      p * (58 * N * c + E2) + m * ((53 * N - 1) * L + 58 * N * M + E3) +
      (2 * (58 * N) ^ 2 * κ + 2 * (53 * N) * (58 * N) * (κm - 53 / 58 * L - cm) +
        (53 * N - 1) * ((53 * N - 1) + 1) * L - N ^ 2 * Tau - (58 * N) ^ 2 * (Ep + Em)) / 2 +
      2 * (58 * N) ^ 2 * η + C0 * (58 * N) / 2)
    (hI : I ≤ Ic)
    (hGas : Gas = κ + 53 / 58 * (κm - cm) - (53 / 58) ^ 2 / 2 * L - (Ep + Em) / 2 -
      Tau / (2 * 58 ^ 2))
    (hG : Gas ≤ Gc)
    (hB : Ic - 3 / 2 * (1 - α - b) ^ 2 * L + (1 - α) * (r + c) + α * M +
      L * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) + Gc ≤
        -target + L / 2 + cost * α / 58)
    (hE : 58 * N * (|E1| + |E2| + |E3| + C0 / 2) ≤ (58 * N) ^ 2 * (ε / 2))
    (hεt : εt = ε / 4) (hη : η = ε / 8) :
    X ≤ (58 * N) ^ 2 * (-target + L / 2 + ε) + cost * N * m := by
  subst hp hm hGas hεt hη
  set A : ℝ := 58 * N with hA
  have hA0 : 0 < A := by positivity
  have key : ((A * (1 - α)) * (75 * N - 1) + (A * (1 - α)) * ((A * (1 - α)) - 1) / 2) * L +
      A ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + ε / 4) + (A * (1 - α)) * (A * r + E1) +
      (A * (1 - α)) * (A * c + E2) + (A * α) * ((53 * N - 1) * L + A * M + E3) +
      (2 * A ^ 2 * κ + 2 * (53 * N) * A * (κm - 53 / 58 * L - cm) +
        (53 * N - 1) * ((53 * N - 1) + 1) * L - N ^ 2 * Tau - A ^ 2 * (Ep + Em)) / 2 +
      2 * A ^ 2 * (ε / 8) + C0 * A / 2 =
      A ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + (1 - α) * (r + c) + α * M +
        L * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) +
        (κ + 53 / 58 * (κm - cm) - (53 / 58) ^ 2 / 2 * L - (Ep + Em) / 2 - Tau / (2 * 58 ^ 2))) +
      A ^ 2 * (ε / 2) + A * ((1 - α) * E1 + (1 - α) * E2 + α * E3 + C0 / 2) +
      L * (-(3 / 2) * (A * (1 - α)) - A * α - 53 * N / 2) := by
    rw [hA]
    ring
  rw [key] at hX
  have h1 : A ^ 2 * (I - 3 / 2 * (1 - α - b) ^ 2 * L + (1 - α) * (r + c) + α * M +
      L * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) +
      (κ + 53 / 58 * (κm - cm) - (53 / 58) ^ 2 / 2 * L - (Ep + Em) / 2 - Tau / (2 * 58 ^ 2))) ≤
      A ^ 2 * (-target + L / 2 + cost * α / 58) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hb1 : ∀ t e : ℝ, 0 ≤ t → t ≤ 1 → t * e ≤ |e| := fun t e h0 h1 => by
    have a1 : t * e ≤ t * |e| := mul_le_mul_of_nonneg_left (le_abs_self e) h0
    have a2 : t * |e| ≤ 1 * |e| := mul_le_mul_of_nonneg_right h1 (abs_nonneg e)
    linarith
  have hE' : A * ((1 - α) * E1 + (1 - α) * E2 + α * E3 + C0 / 2) ≤
      A * (|E1| + |E2| + |E3| + C0 / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0.le
    have := hb1 (1 - α) E1 (by linarith) (by linarith)
    have := hb1 (1 - α) E2 (by linarith) (by linarith)
    have := hb1 α E3 hα0 hα1
    linarith
  have h3 : L * (-(3 / 2) * (A * (1 - α)) - A * α - 53 * N / 2) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos hL ?_
    have a1 : 0 ≤ A * (1 - α) := mul_nonneg hA0.le (by linarith)
    have a2 : 0 ≤ A * α := mul_nonneg hA0.le hα0
    linarith
  have e : A ^ 2 * (-target + L / 2 + ε) + cost * N * (A * α) =
      A ^ 2 * (-target + L / 2 + cost * α / 58) + A ^ 2 * (ε / 2) + A ^ 2 * (ε / 2) := by
    rw [hA]
    ring
  rw [e]
  linarith

theorem tangent_scale {n P I SR SC LX LS ε : ℝ} (hn : 0 < n)
    (h : P ≤ I + SR / n + SC / n - LX / (2 * n ^ 2) - LS / n ^ 2 + ε) :
    n ^ 2 * P ≤ n ^ 2 * (I + ε) + n * SR + n * SC - LX / 2 - LS := by
  have h2 := mul_le_mul_of_nonneg_left h (sq_nonneg n)
  refine h2.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### Rows of the configuration -/

theorem gasRow_free (κ c : ℝ) (D N : ℕ) {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (sel : Fin (p + m) → Bool) (i : Fin p) :
    gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.castAdd m i) =
      if 0 ≤ x i then pRow S κ D N (x i) else mRow S c N (x i) := by
  unfold gasRow
  have h : Fin.castAdd m i ∉ selectedRows x y sel := by
    simp [selectedRows]
  rw [if_neg h, Fin.append_left]

theorem gasRow_mark (κ c : ℝ) (D N : ℕ) {p m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (sel : Fin (p + m) → Bool) (j : Fin m) (hy0 : y j ≠ 0) :
    (0 < y j ∧ (gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.natAdd p j) =
        pRow S κ D N (y j) ∨
      gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.natAdd p j) =
        pRow S κ D N (y j)⁻¹)) ∨
    (y j < 0 ∧ gasRow S κ c D N (Fin.append x y) (selectedRows x y sel) (Fin.natAdd p j) =
      mRow S c N (y j)) := by
  by_cases h : Fin.natAdd p j ∈ selectedRows x y sel
  · have h2 := (Finset.mem_filter.mp h).2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.append_right] at h2
    refine Or.inl ⟨lt_of_le_of_ne h2.2 hy0.symm, Or.inr ?_⟩
    simp only [gasRow, if_pos h, Fin.append_right]
  · by_cases h2 : 0 ≤ y j
    · refine Or.inl ⟨lt_of_le_of_ne h2 hy0.symm, Or.inl ?_⟩
      simp only [gasRow, if_neg h, Fin.append_right, if_pos h2]
    · refine Or.inr ⟨not_le.mp h2, ?_⟩
      simp only [gasRow, if_neg h, Fin.append_right, if_neg h2]

/-- The master inequality on an index type of the right size. -/
theorem gas_master' (hS : S.Admissible) (hF : FoldSeed S) {κp κm : ℝ}
    (hp : S.AngCap Trunc.exact Sign.pos κp) (hm : S.AngCap Trunc.exact Sign.neg κm)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N D n' : ℕ), 0 < N → D + 1 = 53 * N → n' = 58 * N →
      ∀ (z : Fin n' → ℝ) (T : Finset (Fin n')), (∀ i, z i ≠ 0) →
      (comparisonLaurent (5 * N) z T).det ≠ 0 →
      2 * Real.log |(comparisonLaurent (5 * N) z T).det| ≤
        2 * ∑ i, gasRow S κp (κm - 53 / 58 * Real.log 2 - cM S) D N z T i +
        gasK S κp (κm - 53 / 58 * Real.log 2 - cM S) D N +
        4 * ((58 * N : ℕ) : ℝ) ^ 2 * η + C * ((58 * N : ℕ) : ℝ) := by
  obtain ⟨C, hC, H⟩ := gas_master hS hF hp hm hη
  refine ⟨C, hC, fun N D n' hN hD hn z T hz hdet => ?_⟩
  subst hn
  exact H N D hN hD z T hz hdet

set_option maxHeartbeats 800000 in
/-- The whole logarithmic estimate for one configuration at one moved anchor `(A, V)` (GP Lemma
5.3).  The left side carries `log Z` (`Z = (∏ (1 + ζ s))^m`, bounded through the column field
`γ log (1 + ζ s)` with `m ≤ γ n`) and the node correction `58 N ∑ d(y_j)`; the right side has the
moved caps `r`, `c`, the moved intercept `anchorIntercept b A V` and the marks cap `M` (with `d`). -/
theorem config_bound (hS : S.Admissible) (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c) (a : Fin 2)
    {A V : ℕ → ℝ} {fR fC : ℝ → ℝ} {d : ℝ → ℝ} {G : ℝ → Prop} {γ ζ : ℝ}
    {r c M Hr Hc C0 η εt α : ℝ} {N D p m : ℕ} (hN : 0 < N) (hD : D + 1 = 53 * N)
    (hζ : 0 ≤ ζ) (hγ : (m : ℝ) ≤ 58 * (N : ℝ) * γ)
    (hmR : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      anchorRowField (aB S a) A V x = anchorRowField (aB S a) (aT S a) (aV S a) x + fR x)
    (hmC : ∀ s ∈ Ioo (0 : ℝ) 1,
      anchorColumnField (aB S a) V s = anchorColumnField (aB S a) (aV S a) s + fC s)
    (hrc : ∀ x ∈ CapSource.rowDom, S.freeRow Trunc.exact a x + fR x ≤ r)
    (hcc : ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s + fC s + γ * Real.log (1 + ζ * s) ≤ c)
    (hop : S.OrdCap Trunc.exact Sign.pos d G M) (hom : S.OrdCap Trunc.exact Sign.neg d G M)
    (hnr : S.NearCap Trunc.exact d G M)
    (hHr : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x + fR x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ Hr)
    (hHc : ∀ s ∈ Ioo (0 : ℝ) 1,
      S.colField a s + fC s + γ * Real.log (1 + ζ * s) - 3 / 58 * Real.log (1 - s) ≤ Hc)
    (hp58 : (p : ℝ) = 58 * (N : ℝ) * (1 - α))
    {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) (hyG : ∀ j, G (y j))
    (hdom : ∀ j, (0 < y j → y j ∈ CapSource.ordDom Sign.pos) ∧
      (y j < 0 → -y j ∈ CapSource.ordDom Sign.neg))
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hxi : Function.Injective x) (hsi : Function.Injective s)
    (sel : Fin (p + m) → Bool)
    (htan : pinOffDiagonalInteraction (58 * (N : ℝ)) 1 x s ≤
      anchorIntercept (aB S a) A V -
        (3 / 2 : ℝ) * ((p : ℝ) / (58 * (N : ℝ)) - aB S a) ^ 2 * Real.log 2 +
        (∑ i, anchorRowField (aB S a) A V (x i)) / (58 * (N : ℝ)) +
        (∑ j, anchorColumnField (aB S a) V (s j)) / (58 * (N : ℝ)) -
        (∑ i, Real.log (1 - x i)) / (2 * (58 * (N : ℝ)) ^ 2) -
        (∑ j, Real.log (1 - s j)) / (58 * (N : ℝ)) ^ 2 + εt)
    {dt : ℝ}
    (hgm : 2 * dt ≤
      2 * ∑ i, gasRow S (kappa Sign.pos) (cNeg S) D N (Fin.append x y) (selectedRows x y sel) i +
        gasK S (kappa Sign.pos) (cNeg S) D N + 4 * ((58 * N : ℕ) : ℝ) ^ 2 * η +
        C0 * ((58 * N : ℕ) : ℝ)) :
    Real.log (selectedScalar P N x y s) + dt + (m : ℝ) * (∑ i, Real.log (1 + ζ * s i)) +
        ((58 * N : ℕ) : ℝ) * ∑ j, d (y j) ≤
      ((p : ℝ) * (75 * (N : ℝ) - 1) + (p : ℝ) * ((p : ℝ) - 1) / 2) * Real.log 2 +
      (58 * (N : ℝ)) ^ 2 * (anchorIntercept (aB S a) A V -
        3 / 2 * (1 - α - aB S a) ^ 2 * Real.log 2 + εt) +
      (p : ℝ) * (58 * (N : ℝ) * r + (29 / 6 * (Hr - r) + 2 * Real.log 2)) +
      (p : ℝ) * (58 * (N : ℝ) * c + 58 / 3 * (Hc - c)) +
      (m : ℝ) * ((53 * (N : ℝ) - 1) * Real.log 2 + 58 * (N : ℝ) * M + markE) +
      (2 * (58 * (N : ℝ)) ^ 2 * kappa Sign.pos +
        2 * (53 * (N : ℝ)) * (58 * (N : ℝ)) *
          (kappa Sign.neg - 53 / 58 * Real.log 2 - cM S) +
        (53 * (N : ℝ) - 1) * ((53 * (N : ℝ) - 1) + 1) * Real.log 2 - (N : ℝ) ^ 2 * tauInt S -
        (58 * (N : ℝ)) ^ 2 * (planarEnergy (qP S) + planarEnergy (qM S))) / 2 +
      2 * (58 * (N : ℝ)) ^ 2 * η + C0 * (58 * (N : ℝ)) / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : 1 ≤ N := hN
  have hn0 : (0 : ℝ) < 58 * (N : ℝ) := by positivity
  have hDr : (D : ℝ) = 53 * (N : ℝ) - 1 := by
    have : ((D + 1 : ℕ) : ℝ) = ((53 * N : ℕ) : ℝ) := by rw [hD]
    push_cast at this
    linarith
  have hl1 := log_scalar (P := P) hN hD hx hx0 hy hy0 hs hxi hsi
  have hl2 := log_paramPinPrincipal (Shape58.adm (P := P)) hN x s hx hs hx0 hxi hsi
  have c1 : ((P.C N - 1 : ℕ) : ℝ) = 75 * (N : ℝ) - 1 := by
    rw [Shape58.C_eq, Nat.cast_sub (by omega)]
    push_cast
    ring
  have c2 : ((2 * P.h N : ℕ) : ℝ) = 6 * (N : ℝ) := by
    rw [Shape58.h_eq]
    push_cast
    ring
  have c3 : ((P.H N - 2 : ℕ) : ℝ) = 78 * (N : ℝ) - 2 := by
    rw [Shape58.H_eq, Nat.cast_sub (by omega)]
    push_cast
    ring
  have c4 : ((P.b N : ℕ) : ℝ) = 9 * (N : ℝ) := by
    rw [Shape58.b_eq]
    push_cast
    ring
  have c5 : ((P.q N : ℕ) : ℝ) = 3 * (N : ℝ) := by
    rw [Shape58.q_eq]
    push_cast
    ring
  have c6 : ((p * (P.C N - 1) + p.choose 2 : ℕ) : ℝ) =
      (p : ℝ) * (75 * (N : ℝ) - 1) + (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    rw [Nat.cast_add, Nat.cast_mul, c1, Nat.cast_choose_two]
  rw [c6, c4, c5, c1, c2, c3] at hl2
  -- the tangent, scaled
  have hfrac : (p : ℝ) / (58 * (N : ℝ)) = 1 - α := by
    rw [hp58]
    field_simp
  rw [hfrac] at htan
  have hts := tangent_scale hn0 htan
  have hpin : (58 * (N : ℝ)) ^ 2 * pinOffDiagonalInteraction (58 * (N : ℝ)) 1 x s =
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log (1 - x i * x j)) +
      2 * (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |s j - s i|) -
      (∑ i, ∑ j, Real.log (1 - 2 * x i * s j + x i ^ 2)) := by
    unfold pinOffDiagonalInteraction
    field_simp
  rw [hpin] at hts
  -- the rows
  have hrow : ∑ i, ((75 * (N : ℝ) - 1) * Real.log |x i| + 6 * (N : ℝ) * Real.log (1 - x i) -
      (78 * (N : ℝ) - 2) * Real.log (1 + x i ^ 2) +
      ((58 * N : ℕ) : ℝ) * anchorRowField (aB S a) A V (x i) -
      1 / 2 * Real.log (1 - x i) +
      (if 0 ≤ x i then pRow S (kappa Sign.pos) D N (x i) else mRow S (cNeg S) N (x i))) ≤
      ∑ _i : Fin p, (((58 * N : ℕ) : ℝ) * r + (29 / 6 * (Hr - r) + 2 * Real.log 2)) :=
    Finset.sum_le_sum fun i _ => free_total hcol hS a hrc hmR hHr hN hD (hx i) (hx0 i)
  have hcolS : ∑ j, (9 * (N : ℝ) * Real.log (s j) + 3 * (N : ℝ) * Real.log (1 - s j) +
      ((58 * N : ℕ) : ℝ) * anchorColumnField (aB S a) V (s j) - Real.log (1 - s j) +
      ((58 * N : ℕ) : ℝ) * (γ * Real.log (1 + ζ * s j))) ≤
      ∑ _j : Fin p, (((58 * N : ℕ) : ℝ) * c + 58 / 3 * (Hc - c)) :=
    Finset.sum_le_sum fun j _ => col_total hcol hS a hcc hmC hHc hN (hs j)
  have hmark : ∑ j, (markScal D (y j) + gasRow S (kappa Sign.pos) (cNeg S) D N (Fin.append x y)
      (selectedRows x y sel) (Fin.natAdd p j) + ((58 * N : ℕ) : ℝ) * d (y j)) ≤
      ∑ _j : Fin m, ((D : ℝ) * Real.log 2 + ((58 * N : ℕ) : ℝ) * M + markE) :=
    Finset.sum_le_sum fun j _ => mark_total hS hop hom hnr hD (hy j) (hyG j) (hdom j)
      (gasRow_mark _ _ D N x y sel j (hy0 j))
  -- log Z against the column field
  have hg0 : ∀ i, 0 ≤ Real.log (1 + ζ * s i) := fun i =>
    Real.log_nonneg (by have := mul_nonneg hζ (hs i).1.le; linarith)
  have hZ : (m : ℝ) * (∑ i, Real.log (1 + ζ * s i)) ≤
      58 * (N : ℝ) * (γ * ∑ i, Real.log (1 + ζ * s i)) := by
    calc (m : ℝ) * (∑ i, Real.log (1 + ζ * s i)) ≤
        (58 * (N : ℝ) * γ) * ∑ i, Real.log (1 + ζ * s i) :=
          mul_le_mul_of_nonneg_right hγ (Finset.sum_nonneg fun i _ => hg0 i)
      _ = _ := by ring
  have hsplit := Fin.sum_univ_add (fun i => gasRow S (kappa Sign.pos) (cNeg S) D N
    (Fin.append x y) (selectedRows x y sel) i)
  simp only [gasRow_free] at hsplit
  rw [hsplit] at hgm
  unfold gasK at hgm
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hrow hcolS hmark hl2
  rw [hDr] at hgm hmark
  unfold cNeg at hgm hrow hmark
  push_cast at hrow hcolS hmark hgm ⊢
  linarith [hZ]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas




namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open Finset MeasureTheory Filter Set
open scoped BigOperators
open CapFields YCell OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.PhysicalPick CatalanMeasure.Parametric

noncomputable section

variable {S : CapSource} {P : Parameters} [Shape58 P]

/-- The common cap of the marked rows. -/
def markCap {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ} {anchI : Fin 2 → ℝ}
    (B : S.CapBundle Trunc.exact d G gasI anchI) : ℝ :=
  max (max (B.ordCap Sign.pos) (B.ordCap Sign.neg)) B.nearCap

/-- The explicit constant of the completed gas: the angular constants, the fold constant, the two
planar energies and the Legendre integral. -/
def gasConst (S : CapSource) : ℝ :=
  kappa Sign.pos + 53 / 58 * (kappa Sign.neg - cM S) - (53 / 58) ^ 2 / 2 * Real.log 2 -
    (planarEnergy (qP S) + planarEnergy (qM S)) / 2 - tauInt S / (2 * 58 ^ 2)

/-- The budget at a moved anchor with base mass `b`, intercept cap `I`, row cap `r`, column cap
`c` and marked fraction `α`, retaining the mass square (GP §11.1: the three values are
arguments). -/
def capBudget {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ} {anchI : Fin 2 → ℝ}
    (B : S.CapBundle Trunc.exact d G gasI anchI) (b I r c α : ℝ) : ℝ :=
  I - 3 / 2 * (1 - α - b) ^ 2 * Real.log 2 +
    (1 - α) * (r + c) + α * markCap B +
    Real.log 2 * (75 / 58 * (1 - α) + (1 - α) ^ 2 / 2 + 53 / 58 * α) + B.gasICap

/-- **The comparison bound on the near sheet, one cell.**  The anchor is the moved anchor `(A, V)`
of the cell (`anchorRowField` and `anchorColumnField` are the base fields plus the bounded `fR`,
`fC`), the caps are the cell's `r`, `c`, `I` with the column factor `γ log (1 + ζ s)` (`γ` at least
the marked fractions of the window `W`), and `d = δ ∘ t / 58` is the node correction.  The cutoff is
chosen before the configuration and the selector; the Pick window is not used. -/
theorem selected_comparison (hS : S.Admissible) (hF : FoldSeed S)
    (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)
    {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ} {anchI : Fin 2 → ℝ}
    (B : S.CapBundle Trunc.exact d G gasI anchI)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ)
    (hgas : gasConst S ≤ gasI)
    (a : Fin 2) {A V : ℕ → ℝ} {fR fC : ℝ → ℝ} {K : ℝ}
    (hA : ∀ k, k ≠ 0 → |A k| ≤ K / k) (hV : ∀ k, k ≠ 0 → |V k| ≤ K / k)
    (hmR : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      anchorRowField (aB S a) A V x = anchorRowField (aB S a) (aT S a) (aV S a) x + fR x)
    (hmC : ∀ s ∈ Ioo (0 : ℝ) 1,
      anchorColumnField (aB S a) V s = anchorColumnField (aB S a) (aV S a) s + fC s)
    (hfR : ∃ Bf, ∀ x ∈ Ioo (-1 : ℝ) 1, |fR x| ≤ Bf)
    (hfC : ∃ Bf, ∀ s ∈ Ioo (0 : ℝ) 1, |fC s| ≤ Bf)
    {r c I γ ζ : ℝ} (hζ : 0 ≤ ζ) (hγ0 : 0 ≤ γ)
    (hrc : ∀ x ∈ CapSource.rowDom, S.freeRow Trunc.exact a x + fR x ≤ r)
    (hcc : ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s + fC s + γ * Real.log (1 + ζ * s) ≤ c)
    (hI : anchorIntercept (aB S a) A V ≤ I)
    {target cost : ℝ} {W : Set ℝ} (hWγ : ∀ α ∈ W, α ≤ γ)
    (hbud : ∀ α ∈ W, capBudget B (aB S a) I r c α ≤ -target + Real.log 2 / 2 + cost * α / 58)
    {δ : ℝ → ℝ} (hdδ : ∀ u, d u = δ (realCoordinateInv u) / 58)
    (hG : ∀ y, G y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧
      (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ W) :
    SelectedComparisonOnPick P ζ δ target cost G Q := by
  intro ε hε
  have hAp : S.AngCap Trunc.exact Sign.pos (kappa Sign.pos) := fun i hi θ =>
    (B.ang Sign.pos i hi θ).trans (hang _)
  have hAm : S.AngCap Trunc.exact Sign.neg (kappa Sign.neg) := fun i hi θ =>
    (B.ang Sign.neg i hi θ).trans (hang _)
  obtain ⟨C0, hC0, hgm⟩ := gas_master' hS hF hAp hAm (η := ε / 8) (by positivity)
  obtain ⟨ν, hν0, hν⟩ : ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν₀ ≤ ν → ∀ (p : ℕ), (p : ℝ) ≤ ν →
      ∀ (x s : Fin p → ℝ), (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      Function.Injective x → Function.Injective s →
      pinOffDiagonalInteraction ν 1 x s ≤
        anchorIntercept (aB S a) A V -
          (3 / 2 : ℝ) * ((p : ℝ) / ν - aB S a) ^ 2 * Real.log 2 +
          (∑ i, anchorRowField (aB S a) A V (x i)) / ν +
          (∑ j, anchorColumnField (aB S a) V (s j)) / ν -
          (∑ i, Real.log (1 - x i)) / (2 * ν ^ 2) - (∑ j, Real.log (1 - s j)) / ν ^ 2 + ε / 4 := by
    have h1 := summable_of_moment_bound (u := A) (C := K) hA
    have h2 := summable_of_moment_bound (u := V) (C := K) hV
    exact free_pin_anchor_tangent (aB S a) A V h1.1 h2.1 h1.2 h2.2 (ε := ε / 4) (by positivity)
  obtain ⟨Hr0, hHr0⟩ := free_row_bounded hcol hS a
  obtain ⟨Hc0, hHc0⟩ := free_col_bounded hcol hS a
  obtain ⟨Bf, hBf⟩ := hfR
  obtain ⟨Bc, hBc⟩ := hfC
  set Hr : ℝ := Hr0 + Bf with hHrdef
  set Hc : ℝ := Hc0 + Bc + γ * Real.log (1 + ζ) with hHcdef
  have hHr : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      S.freeRow Trunc.exact a x + fR x - 3 / 29 * Real.log (1 - x) - 11 / 29 * Real.log |x| ≤ Hr :=
    fun x hx hx0 => by
      have h1 := hHr0 x hx hx0
      have h2 := (le_abs_self (fR x)).trans (hBf x hx)
      rw [hHrdef]
      linarith
  have hHc : ∀ s ∈ Ioo (0 : ℝ) 1,
      S.colField a s + fC s + γ * Real.log (1 + ζ * s) - 3 / 58 * Real.log (1 - s) ≤ Hc :=
    fun s hs => by
      have h1 := hHc0 s hs
      have h2 := (le_abs_self (fC s)).trans (hBc s hs)
      have h3 : Real.log (1 + ζ * s) ≤ Real.log (1 + ζ) :=
        Real.log_le_log (by have := mul_nonneg hζ hs.1.le; linarith)
          (by have := mul_le_mul_of_nonneg_left hs.2.le hζ; linarith)
      have h4 := mul_le_mul_of_nonneg_left h3 hγ0
      rw [hHcdef]
      linarith
  set M := markCap B with hMdef
  have hop : S.OrdCap Trunc.exact Sign.pos d G M := fun s hs hGs =>
    (B.ord Sign.pos s hs hGs).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hom : S.OrdCap Trunc.exact Sign.neg d G M := fun s hs hGs =>
    (B.ord Sign.neg s hs hGs).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hnr : S.NearCap Trunc.exact d G M := fun y hy hGy =>
    (B.near y hy hGy).trans (le_max_right _ _)
  set Et : ℝ := |29 / 6 * (Hr - r) + 2 * Real.log 2| +
    |58 / 3 * (Hc - c)| + |markE| + C0 / 2 with hEt
  have hEt0 : 0 ≤ Et := by
    simp only [hEt]
    positivity
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈ν⌉₊,
    eventually_ge_atTop ⌈Et * 2 / ε⌉₊] with N hN1 hNa hNE
  intro p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hQc sel _
  have hn58 : ∀ M : ℕ, P.n M = 58 * M := fun M => Shape58.n_eq (P := P) M
  have hpm' : p + m = 58 * N := by rw [← hn58]; exact hpm
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  obtain ⟨D, hD⟩ : ∃ D, D + 1 = 53 * N := ⟨53 * N - 1, by omega⟩
  have hn0 : (0 : ℝ) < 58 * (N : ℝ) := by positivity
  have hpmr : (p : ℝ) + m = 58 * (N : ℝ) := by
    have : ((p + m : ℕ) : ℝ) = ((58 * N : ℕ) : ℝ) := by rw [hpm']
    push_cast at this
    exact this
  set α : ℝ := (m : ℝ) / (58 * (N : ℝ)) with hα
  have hm' : (m : ℝ) = 58 * (N : ℝ) * α := by
    rw [hα]
    field_simp
  have hp' : (p : ℝ) = 58 * (N : ℝ) * (1 - α) := by
    rw [mul_sub, mul_one, ← hm']
    linarith
  have hα0 : 0 ≤ α := by positivity
  have hα1 : α ≤ 1 := by
    rw [hα, div_le_one hn0]
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    linarith
  have hnR : ((P.n N : ℕ) : ℝ) = 58 * (N : ℝ) := by
    rw [hn58]
    push_cast
    ring
  have hαW : α ∈ W := by
    have h := hQ N p m x y s hQc
    rwa [hnR] at h
  have hmγ : (m : ℝ) ≤ 58 * (N : ℝ) * γ := by
    rw [hm']
    exact mul_le_mul_of_nonneg_left (hWγ α hαW) hn0.le
  have hxi : Function.Injective x := by
    intro i j h
    have h2 : Fin.append x y (Fin.castAdd m i) = Fin.append x y (Fin.castAdd m j) := by
      simpa using h
    exact Fin.castAdd_injective _ _ (hzi h2)
  have hz0 : ∀ i : Fin (p + m), Fin.append x y i ≠ 0 := fun i =>
    Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hdom : ∀ j, (0 < y j → y j ∈ CapSource.ordDom Sign.pos) ∧
      (y j < 0 → -y j ∈ CapSource.ordDom Sign.neg) := fun j => hG _ (hyG j)
  have hgN : P.g N = 5 * N := Shape58.g_eq (P := P) N
  rw [hgN]
  by_cases hdet : (comparisonLaurent (5 * N) (Fin.append x y) (selectedRows x y sel)).det = 0
  · rw [hdet, abs_zero, mul_zero, mul_zero]
    unfold selectedCap
    positivity
  have hpos := scalar_pos (P := P) hN hx hx0 hy hy0 hs hxi hsi
  have hg := hgm N D (p + m) hN hD hpm' (Fin.append x y) (selectedRows x y sel) hz0 hdet
  have hνa : ν ≤ 58 * (N : ℝ) := by
    have h0 : ν ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNa)
    linarith
  have hple : (p : ℝ) ≤ 58 * (N : ℝ) := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have htan := hν (58 * (N : ℝ)) hνa p hple x s hx hs hxi hsi
  have hcfg := config_bound (P := P) hS hcol a (A := A) (V := V) (fR := fR) (fC := fC) (d := d) (G := G)
    (γ := γ) (ζ := ζ) (r := r) (c := c) (M := M) (C0 := C0) (η := ε / 8) (εt := ε / 4)
    (α := α) hN hD hζ hmγ hmR hmC hrc hcc hop hom hnr hHr hHc hp'
    hx hx0 hy hy0 hyG hdom hs hxi hsi sel htan hg
  have hE : 58 * (N : ℝ) * (|29 / 6 * (Hr - r) + 2 * Real.log 2| +
      |58 / 3 * (Hc - c)| + |markE| + C0 / 2) ≤ (58 * (N : ℝ)) ^ 2 * (ε / 2) := by
    have h1 : Et * 2 / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNE)
    have h2 : Et ≤ (N : ℝ) * (ε / 2) := by
      rw [div_le_iff₀ hε] at h1
      linarith
    have h4 : Et ≤ 58 * (N : ℝ) * (ε / 2) := by
      have : (N : ℝ) * (ε / 2) ≤ 58 * (N : ℝ) * (ε / 2) := by
        have : 0 < (N : ℝ) * (ε / 2) := by positivity
        linarith
      linarith
    calc 58 * (N : ℝ) * Et ≤ 58 * (N : ℝ) * (58 * (N : ℝ) * (ε / 2)) :=
          mul_le_mul_of_nonneg_left h4 hn0.le
      _ = _ := by ring
  have hfin := final_arith
    (X := Real.log (selectedScalar P N x y s) +
      Real.log |(comparisonLaurent (5 * N) (Fin.append x y) (selectedRows x y sel)).det| +
      (m : ℝ) * (∑ i, Real.log (1 + ζ * s i)) + ((58 * N : ℕ) : ℝ) * ∑ j, d (y j))
    (L := Real.log 2) (N := (N : ℝ)) (α := α) (p := (p : ℝ)) (m := (m : ℝ))
    (I := anchorIntercept (aB S a) A V) (Ic := I) (b := aB S a)
    (r := r) (c := c) (M := M)
    (E1 := 29 / 6 * (Hr - r) + 2 * Real.log 2) (E2 := 58 / 3 * (Hc - c))
    (E3 := markE) (C0 := C0) (η := ε / 8) (εt := ε / 4) (κ := kappa Sign.pos)
    (κm := kappa Sign.neg) (cm := cM S) (Ep := planarEnergy (qP S))
    (Em := planarEnergy (qM S)) (Tau := tauInt S) (Gas := gasConst S) (Gc := B.gasICap)
    (target := target) (cost := cost) (ε := ε)
    hNr (Real.log_nonneg (by norm_num)) hp' hm' hα0 hα1 hcfg hI rfl
    (hgas.trans B.gasI_le) (hbud α hαW) hE rfl rfl
  -- back to the product
  have hZpos : 0 < (∏ l, (1 + ζ * s l)) ^ m :=
    pow_pos (prod_pos fun i _ => by have := mul_nonneg hζ (hs i).1.le; linarith) _
  have hZlog : Real.log ((∏ l, (1 + ζ * s l)) ^ m) = (m : ℝ) * ∑ i, Real.log (1 + ζ * s i) := by
    rw [Real.log_pow, Real.log_prod (fun i _ => by
      have := mul_nonneg hζ (hs i).1.le; exact (by linarith : (1 + ζ * s i) ≠ 0))]
  have habs : 0 < |(comparisonLaurent (5 * N) (Fin.append x y) (selectedRows x y sel)).det| :=
    abs_pos.mpr hdet
  have hprefix : (1 : ℝ) ≤ (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N :=
    one_le_pow₀ (by
      have : 0 ≤ 10 * Real.exp 12 * (P.n N : ℝ) := by positivity
      linarith)
  have hcast : ((P.n0 : ℝ) * N) = 58 * (N : ℝ) := by rw [Shape58.n0_eq (P := P)]; norm_num
  have hE' : ((58 * N : ℕ) : ℝ) * ∑ j, d (y j) = (N : ℝ) * ∑ j, δ (realCoordinateInv (y j)) := by
    simp only [hdδ, ← Finset.sum_div]
    push_cast
    ring
  unfold selectedCap
  rw [hcast, ← hE']
  calc (∏ l, (1 + ζ * s l)) ^ m * (selectedScalar P N x y s *
        |(comparisonLaurent (5 * N) (Fin.append x y) (selectedRows x y sel)).det|) =
      Real.exp (Real.log ((∏ l, (1 + ζ * s l)) ^ m) + Real.log (selectedScalar P N x y s) +
        Real.log |(comparisonLaurent (5 * N) (Fin.append x y) (selectedRows x y sel)).det|) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hZpos, Real.exp_log hpos,
          Real.exp_log habs, mul_assoc]
    _ ≤ Real.exp ((58 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m -
          ((58 * N : ℕ) : ℝ) * ∑ j, d (y j)) :=
        Real.exp_le_exp.mpr (by rw [hZlog]; linarith only [hfin])
    _ = 1 * Real.exp ((58 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + cost * N * m -
          ((58 * N : ℕ) : ℝ) * ∑ j, d (y j)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hprefix (Real.exp_pos _).le

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas





namespace CatalanMeasure.GenD.Signed.RouteI.CompletedGas

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Signed
open CatalanMeasure.Parametric OAI.InternalCatalan Set Finset Filter
open CatalanMeasure.GenD.Signed.PhysicalPick
open CapFields YCell
open scoped BigOperators Topology

noncomputable section

variable {S : CapSource} {P : Parameters} [Shape58 P]

theorem sum_append_split (φ : ℝ → ℝ) {p a b m : ℕ} (x : Fin p → ℝ) (y : Fin m → ℝ)
    (eq : Fin a ⊕ Fin b ≃ Fin m) :
    ∑ i : Fin (p + m), φ (Fin.append x y i) =
      (∑ i, φ (x i)) + (∑ i, φ (y (eq (Sum.inl i)))) + ∑ i, φ (y (eq (Sum.inr i))) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Equiv.sum_comp eq, Fintype.sum_sum_type, add_assoc]

theorem arctan_pair : Real.arctan 4 + Real.arctan (1 / 4) = Real.pi / 2 := by
  have h := Real.arctan_inv_of_pos (show (0 : ℝ) < 4 by norm_num)
  have h2 : (1 / 4 : ℝ) = 4⁻¹ := by norm_num
  rw [h2, h]
  ring

/-- The phase margin, per row, in the normalisation of `P`. -/
theorem phase_arith {ν Nr e R A1 A4 Cc ξ η Z αF L hc : ℝ}
    (hν : ν = 58 * Nr) (he : e = 48 * Nr - 1) (hpair : A4 + A1 = Real.pi / 2)
    (hA4 : A4 < Real.pi / 2) (hR : R = A1 + 5 / 29 * A4 + Cc)
    (hξ : 0 < ξ) (hNξ : 1 ≤ Nr * ξ) (hη : η = ξ / 4)
    (hph : R + ξ ≤ Z - αF - hc)
    (hL : ν * (Z - η) - ν * αF - ν * hc ≤ L) :
    ν * (Real.pi / 2) + Real.pi / 2 + ν * Cc - e * A4 < L := by
  have hν0 : 0 < ν := by
    have : 0 < Nr := by
      by_contra h
      nlinarith [not_lt.1 h]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hph hν0.le
  have hpi := Real.pi_lt_four
  have h2 : (4 : ℝ) < ν * (ξ * (3 / 4)) := by
    rw [hν]
    nlinarith
  subst hR hη he
  have h3 : ν * (Real.pi / 2) = ν * A4 + ν * A1 := by
    rw [← hpair]
    ring
  have h4 : 58 * Nr * A4 = ν * A4 := by rw [hν]
  rw [h3]
  nlinarith only [h1, h2, hL, hpi, hA4, h4]

/-- The one-point margin, per row, in the normalisation of `P`. -/
theorem onepoint_arith {ν Nr e α u2 sq η ξ Sf Sm Sn W B : ℝ} {p a b : ℝ}
    (hν : ν = 58 * Nr) (he : e = 48 * Nr - 1) (hξ : 0 < ξ) (hNξ : 1 ≤ Nr * ξ) (hη : η = ξ / 4)
    (hcount : p + a + b = ν) (hα : ν * α = a + b) (ha : 0 ≤ a)
    (hone : 1 - (1 - α + u2 - sq) / 2 + ξ ≤ 5 / 6 * (48 / 58))
    (hW : ν * (u2 - sq - η) ≤ W) (hWd : W = 2 * Sf - p + (2 * Sm - a) / 2)
    (hSm : 0 ≤ Sm) (hSn : 0 ≤ Sn) (hB : B ≤ (p - Sf) + (a - Sm) + (b - Sn)) :
    B ≤ 5 / 6 * e := by
  have hν0 : 0 < ν := by
    have : 0 < Nr := by
      by_contra h
      nlinarith [not_lt.1 h]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hone hν0.le
  have h2 : (5 / 6 : ℝ) < ν * (ξ * (3 / 4)) := by
    rw [hν]
    nlinarith
  subst hη he
  have h3 : 5 / 6 * (48 * Nr - 1) = ν * (5 / 6 * (48 / 58)) - 5 / 6 := by
    rw [hν]
    ring
  rw [h3]
  nlinarith only [h1, h2, hW, hWd, hSm, hSn, hB, hcount, hα, ha]

set_option maxHeartbeats 1600000 in
/-- **Low branch or physical Pick window on the selected sheet of `P`.**  The cutoff is chosen
in the order fixed test, fixed damping `e`, eventual `N`, and depends only on `ε`. -/
theorem selected_low_or_pick {W : Set ℝ} {γ ζ : ℝ} {dc : ℝ → ℝ}
    {t₀ residual nearCap c₀ target cost : ℝ} {G : ℝ → Prop} (hζ : 0 ≤ ζ)
    (hWγ : ∀ α ∈ W, α ≤ γ)
    (D : SecondTrialBoundsEnd P W
      (fun N u => populationEndpointColumnField P N 0 u + γ * Real.log (1 + ζ * u)) dc
      t₀ residual nearCap c₀ G) (T : PhaseTest)
    {δ : ℝ → ℝ} (hdδ : ∀ u, dc u = δ (realCoordinateInv u) / 58)
    {Δ : ℝ → ℝ} {ξ d : ℝ} (hξ : 0 < ξ) (hd : 0 < d)
    (hΔ : ∀ α ∈ W, ∀ β ∈ Icc 0 α,
      oldBound P D.normCap D.fieldCap residual nearCap α β ≤
        -target + Real.log 2 / 2 + cost / 58 * α + Δ α)
    (hphase : ∀ α ∈ W,
      Real.arctan (1 / 4) + 5 / 29 * Real.arctan 4 +
          (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) + ξ ≤
        T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * D.p (k + 1)) - Real.sqrt (T.H * (Δ α / 2)) -
          α * T.F 0 / 4 - T.h₀ * (Δ α / d))
    (hone : ∀ α ∈ W,
      1 - (1 - α + D.p 2 - Real.sqrt (2 * (Δ α / 2))) / 2 + ξ ≤ 5 / 6 * (48 / 58))
    (hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-T.a₀) 0, freeRowX P N D.p D.v x ≤ D.MX - d)
    (hGneg : ∀ y, G y → y < 0 → y ≤ -T.a₀)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ W)
    (hpick : ∀ {n : ℕ} (w : Fin n → ℝ) (e : ℕ), Function.Injective w → (∀ i, w i ≠ 0) →
      (∀ i, |w i| < 1) →
      ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2) ≤
        5 / 6 * (e : ℝ) →
      ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
          (17 / 4) * ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (1 / 100) ^ 2 /
            (1 - (1 / 100) ^ 2) <
        (e : ℝ) * Real.arctan 4 -
          ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
            Real.arctan (4 * ((1 - w i) / (1 + w i))) →
      PickWindow (1 / 100) e w) :
    SelectedLowOrPick P ζ δ target cost G Q := by
  intro ε hε
  have hη : 0 < ξ / 4 := by linarith only [hξ]
  set Cst : ℝ := 4 * (∑' j, |D.p j|) + 4 * (∑' j, |D.v j|) + |D.p 1| + 20 with hCst
  have hCpos : 0 < Cst := by
    have h1 : 0 ≤ ∑' j, |D.p j| := tsum_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ ∑' j, |D.v j| := tsum_nonneg fun _ => abs_nonneg _
    have h3 := abs_nonneg (D.p 1)
    rw [hCst]
    linarith only [h1, h2, h3]
  have he₁ : 0 < min (min (1 / 8 : ℝ) (ε / 2 / Cst)) (ξ / 8) :=
    lt_min (lt_min (by norm_num) (by positivity)) (by linarith only [hξ])
  obtain ⟨e, habel, he0⟩ := ((abel_eventually T.summable hη).and
    (Ioo_mem_nhdsGT he₁)).exists
  have he : e ∈ Ioo (0 : ℝ) (1 / 8) :=
    ⟨he0.1, he0.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hec : e * Cst < ε / 2 := by
    have : e < ε / 2 / Cst := he0.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    rwa [lt_div_iff₀ hCpos] at this
  have hη2 : 2 * e ≤ ξ / 4 := by
    have : e < ξ / 8 := he0.2.trans_le (min_le_right _ _)
    linarith only [this]
  have habel' : ∀ w ∈ Icc (-1 : ℝ) 1,
      |dampedT T.F (realEnergyTau e) w - dampedT T.F 1 w| ≤ ξ / 4 := habel
  filter_upwards [second_energy_sq_end (Shape58.adm (P := P)) D hε he hec, hsup,
    eventually_ge_atTop 48, eventually_ge_atTop ⌈1 / ξ⌉₊] with N henergy hsupN hN48 hNc
  intro p m hpm x y s hx hx0 hy hy0 hG hs hinj hsi hcase hq sel
  obtain ⟨a, b, hab, eq, hnear, hinj2, hyb, hsheet⟩ :=
    selected_sheet_grouped (Shape58.adm (P := P)) hN48 hpm x y s hx hx0 hy hy0 hs hinj hcase sel
  have hcount : p + a + b = P.n N := by omega
  have hxi : Function.Injective x := fun i j h => by
    have h2 := @hinj2 (Fin.castAdd a i) (Fin.castAdd a j) (by simpa using h)
    exact Fin.castAdd_injective _ _ h2
  have hya : ∀ i, y (eq (Sum.inl i)) ∈ Ioo (-1 : ℝ) 1 := fun i => hy _
  have hNpos : 0 < N := by omega
  obtain ⟨hE, hbr0, hXz⟩ := henergy p a b hcount x (fun i => y (eq (Sum.inl i)))
    (fun i => y (eq (Sum.inr i))) s hx hx0 hya (fun i => hG _) hnear (fun i => hG _) hs hxi hinj2 hyb hsi
  have hν : 0 < (P.n N : ℝ) := by exact_mod_cast n_pos (Shape58.adm (P := P)) hNpos
  have hνN : (P.n N : ℝ) = 58 * (N : ℝ) := by
    rw [Shape58.n_eq (P := P)]
    push_cast
    ring
  have hcR : (p : ℝ) + a + b = (P.n N : ℝ) := by exact_mod_cast hcount
  have habR : (a : ℝ) + b = m := by exact_mod_cast hab
  set α : ℝ := ((a + b : ℕ) : ℝ) / (P.n N : ℝ) with hαd
  set β : ℝ := (b : ℝ) / (P.n N : ℝ) with hβd
  have hαν : (P.n N : ℝ) * α = (a : ℝ) + b := by
    rw [hαd, Nat.cast_add]
    field_simp
  have hαm : α ∈ W := by
    have h := hQ N p m x y s hq
    rw [← hab] at h
    simpa [hαd] using h
  have hβm : β ∈ Icc 0 α := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hν.le, ?_⟩
    rw [hαd, hβd]
    refine div_le_div_of_nonneg_right ?_ hν.le
    exact_mod_cast (show b ≤ a + b by omega)
  by_cases hV : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
      (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + dc u)
      (fun u => groupedNearField P N u + dc u)
      (fun u => populationEndpointColumnField P N 0 u + α * Real.log (1 + ζ * u)) x
      (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s ≤
      -target + Real.log 2 / 2 + cost / 58 * α + ε
  · left
    have hl := low_of_value (Shape58.adm (P := P)) hNpos hcount hζ hx hx0 hya hnear hs
      (fun i j h => hxi h) hinj2 hyb hsi hV
    have hPr : 0 < ∏ i, (1 + s i) := Finset.prod_pos fun i _ => by linarith [(hs i).1]
    have hPm : 0 < (∏ i, (1 + s i)) ^ m := pow_pos hPr _
    have hK : 0 ≤ (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N := by positivity
    have hZ : 0 ≤ (∏ i, (1 + ζ * s i)) ^ m :=
      pow_nonneg (Finset.prod_nonneg fun i _ => by
        have := mul_nonneg hζ (hs i).1.le; linarith) _
    have hcost : (((P.n0 : ℕ) : ℝ) * (cost / 58)) * N * ((a : ℝ) + b) = cost * N * m := by
      rw [habR, Shape58.n0_eq (P := P)]
      push_cast
      ring
    have hEs : (P.n N : ℝ) * ((∑ i, dc (y (eq (Sum.inl i)))) + ∑ i, dc (y (eq (Sum.inr i)))) =
        (N : ℝ) * ∑ j, δ (realCoordinateInv (y j)) := by
      have h1 : ∑ j, dc (y j) =
          (∑ i, dc (y (eq (Sum.inl i)))) + ∑ i, dc (y (eq (Sum.inr i))) := by
        rw [← Equiv.sum_comp eq, Fintype.sum_sum_type]
      rw [← h1, hνN]
      simp only [hdδ, ← Finset.sum_div]
      ring
    rw [hcost, hEs, hab] at hl
    unfold selectedCap
    refine le_of_mul_le_mul_left ?_ hPm
    calc (∏ i, (1 + s i)) ^ m * ((∏ i, (1 + ζ * s i)) ^ m * (selectedScalar P N x y s *
          |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|))
        = (∏ i, (1 + ζ * s i)) ^ m * ((∏ i, (1 + s i)) ^ m * (selectedScalar P N x y s *
          |(selectedLaurent (P.g N) (Fin.append x y) (selectedRows x y sel)).det|)) := by ring
      _ ≤ (∏ i, (1 + ζ * s i)) ^ m * ((1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          groupedProduct P N x (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s) :=
        mul_le_mul_of_nonneg_left hsheet hZ
      _ = (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N * ((∏ i, (1 + ζ * s i)) ^ m *
          groupedProduct P N x (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s) := by
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl hK
      _ = _ := by ring
  · right
    have hlt := not_le.1 hV
    have hmono : groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + dc u)
        (fun u => groupedNearField P N u + dc u)
        (fun u => populationEndpointColumnField P N 0 u + α * Real.log (1 + ζ * u)) x
        (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s ≤
        groupedValueWithFields (P.n N : ℝ) (groupedConstant P N p a b)
        (populationPhysicalFreeField P N) (fun u => groupedMarkedField P N u + dc u)
        (fun u => groupedNearField P N u + dc u)
        (fun u => populationEndpointColumnField P N 0 u + γ * Real.log (1 + ζ * u)) x
        (fun i => y (eq (Sum.inl i))) (fun i => y (eq (Sum.inr i))) s := by
      unfold groupedValueWithFields
      have hsum : ∑ i, (populationEndpointColumnField P N 0 (s i) + α * Real.log (1 + ζ * s i)) ≤
          ∑ i, (populationEndpointColumnField P N 0 (s i) + γ * Real.log (1 + ζ * s i)) :=
        Finset.sum_le_sum fun i _ => by
          have hg0 : 0 ≤ Real.log (1 + ζ * s i) :=
            Real.log_nonneg (by have := mul_nonneg hζ (hs i).1.le; linarith)
          have := mul_le_mul_of_nonneg_right (hWγ α hαm) hg0
          linarith
      have := div_le_div_of_nonneg_right hsum hν.le
      linarith
    have hOB := hΔ α hαm β hβm
    have hsqs : ∀ i, y (eq (Sum.inr i)) ∈ Ioo (-1 : ℝ) 1 := fun i => hy _
    have hzx := append_mem hx hya
    have hcos := (cosineSquares_nonneg hν he hzx hsqs D.p D.p_summable).2
    have hq1 := sqTail_nonneg D.p (pinCosineMoment (P.n N : ℝ) e x)
    have hq2 := sqTail_nonneg D.v (fun j => pinPowerMoment (P.n N : ℝ) e x j -
      2 * pinColumnMoment (P.n N : ℝ) e s j)
    have hsplit : groupedSquares (P.n N : ℝ) e D.p D.p D.v (Fin.append x
        (fun i => y (eq (Sum.inl i)))) (fun i => y (eq (Sum.inr i))) x s =
      cosineSquares (P.n N : ℝ) e D.p (Fin.append x (fun i => y (eq (Sum.inl i))))
          (fun i => y (eq (Sum.inr i))) +
        (sqTail D.p (pinCosineMoment (P.n N : ℝ) e x) +
          sqTail D.v (fun j => pinPowerMoment (P.n N : ℝ) e x j -
            2 * pinColumnMoment (P.n N : ℝ) e s j) / 2) := rfl
    rw [hsplit] at hE
    have hΔ2 : sqTail D.p (pinCosineMoment (P.n N : ℝ) e x) +
        cosineSquares (P.n N : ℝ) e D.p (Fin.append x (fun i => y (eq (Sum.inl i))))
          (fun i => y (eq (Sum.inr i))) ≤ Δ α := by
      linarith only [hE, hlt, hmono, hOB, hbr0, hq2]
    have hbrΔ : bracketSlack (P.n N : ℝ) (D.MX + ε / 4)
        (fun i => freeRowX P N D.p D.v (x i)) ≤ Δ α := by
      linarith only [hE, hlt, hmono, hOB, hcos, hq1, hq2]
    have hcard := card_mul_le_bracket hν (fun i => freeRowX P N D.p D.v (x i))
      (Finset.univ.filter (fun i => x i ∈ Ioo (-T.a₀) 0)) (cap := D.MX + ε / 4) (d := d) hXz
      (fun i hi => by
        have h1 := hsupN (x i) (Finset.mem_filter.mp hi).2
        linarith only [h1, hε])
    have hc : ((Finset.univ.filter (fun i => x i ∈ Ioo (-T.a₀) 0)).card : ℝ) ≤
        (P.n N : ℝ) * (Δ α / d) := by
      rw [← mul_div_assoc, le_div_iff₀ hd]
      exact hcard.trans (mul_le_mul_of_nonneg_left hbrΔ hν.le)
    have hlow := phase_sum_lower T hν he habel' hcR hx hx0 hya (fun i => hy0 _)
      (fun i h => hGneg _ (hG _) h) hnear D.p D.p_summable hΔ2 hc
    have hone' := onepoint_lower hν he hη2 hcR hx hya hsqs D.p D.p_summable hΔ2
    have hNξ : 1 ≤ (N : ℝ) * ξ := by
      have h1 : 1 / ξ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNc)
      rwa [div_le_iff₀ hξ] at h1
    have hg : P.g N = 5 * N := Shape58.g_eq (P := P) N
    have hn : P.n N = 58 * N := Shape58.n_eq (P := P) N
    have heN : ((p + m - 1 - 2 * P.g N : ℕ) : ℝ) = 48 * (N : ℝ) - 1 := by
      have h : (p + m - 1 - 2 * P.g N) + 1 = 48 * N := by
        rw [hg]
        omega
      have h2 : (((p + m - 1 - 2 * P.g N : ℕ) : ℝ)) + 1 = 48 * (N : ℝ) := by exact_mod_cast h
      linarith only [h2]
    have hpm' : ((p + m : ℕ) : ℝ) = (P.n N : ℝ) := by exact_mod_cast hpm
    have hw0 : ∀ i, Fin.append x y i ≠ 0 := fun i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using hx0 j
      · simpa using hy0 j
    have hwm := append_mem hx hy
    refine hpick _ _ hinj hw0 (fun i => abs_lt.mpr (hwm i)) ?_ ?_
    · have h1 := onepoint_le hwm
      have h2 := sum_append_split (fun t => 1 - t ^ 2) x y eq
      rw [h2] at h1
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, ← Finset.mul_sum] at h1 hone'
      have hSm : 0 ≤ ∑ i, y (eq (Sum.inl i)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hSn : 0 ≤ ∑ i, y (eq (Sum.inr i)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [heN]
      exact onepoint_arith (hνN) rfl hξ hNξ rfl hcR hαν (Nat.cast_nonneg _) (hone α hαm) hone'
        rfl hSm hSn (by linarith only [h1])
    · refine hstat_of_sum hw0 _ ?_
      rw [sum_append_split phasePlus x y eq, heN, hpm']
      have hA4 : Real.arctan 4 < Real.pi / 2 := Real.arctan_lt_pi_div_two 4
      have hL : (P.n N : ℝ) * (T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * D.p (k + 1)) -
            Real.sqrt (T.H * (Δ α / 2)) - ξ / 4) - (P.n N : ℝ) * (α * T.F 0 / 4) -
            (P.n N : ℝ) * (T.h₀ * (Δ α / d)) ≤
          (∑ i, phasePlus (x i)) + (∑ i, phasePlus (y (eq (Sum.inl i)))) +
            ∑ i, phasePlus (y (eq (Sum.inr i))) := by
        have h1 : (P.n N : ℝ) * (α * T.F 0 / 4) = ((a : ℝ) + b) * T.F 0 / 4 := by
          rw [← hαν]
          ring
        rw [h1]
        linarith only [hlow]
      have := phase_arith (Cc := (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2))
        hνN rfl arctan_pair hA4 rfl hξ hNξ rfl (hphase α hαm) hL
      have hC : (17 / 4) * (P.n N : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) =
          (P.n N : ℝ) * ((17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2)) := by ring
      rw [hC]
      exact this

/-- **The selected free-product cost for `P`, one cell:** the exact consumer of `Wrappers`, with the
column factor `Z` and the node field `δ`. -/
theorem selected_free_product (hS : S.Admissible) (hF : FoldSeed S)
    (hcol : ∀ a, ∀ c ∈ S.refCol a, ColCell c)
    {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ} {anchI : Fin 2 → ℝ}
    (B : S.CapBundle Trunc.exact d G gasI anchI)
    (hang : ∀ σ, B.angCap σ ≤ kappa σ) (hgas : gasConst S ≤ gasI)
    (a : Fin 2) {A V : ℕ → ℝ} {fR fC : ℝ → ℝ} {K : ℝ}
    (hA : ∀ k, k ≠ 0 → |A k| ≤ K / k) (hV : ∀ k, k ≠ 0 → |V k| ≤ K / k)
    (hmR : ∀ x ∈ Ioo (-1 : ℝ) 1, x ≠ 0 →
      anchorRowField (aB S a) A V x = anchorRowField (aB S a) (aT S a) (aV S a) x + fR x)
    (hmC : ∀ s ∈ Ioo (0 : ℝ) 1,
      anchorColumnField (aB S a) V s = anchorColumnField (aB S a) (aV S a) s + fC s)
    (hfR : ∃ Bf, ∀ x ∈ Ioo (-1 : ℝ) 1, |fR x| ≤ Bf)
    (hfC : ∃ Bf, ∀ s ∈ Ioo (0 : ℝ) 1, |fC s| ≤ Bf)
    {r c I γ ζ : ℝ} (hζ : 0 ≤ ζ) (hγ0 : 0 ≤ γ)
    (hrc : ∀ x ∈ CapSource.rowDom, S.freeRow Trunc.exact a x + fR x ≤ r)
    (hcc : ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s + fC s + γ * Real.log (1 + ζ * s) ≤ c)
    (hI : anchorIntercept (aB S a) A V ≤ I)
    {target cost : ℝ} {W : Set ℝ} (hWγ : ∀ α ∈ W, α ≤ γ)
    (hbud : ∀ α ∈ W, capBudget B (aB S a) I r c α ≤ -target + Real.log 2 / 2 + cost * α / 58)
    {δ : ℝ → ℝ} (hdδ : ∀ u, d u = δ (realCoordinateInv u) / 58)
    (hG : ∀ y, G y → (0 < y → y ∈ CapSource.ordDom Sign.pos) ∧
      (y < 0 → -y ∈ CapSource.ordDom Sign.neg))
    {t₀ residual nearCap c₀ : ℝ}
    (D : SecondTrialBoundsEnd P W
      (fun N u => populationEndpointColumnField P N 0 u + γ * Real.log (1 + ζ * u)) d
      t₀ residual nearCap c₀ G) (T : PhaseTest)
    {Δ : ℝ → ℝ} {ξ dm : ℝ} (hξ : 0 < ξ) (hdm : 0 < dm)
    (hΔ : ∀ α ∈ W, ∀ β ∈ Icc 0 α,
      oldBound P D.normCap D.fieldCap residual nearCap α β ≤
        -target + Real.log 2 / 2 + cost / 58 * α + Δ α)
    (hphase : ∀ α ∈ W,
      Real.arctan (1 / 4) + 5 / 29 * Real.arctan 4 +
          (17 / 4) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) + ξ ≤
        T.F 0 / 2 + (∑' k : ℕ, T.F (k + 1) * D.p (k + 1)) - Real.sqrt (T.H * (Δ α / 2)) -
          α * T.F 0 / 4 - T.h₀ * (Δ α / dm))
    (hone : ∀ α ∈ W,
      1 - (1 - α + D.p 2 - Real.sqrt (2 * (Δ α / 2))) / 2 + ξ ≤ 5 / 6 * (48 / 58))
    (hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-T.a₀) 0, freeRowX P N D.p D.v x ≤ D.MX - dm)
    (hGneg : ∀ y, G y → y < 0 → y ≤ -T.a₀)
    {Q : ∀ (N p m : ℕ), (Fin p → ℝ) → (Fin m → ℝ) → (Fin p → ℝ) → Prop}
    (hQ : ∀ N p m x y s, Q N p m x y s → ((m : ℝ) / (P.n N : ℝ)) ∈ W)
    (hpick : ∀ {n : ℕ} (w : Fin n → ℝ) (e : ℕ), Function.Injective w → (∀ i, w i ≠ 0) →
      (∀ i, |w i| < 1) →
      ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), (1 - w i ^ 2) / (1 + w i ^ 2) ≤
        5 / 6 * (e : ℝ) →
      ((Finset.univ.filter (fun i => w i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
          (17 / 4) * ((Finset.univ.filter (fun i => 0 < w i)).card : ℝ) * (1 / 100) ^ 2 /
            (1 - (1 / 100) ^ 2) <
        (e : ℝ) * Real.arctan 4 -
          ∑ i ∈ Finset.univ.filter (fun i => 0 < w i),
            Real.arctan (4 * ((1 - w i) / (1 + w i))) →
      PickWindow (1 / 100) e w) :
    SelectedFreeProductCostOnRestr P ζ δ target cost G Q :=
  selectedFree_of_lowOrPick (Shape58.adm (P := P)) hζ
    (selected_low_or_pick hζ hWγ D T hdδ hξ hdm hΔ hphase hone hsup hGneg hQ hpick)
    (selected_comparison hS hF hcol B hang hgas a hA hV hmR hmC hfR hfC hζ hγ0 hrc hcc hI
      hWγ hbud hdδ hG hQ)

/-! ### GP Lemma 5.4: convexity in place of subadditivity (chords)

The moved row field `F + h⁰ + τ h¹` and the moved column field `F + k⁰ + τ k¹ + γ g` are affine in
`τ` (resp. in `γ`); two (resp. three) endpoint caps therefore bound them along the whole segment by
the chord. -/

/-- Rows: `(R0)` and `(R1)` give `(R)` at every `τ ∈ [0, 1]` with the chord cap. -/
theorem chord_row {F h0 h1 c0 c1 τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (R0 : F + h0 ≤ c0) (R1 : F + h0 + h1 ≤ c1) :
    F + (h0 + τ * h1) ≤ (1 - τ) * c0 + τ * c1 := by
  nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr R1), mul_nonneg (sub_nonneg.mpr hτ1) (sub_nonneg.mpr R0)]

/-- Columns, first chord: `(C0)` and `(C1)` give `(C)` at `(τ, γ = τ α_e)` with the chord cap. -/
theorem chord_col {F k0 k1 g c0 c1 ae τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (C0 : F + k0 ≤ c0) (C1 : F + k0 + k1 + ae * g ≤ c1) :
    F + (k0 + τ * k1) + (τ * ae) * g ≤ (1 - τ) * c0 + τ * c1 := by
  nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr C1), mul_nonneg (sub_nonneg.mpr hτ1) (sub_nonneg.mpr C0)]

/-- Columns, second chord: at `τ = 1` and `γ ∈ [α_e, α₁]` the field is affine in `γ`, so `(C1)`
and `(C2)` bound it by the chord of `c₁`, `c₂` at `γ`. -/
theorem chord_col_gamma {F g c1 c2 ae a1 γ : ℝ} (hae : ae < a1) (hγ0 : ae ≤ γ) (hγ1 : γ ≤ a1)
    (C1 : F + ae * g ≤ c1) (C2 : F + a1 * g ≤ c2) :
    F + γ * g ≤ ((a1 - γ) * c1 + (γ - ae) * c2) / (a1 - ae) := by
  have hd : 0 < a1 - ae := sub_pos.mpr hae
  rw [le_div_iff₀ hd]
  nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) (sub_nonneg.mpr C1),
    mul_nonneg (sub_nonneg.mpr hγ0) (sub_nonneg.mpr C2)]

end
end CatalanMeasure.GenD.Signed.RouteI.CompletedGas


#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.config_bound
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.free_total
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.col_total
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.mark_total
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.selected_comparison
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.selected_low_or_pick
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.selected_free_product
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.anchorIntercept_move
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.chord_row
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.chord_col
#print axioms CatalanMeasure.GenD.Signed.RouteI.CompletedGas.chord_col_gamma
