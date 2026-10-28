module
public import CatalanCore.Uniform.Decay.Nodes.Regular
public import CatalanCore.Uniform.Decay.Nodes.FreePotential
@[expose] public section

/-!
# Variation and size of the regularised interval potential

For `0 ≤ lo ≤ hi ≤ b`: `|kapInt lo hi x| ≤ (hi - lo) (1/2) log (1 + b²)` on `[0, b]`, `kapInt` is
unimodal (increasing up to the midpoint, decreasing after), hence
`∫_0^b |kapD| ≤ 4 (hi - lo) (1/2) log (1 + b²)`; and `kapInt ≥ exact potential - 6`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset MeasureTheory Set intervalIntegral

noncomputable def kapD (lo hi x : ℝ) : ℝ :=
  -(1 / 2) * (Real.log (1 + (x - lo) ^ 2) - Real.log (1 + (x - hi) ^ 2))

theorem hasDerivAt_kapInt (lo hi x : ℝ) : HasDerivAt (kapInt lo hi) (kapD lo hi x) x := by
  have h1 := (hasDerivAt_Gk (x - lo)).comp x ((hasDerivAt_id x).sub_const lo)
  have h2 := (hasDerivAt_Gk (x - hi)).comp x ((hasDerivAt_id x).sub_const hi)
  have h3 := (h1.sub h2).const_mul (-(1 / 2))
  unfold kapInt kapD
  simpa [Function.comp_def] using h3

theorem continuous_kapInt (lo hi : ℝ) : Continuous (kapInt lo hi) := by
  unfold kapInt
  exact continuous_const.mul ((continuous_Gk.comp (continuous_id.sub continuous_const)).sub
    (continuous_Gk.comp (continuous_id.sub continuous_const)))

theorem continuous_kapD (lo hi : ℝ) : Continuous (kapD lo hi) := by
  unfold kapD
  have : ∀ c : ℝ, Continuous fun x : ℝ => Real.log (1 + (x - c) ^ 2) := fun c =>
    Continuous.log (by fun_prop) (fun x => by positivity)
  exact continuous_const.mul ((this lo).sub (this hi))

theorem abs_kapInt_le {lo hi b x : ℝ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhb : hi ≤ b)
    (hx : x ∈ Icc 0 b) : |kapInt lo hi x| ≤ (hi - lo) * ((1 / 2) * Real.log (1 + b ^ 2)) := by
  rw [← integral_kap]
  have hb : 0 ≤ b := hlo.trans (hlh.trans hhb)
  have hnorm : ∀ y ∈ Set.uIoc lo hi, ‖kap x y‖ ≤ (1 / 2) * Real.log (1 + b ^ 2) := by
    intro y hy
    rw [Set.uIoc_of_le hlh] at hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have hyb : y ≤ b := by linarith [hy.2]
    have hsq : (x - y) ^ 2 ≤ b ^ 2 := by
      have : |x - y| ≤ b := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      calc (x - y) ^ 2 = |x - y| ^ 2 := (sq_abs _).symm
        _ ≤ b ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    unfold kap
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 : 0 ≤ Real.log ((x - y) ^ 2 + 1) := Real.log_nonneg (by nlinarith [sq_nonneg (x - y)])
    rw [abs_of_nonneg h1]
    have h2 : Real.log ((x - y) ^ 2 + 1) ≤ Real.log (1 + b ^ 2) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  rw [Real.norm_eq_abs] at this
  rw [abs_of_nonneg (sub_nonneg.mpr hlh)] at this
  linarith

theorem integral_abs_kapD_le {lo hi b : ℝ} (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhb : hi ≤ b) :
    ∫ x in Ioc 0 b, |kapD lo hi x| ≤ 4 * ((hi - lo) * ((1 / 2) * Real.log (1 + b ^ 2))) := by
  have hb : 0 ≤ b := hlo.trans (hlh.trans hhb)
  rw [← intervalIntegral.integral_of_le hb]
  set m := (lo + hi) / 2 with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have hmb : m ≤ b := by rw [hm]; linarith
  have hI : ∀ x y : ℝ, IntervalIntegrable (fun t => |kapD lo hi t|) volume x y :=
    fun x y => ((continuous_kapD lo hi).abs).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 0 m) (hI m b)]
  have hsgn1 : ∀ x ∈ uIcc (0 : ℝ) m, |kapD lo hi x| = kapD lo hi x := by
    intro x hx
    rw [Set.uIcc_of_le hm0] at hx
    rw [abs_of_nonneg]
    unfold kapD
    have h1 : (x - lo) ^ 2 ≤ (x - hi) ^ 2 := by nlinarith [hx.2]
    have h2 := Real.log_le_log (by positivity : (0 : ℝ) < 1 + (x - lo) ^ 2) (by linarith : 1 + (x - lo) ^ 2 ≤ 1 + (x - hi) ^ 2)
    nlinarith
  have hsgn2 : ∀ x ∈ uIcc m b, |kapD lo hi x| = -kapD lo hi x := by
    intro x hx
    rw [Set.uIcc_of_le hmb] at hx
    rw [abs_of_nonpos]
    unfold kapD
    have h1 : (x - hi) ^ 2 ≤ (x - lo) ^ 2 := by nlinarith [hx.1]
    have h2 := Real.log_le_log (by positivity : (0 : ℝ) < 1 + (x - hi) ^ 2) (by linarith : 1 + (x - hi) ^ 2 ≤ 1 + (x - lo) ^ 2)
    nlinarith
  have hFTC : ∀ p q : ℝ, ∫ x in p..q, kapD lo hi x = kapInt lo hi q - kapInt lo hi p := fun p q =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_kapInt lo hi x)
      ((continuous_kapD lo hi).intervalIntegrable _ _)
  rw [intervalIntegral.integral_congr hsgn1, intervalIntegral.integral_congr hsgn2,
    intervalIntegral.integral_neg, hFTC, hFTC]
  have a0 := abs_kapInt_le hlo hlh hhb (⟨le_rfl, hb⟩ : (0 : ℝ) ∈ Icc 0 b)
  have am := abs_kapInt_le hlo hlh hhb (⟨hm0, hmb⟩ : m ∈ Icc 0 b)
  have ab := abs_kapInt_le hlo hlh hhb (⟨hb, le_rfl⟩ : b ∈ Icc 0 b)
  rw [abs_le] at a0 am ab
  linarith [a0.1, a0.2, am.1, am.2, ab.1, ab.2]

/-- The regularised potential is at least the exact one minus `6`. -/
theorem kapInt_ge (lo hi x : ℝ) :
    -(Lam (x - lo) - Lam (x - hi)) - 6 ≤ kapInt lo hi x := by
  have h1 := abs_Abnd_le (x - lo)
  have h2 := abs_Abnd_le (x - hi)
  unfold kapInt Abnd at *
  rw [abs_le] at h1 h2
  nlinarith [h1.1, h1.2, h2.1, h2.2]

end CatalanCore.Uniform.Decay.Nodes
