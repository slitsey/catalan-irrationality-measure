module

public import CatalanCore.Uniform.Decay.Jet.Gram
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section
set_option Elab.async false

/-! # Arbitrary-order pole contour kernels (Q04, cleanup SG-S)
Permanent generic helper for Jet.Source; all orders and coincident node labels.
-/
open Finset MeasureTheory Set Filter Complex
namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore.Frame (g3F)
open CatalanLambda.Decay (contL_tri_west contL_tri_east)

/-! General pole-order ray kernels. The positive index n+1 avoids an order-zero case. -/
open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos norm_inv_rayPt_le
  integrableOn_ray3 integrableOn_invsq rayPt_sub_ne)

noncomputable def gPole (n : ℕ) (p a b : ℝ) (z : ℂ) : ℂ :=
  ((z - p)⁻¹) ^ (n + 1) * ((z - a)⁻¹ * (z - b)⁻¹)

theorem gPole_zero (p a b : ℝ) : gPole 0 p a b = CatalanCore.Frame.g3F p a b := by
  funext z
  simp [gPole, CatalanCore.Frame.g3F, mul_assoc]

theorem hasDerivAt_gPole (n : ℕ) (z : ℂ) {p : ℝ} (hp : z - (p : ℂ) ≠ 0) (a b : ℝ) :
    HasDerivAt (fun q : ℝ => gPole n q a b z)
      ((n + 1 : ℕ) * gPole (n + 1) p a b z) p := by
  have hd := ((hasDerivAt_inv_sub z hp).pow (n + 1)).mul_const
    ((z - (a : ℂ))⁻¹ * (z - (b : ℂ))⁻¹)
  apply hd.congr_deriv
  simp only [gPole, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [show n + 1 + 1 = n + 2 by omega, pow_add]
  ring

theorem norm_gPole_ray_le (n : ℕ) {x θ p a b m r : ℝ}
    (hp : p ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin θ ≠ 0)
    (hm : 0 < m) (hmp : m ≤ |x - p|) (hma : m ≤ |x - a|) (hmb : m ≤ |x - b|) (hr : 0 ≤ r) :
    ‖gPole n p a b (rayPt x θ r) * exp ((θ : ℂ) * I)‖ ≤
      ((1 / (Real.sqrt (kap2 θ) * m)) ^ (n + 1) / (Real.sqrt (kap2 θ)) ^ 2) *
        (1 / (m + r) ^ 2) := by
  let K := Real.sqrt (kap2 θ)
  have hK : 0 < K := Real.sqrt_pos.mpr (kap2_pos hs)
  have hmr : 0 < m + r := by linarith
  have hp1 := norm_inv_rayPt_le (x := x) (θ := θ) p hp hs hr
  have ha1 := norm_inv_rayPt_le (x := x) (θ := θ) a ha hs hr
  have hb1 := norm_inv_rayPt_le (x := x) (θ := θ) b hb hs hr
  have hp2 : ‖(rayPt x θ r - p)⁻¹‖ ≤ 1 / (K * m) := by
    refine hp1.trans (one_div_le_one_div_of_le (by positivity) ?_)
    apply mul_le_mul_of_nonneg_left _ hK.le
    linarith
  have ha2 : ‖(rayPt x θ r - a)⁻¹‖ ≤ 1 / (K * (m + r)) := by
    refine ha1.trans (one_div_le_one_div_of_le (by positivity) ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) hK.le
  have hb2 : ‖(rayPt x θ r - b)⁻¹‖ ≤ 1 / (K * (m + r)) := by
    refine hb1.trans (one_div_le_one_div_of_le (by positivity) ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) hK.le
  simp only [gPole, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
  calc
    _ ≤ (1 / (K * m)) ^ (n + 1) *
        ((1 / (K * (m + r))) * (1 / (K * (m + r)))) := by
      apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hp2 _)
        (mul_le_mul ha2 hb2 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = (1 / (K * m)) ^ (n + 1) * (1 / K ^ 2 * (1 / (m + r) ^ 2)) := by
      congr 1
      field_simp
    _ = _ := by dsimp [K]; ring

theorem integrableOn_ray_gPole (n : ℕ) {x θ p a b : ℝ}
    (hp : p ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => gPole n p a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) := by
  let m := min |x - p| (min |x - a| |x - b|)
  have hp0 : 0 < |x - p| := abs_pos.mpr (sub_ne_zero.mpr hp.symm)
  have ha0 : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr ha.symm)
  have hb0 : 0 < |x - b| := abs_pos.mpr (sub_ne_zero.mpr hb.symm)
  have hm : 0 < m := lt_min hp0 (lt_min ha0 hb0)
  refine CatalanLambda.Decay.integrableOn_of_bound (m := m)
    (C := (1 / (Real.sqrt (kap2 θ) * m)) ^ (n + 1) / (Real.sqrt (kap2 θ)) ^ 2) ?_ hm ?_
  · apply Measurable.aestronglyMeasurable
    simp only [gPole, rayPt]
    fun_prop
  · intro r hr
    exact norm_gPole_ray_le n hp ha hb hs hm (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) (le_of_lt hr)

theorem hasDerivAt_rayI_gPole (n : ℕ) {x θ p₀ a b : ℝ}
    (hp : p₀ ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin θ ≠ 0) :
    HasDerivAt (fun p : ℝ => rayI x θ (gPole n p a b))
      ((n + 1 : ℕ) * rayI x θ (gPole (n + 1) p₀ a b)) p₀ := by
  let ε : ℝ := |x - p₀| / 2
  have hε : 0 < ε := by
    have : 0 < |x - p₀| := abs_pos.mpr (sub_ne_zero.mpr hp.symm)
    dsimp [ε]; positivity
  let m := min ε (min |x - a| |x - b|)
  have ha0 : 0 < |x - a| := abs_pos.mpr (sub_ne_zero.mpr ha.symm)
  have hb0 : 0 < |x - b| := abs_pos.mpr (sub_ne_zero.mpr hb.symm)
  have hm : 0 < m := lt_min hε (lt_min ha0 hb0)
  have hball : ∀ p ∈ Metric.ball p₀ ε, ε ≤ |x - p| := by
    intro p hp
    rw [Metric.mem_ball, Real.dist_eq] at hp
    have htri : |x - p₀| ≤ |x - p| + |p - p₀| := by
      calc
        _ = |(x - p) + (p - p₀)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    dsimp [ε] at *
    linarith
  have hne : ∀ p ∈ Metric.ball p₀ ε, p ≠ x := by
    intro p hp he
    have hb := hball p hp
    rw [he, sub_self, abs_zero] at hb
    linarith
  let e := exp ((θ : ℂ) * I)
  let F : ℝ → ℝ → ℂ := fun p r => gPole n p a b (rayPt x θ r) * e
  let F' : ℝ → ℝ → ℂ := fun p r => ((n + 1 : ℕ) : ℂ) * gPole (n + 1) p a b (rayPt x θ r) * e
  let K := Real.sqrt (kap2 θ)
  let C : ℝ := (n + 1 : ℕ) * ((1 / (K * m)) ^ (n + 1 + 1) / K ^ 2)
  let bound : ℝ → ℝ := fun r => C * (1 / (m + r) ^ 2)
  have hmeas : ∀ p : ℝ, AEStronglyMeasurable (F p) (volume.restrict (Ioi 0)) := by
    intro p
    apply Measurable.aestronglyMeasurable
    simp only [F, gPole, rayPt]
    fun_prop
  have hmeas' : AEStronglyMeasurable (F' p₀) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    simp only [F', gPole, rayPt]
    fun_prop
  have hint : Integrable (F p₀) (volume.restrict (Ioi 0)) := integrableOn_ray_gPole n hp ha hb hs
  have hbd : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ p ∈ Metric.ball p₀ ε, ‖F' p r‖ ≤ bound r := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr p hp => ?_)
    have hbase := norm_gPole_ray_le (n + 1) (hne p hp) ha hb hs hm
      ((min_le_left _ _).trans (hball p hp))
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _)) (le_of_lt hr)
    have hb' := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from Nat.cast_nonneg _)
    simpa only [F', bound, C, K, e, ← mul_assoc, norm_mul, Complex.norm_natCast] using hb'
  have hbint : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_invsq m hm).const_mul C
  have hdiff : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ p ∈ Metric.ball p₀ ε,
      HasDerivAt (fun q => F q r) (F' p r) p := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr p hp => ?_)
    have hz : rayPt x θ r - (p : ℂ) ≠ 0 := by
      exact_mod_cast rayPt_sub_ne (x := x) (θ := θ) (hne p hp) hs (le_of_lt hr)
    exact (hasDerivAt_gPole n (rayPt x θ r) hz a b).mul_const e
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (F' := F') (x₀ := p₀) (s := Metric.ball p₀ ε) (bound := bound)
    (Metric.ball_mem_nhds p₀ hε) (Eventually.of_forall hmeas) hint hmeas' hbd hbint hdiff
  have he : (∫ r in Ioi (0 : ℝ), F' p₀ r) = ((n + 1 : ℕ) : ℂ) * rayI x θ (gPole (n + 1) p₀ a b) := by
    simp only [F', rayI, e, mul_assoc, integral_const_mul]
  rw [he] at hd
  exact hd.2

/-! All-order real-pole contour formula.  Differentiating the contour identity
locally avoids a partial-fraction assumption on the two node labels, which may
coincide.  No pole/node distinction is needed on the east side. -/

noncomputable def poleKernel (a b : ℝ) (p : ℝ) : ℂ :=
  1 / (((p : ℂ) - a) * ((p : ℂ) - b))

theorem hasDerivAt_contL_gPole (n : ℕ) {x φ p a b : ℝ}
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p ≠ x) (ha : x < a) (hb : x < b) :
    HasDerivAt (fun q : ℝ => contL x φ (gPole n q a b))
      (((n + 1 : ℕ) : ℂ) * contL x φ (gPole (n + 1) p a b)) p := by
  have hs : Real.sin φ ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hs' : Real.sin (-φ) ≠ 0 := by
    rw [Real.sin_neg]
    exact neg_ne_zero.mpr hs
  have hd := (hasDerivAt_rayI_gPole n hp ha.ne' hb.ne' hs').sub
    (hasDerivAt_rayI_gPole n hp ha.ne' hb.ne' hs)
  exact hd.congr_deriv (by simp only [contL]; ring)

theorem contL_gPole_west (n : ℕ) (p a b x φ : ℝ)
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p < x) (ha : x < a) (hb : x < b) :
    contL x φ (gPole n p a b) =
      (-(2 * Real.pi * I) * ((n.factorial : ℂ)⁻¹)) *
        iteratedDeriv n (poleKernel a b) p := by
  induction n generalizing p with
  | zero =>
      have he : gPole 0 p a b = (fun z : ℂ => (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹) := by
        funext z
        simp only [gPole, Nat.zero_add, pow_one, mul_assoc]
      rw [he]
      simpa only [Nat.factorial_zero, Nat.cast_one, inv_one,
        mul_one, iteratedDeriv_zero, poleKernel] using
        contL_tri_west p a b x φ h1 h2 hp ha hb
  | succ n ih =>
      have hev : (fun q : ℝ => contL x φ (gPole n q a b)) =ᶠ[nhds p]
          fun q : ℝ => (-(2 * Real.pi * I) * ((n.factorial : ℂ)⁻¹)) *
            iteratedDeriv n (poleKernel a b) q := by
        filter_upwards [Iio_mem_nhds hp] with q hq
        exact ih q hq
      have hd := (hasDerivAt_contL_gPole n h1 h2 hp.ne ha hb).deriv
      have he := hev.deriv_eq
      rw [hd, deriv_const_mul_field, ← iteratedDeriv_succ] at he
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply (mul_left_cancel₀ hn)
      rw [he]
      field_simp

theorem contL_gPole_east (n : ℕ) (p a b x φ : ℝ)
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : x < p) (ha : x < a) (hb : x < b) :
    contL x φ (gPole n p a b) = 0 := by
  induction n generalizing p with
  | zero =>
      have he : gPole 0 p a b = (fun z : ℂ => (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹) := by
        funext z
        simp only [gPole, Nat.zero_add, pow_one, mul_assoc]
      rw [he]
      exact contL_tri_east p a b x φ h1 h2 hp ha hb
  | succ n ih =>
      have hev : (fun q : ℝ => contL x φ (gPole n q a b)) =ᶠ[nhds p]
          fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [Ioi_mem_nhds hp] with q hq
        exact ih q hq
      have hd := (hasDerivAt_contL_gPole n h1 h2 hp.ne' ha hb).deriv
      have he := hev.deriv_eq
      rw [hd, deriv_const] at he
      exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)

theorem contL_gPole (n : ℕ) (p a b x φ : ℝ)
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p ≠ x) (ha : x < a) (hb : x < b) :
    contL x φ (gPole n p a b) =
      if p < x then (-(2 * Real.pi * I) * ((n.factorial : ℂ)⁻¹)) *
        iteratedDeriv n (poleKernel a b) p else 0 := by
  rcases lt_or_gt_of_ne hp with h | h
  · rw [if_pos h]
    exact contL_gPole_west n p a b x φ h1 h2 h ha hb
  · rw [if_neg (not_lt.mpr h.le)]
    exact contL_gPole_east n p a b x φ h1 h2 h ha hb


#print axioms hasDerivAt_gPole
#print axioms norm_gPole_ray_le
#print axioms integrableOn_ray_gPole
#print axioms hasDerivAt_rayI_gPole
#print axioms contL_gPole
end CatalanCore.Uniform.Decay.Jet
