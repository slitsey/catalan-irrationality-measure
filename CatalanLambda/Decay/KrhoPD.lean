import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Basic

/-!
# Positive definiteness of `k_ρ(z,w) = -½ log(|z-w|² + ρ²)` on mean-zero weights

* Lemma F: `log a = ∫_0^∞ (e^{-t} - e^{-a t})/t dt` (from Mathlib's Frullani integral),
* Lemma G: Gaussian sums `∑ w_α w_β e^{-t|p_α-p_β|²} ≥ 0`,
* Lemma K: `∑ q_α q_β k_ρ(p_α,p_β) ≥ 0` if `∑ q_α = 0`,
* Corollary K′.
-/

open Real MeasureTheory Set Filter Topology

namespace CatalanLambda.Decay

/-! ### Lemma F -/

lemma exp_neg_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ exp (-x) - exp (-y) ∧ exp (-x) - exp (-y) ≤ (y - x) * exp (-x) := by
  have h1 : exp (-y) = exp (-x) * exp (-(y - x)) := by rw [← exp_add]; ring_nf
  have h2 : exp (-(y - x)) ≤ 1 := by
    rw [exp_le_one_iff]; linarith
  have h3 : -(y - x) + 1 ≤ exp (-(y - x)) := add_one_le_exp _
  have hx := exp_pos (-x)
  rw [h1]
  constructor
  · nlinarith
  · nlinarith

/-- The integrand of Lemma F. -/
noncomputable def frulInt (a t : ℝ) : ℝ := (exp (-t) - exp (-(a * t))) / t

lemma abs_frulInt_le {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    |frulInt a t| ≤ |a - 1| * exp (-(min 1 a * t)) := by
  unfold frulInt
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
  rcases le_total 1 a with h | h
  · have hb := exp_neg_sub_bounds (x := t) (y := a * t) (by nlinarith)
    rw [abs_of_nonneg hb.1, min_eq_left h, abs_of_nonneg (by linarith)]
    calc exp (-t) - exp (-(a * t)) ≤ (a * t - t) * exp (-t) := hb.2
      _ = (a - 1) * exp (-(1 * t)) * t := by ring_nf
  · have hb := exp_neg_sub_bounds (x := a * t) (y := t) (by nlinarith)
    rw [abs_of_nonpos (by linarith [hb.1]), min_eq_right h, abs_of_nonpos (by linarith)]
    calc -(exp (-t) - exp (-(a * t))) = exp (-(a * t)) - exp (-t) := by ring
      _ ≤ (t - a * t) * exp (-(a * t)) := hb.2
      _ = -(a - 1) * exp (-(a * t)) * t := by ring

lemma continuousOn_frulInt (a : ℝ) : ContinuousOn (frulInt a) (Ioi 0) := by
  unfold frulInt
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ne_of_gt ht)

lemma integrableOn_frulInt {a : ℝ} (ha : 0 < a) : IntegrableOn (frulInt a) (Ioi 0) := by
  have hm : 0 < min 1 a := lt_min one_pos ha
  have hI : IntegrableOn (fun t : ℝ => |a - 1| * exp (-(min 1 a) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hm).const_mul _
  refine Integrable.mono' hI ((continuousOn_frulInt a).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have := abs_frulInt_le ha ht
  rw [Real.norm_eq_abs]
  convert this using 2
  ring_nf

/-- **Lemma F.** `log a = ∫_0^∞ (e^{-t} - e^{-a t})/t dt`. -/
theorem log_eq_integral_frulInt {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), frulInt a t = Real.log a := by
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ => exp (-x)) (a := 1) (b := a) (L := 1) (R := 0)
    (by exact (Continuous.continuousOn (by fun_prop)).locallyIntegrableOn measurableSet_Ioi)
    one_pos ha
    (by
      have : Tendsto (fun x : ℝ => exp (-x)) (𝓝 0) (𝓝 1) := by
        simpa using (Continuous.tendsto (by fun_prop : Continuous fun x : ℝ => exp (-x)) 0)
      exact this.mono_left nhdsWithin_le_nhds)
    (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    (by
      refine (integrableOn_frulInt ha).congr_fun (fun t ht => ?_) measurableSet_Ioi
      simp [frulInt, div_eq_inv_mul])
  have e : ∫ t in Ioi (0 : ℝ), frulInt a t
      = ∫ x in Ioi (0 : ℝ), x⁻¹ • (exp (-(1 * x)) - exp (-(a * x))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp [frulInt, div_eq_inv_mul]
  rw [e, h]
  simp

/-! ### Lemma G -/

lemma hasSum_exp_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (exp x) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at this

/-- Sums of squares: `∑_{i,j} v_i v_j (x_i x_j + y_i y_j)^n ≥ 0`. -/
lemma sum_pow_inner_nonneg {ι : Type*} [Fintype ι] (x y v : ι → ℝ) (n : ℕ) :
    0 ≤ ∑ i, ∑ j, v i * v j * (x i * x j + y i * y j) ^ n := by
  have key : ∑ i, ∑ j, v i * v j * (x i * x j + y i * y j) ^ n
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)
          * (∑ i, v i * x i ^ k * y i ^ (n - k)) ^ 2 := by
    have h1 : ∀ i j, v i * v j * (x i * x j + y i * y j) ^ n
        = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)
            * ((v i * x i ^ k * y i ^ (n - k)) * (v j * x j ^ k * y j ^ (n - k))) := by
      intro i j
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_pow, mul_pow]; ring
    simp_rw [h1]
    have swap : ∀ F : ι → ι → ℕ → ℝ, ∑ i, ∑ j, ∑ k ∈ Finset.range (n + 1), F i j k
        = ∑ k ∈ Finset.range (n + 1), ∑ i, ∑ j, F i j k := by
      intro F
      calc _ = ∑ i, ∑ k ∈ Finset.range (n + 1), ∑ j, F i j k :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    rw [swap]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [key]
  exact Finset.sum_nonneg (fun k _ => by positivity)

/-- **Lemma G.** Gaussian sums are nonnegative. -/
theorem gaussian_sum_nonneg {ι : Type*} [Fintype ι] (p : ι → ℂ) (w : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ i, ∑ j, w i * w j * exp (-t * ‖p i - p j‖ ^ 2) := by
  set x : ι → ℝ := fun i => (p i).re
  set y : ι → ℝ := fun i => (p i).im
  set v : ι → ℝ := fun i => w i * exp (-t * (x i ^ 2 + y i ^ 2))
  have hnorm : ∀ i j, ‖p i - p j‖ ^ 2 = (x i ^ 2 + y i ^ 2) + (x j ^ 2 + y j ^ 2)
      - 2 * (x i * x j + y i * y j) := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, x, y]; ring
  have hterm : ∀ i j, w i * w j * exp (-t * ‖p i - p j‖ ^ 2)
      = v i * v j * exp (2 * t * (x i * x j + y i * y j)) := by
    intro i j
    rw [hnorm]
    simp only [v]
    have : exp (-t * ((x i ^ 2 + y i ^ 2) + (x j ^ 2 + y j ^ 2) - 2 * (x i * x j + y i * y j)))
        = exp (-t * (x i ^ 2 + y i ^ 2)) * exp (-t * (x j ^ 2 + y j ^ 2))
          * exp (2 * t * (x i * x j + y i * y j)) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [this]; ring
  simp_rw [hterm]
  have hS : ∀ i j, HasSum (fun n : ℕ => v i * v j * ((2 * t * (x i * x j + y i * y j)) ^ n
      / (n.factorial : ℝ))) (v i * v j * exp (2 * t * (x i * x j + y i * y j))) :=
    fun i j => (hasSum_exp_series _).mul_left _
  have hT := hasSum_sum (s := (Finset.univ : Finset ι)) (fun i _ =>
    hasSum_sum (s := (Finset.univ : Finset ι)) (fun j _ => hS i j))
  refine hT.nonneg (fun n => ?_)
  have : ∑ i, ∑ j, v i * v j * ((2 * t * (x i * x j + y i * y j)) ^ n / (n.factorial : ℝ))
      = (2 * t) ^ n / (n.factorial : ℝ) * ∑ i, ∑ j, v i * v j * (x i * x j + y i * y j) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow]; ring
  rw [this]
  exact mul_nonneg (by positivity) (sum_pow_inner_nonneg x y v n)

/-! ### Lemma K -/

/-- The regularised logarithmic kernel `k_ρ(z,w) = -½ log(|z-w|² + ρ²)`. -/
noncomputable def krho (ρ : ℝ) (z w : ℂ) : ℝ := -(1 / 2) * Real.log (‖z - w‖ ^ 2 + ρ ^ 2)

lemma krho_comm (ρ : ℝ) (z w : ℂ) : krho ρ z w = krho ρ w z := by
  unfold krho; rw [norm_sub_rev]

lemma krho_self {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : krho ρ z z = -Real.log ρ := by
  unfold krho
  rw [sub_self, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  rw [Real.log_pow]; push_cast; ring

/-- **Lemma K.** If `∑ q_α = 0` then `∑ q_α q_β k_ρ(p_α, p_β) ≥ 0`. -/
theorem krho_sum_nonneg {ι : Type*} [Fintype ι] {ρ : ℝ} (hρ : 0 < ρ) (p : ι → ℂ) (q : ι → ℝ)
    (hq : ∑ i, q i = 0) :
    0 ≤ ∑ i, ∑ j, q i * q j * krho ρ (p i) (p j) := by
  set a : ι → ι → ℝ := fun i j => ‖p i - p j‖ ^ 2 + ρ ^ 2 with ha
  have hapos : ∀ i j, 0 < a i j := fun i j => by positivity
  have hF : ∀ i j, Real.log (a i j) = ∫ t in Ioi (0 : ℝ), frulInt (a i j) t :=
    fun i j => (log_eq_integral_frulInt (hapos i j)).symm
  have hint : ∀ i j, Integrable (fun t => q i * q j * (-frulInt (a i j) t)) (volume.restrict (Ioi 0)) :=
    fun i j => ((integrableOn_frulInt (hapos i j)).neg).const_mul _
  have hsum : ∑ i, ∑ j, q i * q j * krho ρ (p i) (p j)
      = (1 / 2) * ∫ t in Ioi (0 : ℝ), ∑ i, ∑ j, q i * q j * (-frulInt (a i j) t) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => hint i j), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul, integral_neg, ← hF]
    unfold krho
    simp only [ha]
    ring
  rw [hsum]
  refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_))
  have ht : 0 < t := ht
  have hpt : ∀ i j, q i * q j * (-frulInt (a i j) t)
      = (exp (-(ρ ^ 2 * t)) / t) * (q i * q j * exp (-t * ‖p i - p j‖ ^ 2))
        - (exp (-t) / t) * (q i * q j) := by
    intro i j
    have : exp (-(a i j * t)) = exp (-(ρ ^ 2 * t)) * exp (-t * ‖p i - p j‖ ^ 2) := by
      rw [← exp_add]; simp only [ha]; ring_nf
    unfold frulInt
    rw [this]
    field_simp
    ring
  simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [hq, mul_zero, Finset.sum_const_zero, sub_zero]
  have := gaussian_sum_nonneg p q ht.le
  have h2 : 0 ≤ exp (-(ρ ^ 2 * t)) / t := by positivity
  nlinarith [mul_nonneg h2 this]

/-! ### Corollary K′ -/

/-- **Corollary K′.** For `h` points `X_i` (as an indexed family) with uniform weights `1/h`, and a
probability vector `m` on points `c_k`,
`(1/h²) ∑_{i≠j} k_ρ(X_i, X_j) ≥ (2/h) ∑_i U(X_i) - I(σ) + (log ρ)/h`
where `U(z) = ∑_k m_k k_ρ(z, c_k)` and `I(σ) = ∑_{k,l} m_k m_l k_ρ(c_k, c_l)`. -/
theorem krho_energy_lower {h K : ℕ} (hh : 0 < h) {ρ : ℝ} (hρ : 0 < ρ) (X : Fin h → ℂ)
    (c : Fin K → ℂ) (m : Fin K → ℝ) (hm : ∑ k, m k = 1) :
    (2 / (h : ℝ)) * ∑ i, ∑ k, m k * krho ρ (X i) (c k)
        - ∑ k, ∑ l, m k * m l * krho ρ (c k) (c l) + Real.log ρ / (h : ℝ)
      ≤ (1 / (h : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, krho ρ (X i) (X j) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  set p : Fin h ⊕ Fin K → ℂ := Sum.elim X c with hp
  set q : Fin h ⊕ Fin K → ℝ := Sum.elim (fun _ => 1 / (h : ℝ)) (fun k => - m k) with hq
  have hq0 : ∑ i, q i = 0 := by
    rw [Fintype.sum_sum_type]
    simp [hq, hm]
    field_simp
    norm_num
  have key := krho_sum_nonneg hρ p q hq0
  simp only [Fintype.sum_sum_type, hp, hq, Sum.elim_inl, Sum.elim_inr] at key
  have hcross : ∑ k, ∑ i, -m k * (1 / (h : ℝ)) * krho ρ (c k) (X i)
      = ∑ i, ∑ k, 1 / (h : ℝ) * -m k * krho ρ (X i) (c k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [krho_comm]; ring
  have hdiag : ∀ i : Fin h, ∑ j, krho ρ (X i) (X j)
      = -Real.log ρ + ∑ j ∈ Finset.univ.erase i, krho ρ (X i) (X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), krho_self hρ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at key
  have e1 : ∑ i : Fin h, ∑ j : Fin h, 1 / (h : ℝ) * (1 / (h : ℝ)) * krho ρ (X i) (X j)
      = (1 / (h : ℝ)) ^ 2 * ∑ i, ∑ j, krho ρ (X i) (X j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have e2 : ∑ i : Fin h, ∑ k : Fin K, 1 / (h : ℝ) * -m k * krho ρ (X i) (c k)
      = -((1 / (h : ℝ)) * ∑ i, ∑ k, m k * krho ρ (X i) (c k)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have e4 : ∑ k : Fin K, ∑ l : Fin K, -m k * -m l * krho ρ (c k) (c l)
      = ∑ k, ∑ l, m k * m l * krho ρ (c k) (c l) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  rw [hcross, e1, e2, e4] at key
  simp_rw [hdiag, Finset.sum_add_distrib] at key
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at key
  have hu : (1 / (h : ℝ)) * h = 1 := by field_simp
  have hu2 : 2 / (h : ℝ) = 2 * (1 / (h : ℝ)) := by ring
  have hu3 : Real.log ρ / (h : ℝ) = Real.log ρ * (1 / (h : ℝ)) := by ring
  have hu4 : 1 / (h : ℝ) ^ 2 = (1 / (h : ℝ)) ^ 2 := by ring
  rw [hu2, hu3, hu4]
  set u := 1 / (h : ℝ)
  have h5 : u ^ 2 * ((h : ℝ) * -Real.log ρ) = -(Real.log ρ * u) := by
    linear_combination (-(Real.log ρ) * u) * hu
  rw [mul_add, h5] at key
  linarith

end CatalanLambda.Decay
