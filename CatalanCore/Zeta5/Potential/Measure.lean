module

public import CatalanCore.Zeta5.Potential.Basic

/-!
# Z5-POTENTIAL, part 3: the measures `ω` and `ν = f ω` on `[0, b]` (ZD04)

`omega b` is the unit arcsine measure on `[0, b]` (image of the angle law under
`θ ↦ (b/2)(1 + cos θ)`), `nu c N b` is the finite Chebyshev series density `f ω`,
`f = Σ_{k ≤ N} c_k T_k(2t/b - 1)`.  `omega_Icc_le` is ZD04: every interval of radius `r` has
`ω`-mass at most `√(2r/b)`; `nu_le_omega` bounds `ν ≤ (Σ|c_k|) ω`.
-/

@[expose] public section

open MeasureTheory Set Polynomial CatalanMeasure.Signed OAI.InternalCatalan

namespace CatalanCore.Zeta5.Potential

noncomputable section

/-! ### The measures on `[0, b]` -/

/-- The point `t = (b/2)(1 + cos θ) = b cos²(θ/2)` of `[0, b]`. -/
def tmap (b θ : ℝ) : ℝ := b / 2 * (1 + Real.cos θ)

theorem continuous_tmap (b : ℝ) : Continuous (tmap b) := by unfold tmap; fun_prop

theorem tmap_mem {b : ℝ} (hb : 0 ≤ b) (θ : ℝ) : tmap b θ ∈ Icc (0 : ℝ) b := by
  unfold tmap
  constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]

/-- The unit arcsine measure on `[0, b]`. -/
def omega (b : ℝ) : Measure ℝ := arc.map (tmap b)

/-- The comparison measure `ν = f ω` on `[0, b]`, `f = Σ_{k ≤ N} c_k T_k (2t/b - 1)`. -/
def nu (c : ℕ → ℝ) (N : ℕ) (b : ℝ) : Measure ℝ :=
  (arc.withDensity fun θ => ENNReal.ofReal (chebF c N (Real.cos θ))).map (tmap b)

theorem integral_nu {c : ℕ → ℝ} {N : ℕ} {b : ℝ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ t, g t ∂(nu c N b) = ∫ θ, chebF c N (Real.cos θ) * g (tmap b θ) ∂arc := by
  unfold nu
  rw [integral_map (continuous_tmap b).measurable.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun θ => ENNReal.ofReal (chebF c N (Real.cos θ)))
      (ENNReal.measurable_ofReal.comp (continuous_chebF_cos c N).measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hpos _ (cos_mem θ))]

theorem integral_omega {b : ℝ} {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ t, g t ∂(omega b) = ∫ θ, g (tmap b θ) ∂arc :=
  integral_map (continuous_tmap b).measurable.aemeasurable hg.aestronglyMeasurable

theorem nu_univ {c : ℕ → ℝ} {N : ℕ} {b : ℝ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) :
    nu c N b univ = ENNReal.ofReal (c 0) := by
  unfold nu
  rw [Measure.map_apply (continuous_tmap b).measurable MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_chebF c N)
      (ae_of_all _ fun θ => hpos _ (cos_mem θ)), integral_chebF]

/-- Total mass `ν(ℝ) = c_0`. -/
theorem nu_real_univ {c : ℕ → ℝ} {N : ℕ} {b : ℝ}
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (h0 : 0 ≤ c 0) :
    (nu c N b).real univ = c 0 := by
  rw [Measure.real, nu_univ hpos, ENNReal.toReal_ofReal h0]

/-- The mass of `ν` is the whole of `[0, b]`. -/
theorem nu_compl_Icc {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    nu c N b (Icc 0 b)ᶜ = 0 := by
  unfold nu
  rw [Measure.map_apply (continuous_tmap b).measurable measurableSet_Icc.compl]
  have : tmap b ⁻¹' (Icc 0 b)ᶜ = ∅ := by
    ext θ; simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact tmap_mem hb θ
  rw [this]; simp


/-! ### ZD04: the mass of short intervals under the arcsine law -/

theorem cos_sub_cos_ge {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.pi) :
    2 * (v - u) ^ 2 / Real.pi ^ 2 ≤ Real.cos u - Real.cos v := by
  set δ : ℝ := (v - u) / 2 with hδ
  set m : ℝ := (u + v) / 2 with hm
  have hπ := Real.pi_pos
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδπ : δ ≤ Real.pi / 2 := by rw [hδ]; linarith
  have hid : Real.cos u - Real.cos v = 2 * Real.sin m * Real.sin δ := by
    rw [Real.cos_sub_cos]
    have : (u - v) / 2 = -δ := by rw [hδ]; ring
    rw [this, Real.sin_neg]; ring
  have hsd : 2 / Real.pi * δ ≤ Real.sin δ := Real.mul_le_sin hδ0 hδπ
  have hsd0 : 0 ≤ Real.sin δ := le_trans (by positivity) hsd
  have hsm : Real.sin δ ≤ Real.sin m := by
    by_cases hmh : m ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hmh (by rw [hδ, hm]; linarith)
    · have : Real.sin m = Real.sin (Real.pi - m) := (Real.sin_pi_sub m).symm
      rw [this]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by rw [hδ, hm]; linarith)
  rw [hid]
  have h1 : (2 / Real.pi * δ) ^ 2 ≤ Real.sin δ ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hsd 2
  have h2 : Real.sin δ ^ 2 ≤ Real.sin m * Real.sin δ := by nlinarith
  have h3 : 2 * (v - u) ^ 2 / Real.pi ^ 2 = 2 * (2 / Real.pi * δ) ^ 2 := by
    rw [hδ]; field_simp
  rw [h3]
  nlinarith

theorem arc_apply_le (S : Set ℝ) (hS : MeasurableSet S) :
    arc S ≤ ENNReal.ofReal (1 / Real.pi) * volume (S ∩ Icc 0 Real.pi) := by
  unfold arc denMeasure
  rw [withDensity_apply _ hS, Measure.restrict_restrict hS]
  calc ∫⁻ θ in S ∩ Icc 0 Real.pi, ENNReal.ofReal (denQ (fun _ => 0) 0 θ) ∂volume
      = ∫⁻ θ in S ∩ Icc 0 Real.pi, ENNReal.ofReal (1 / Real.pi) ∂volume := by
        refine lintegral_congr fun θ => ?_
        simp [denQ, chebP]
    _ ≤ _ := le_of_eq (by rw [setLIntegral_const])

/-- **ZD04.** The unit arcsine measure `ω` on `[0, b]` gives every interval of radius `r`
at most `√(2r/b)`: `ω[m - r, m + r] ≤ √(2r/b)`. -/
theorem omega_Icc_le {b : ℝ} (hb : 0 < b) (m r : ℝ) :
    omega b (Icc (m - r) (m + r)) ≤ ENNReal.ofReal (Real.sqrt (2 * r / b)) := by
  unfold omega
  rw [Measure.map_apply (continuous_tmap b).measurable measurableSet_Icc]
  set S : Set ℝ := tmap b ⁻¹' Icc (m - r) (m + r) with hSdef
  have hSm : MeasurableSet S := (continuous_tmap b).measurable measurableSet_Icc
  refine (arc_apply_le S hSm).trans ?_
  set d : ℝ := Real.pi * Real.sqrt (2 * r / b) with hd
  have hvol : volume (S ∩ Icc 0 Real.pi) ≤ ENNReal.ofReal d := by
    refine (Real.volume_le_diam _).trans ?_
    refine Metric.ediam_le fun θ1 h1 θ2 h2 => ?_
    have key : ∀ u v : ℝ, u ∈ S ∩ Icc 0 Real.pi → v ∈ S ∩ Icc 0 Real.pi → u ≤ v → v - u ≤ d := by
      intro u v hu hv huv
      have h1 := cos_sub_cos_ge hu.2.1 huv hv.2.2
      have hu' : tmap b u ∈ Icc (m - r) (m + r) := hu.1
      have hv' : tmap b v ∈ Icc (m - r) (m + r) := hv.1
      have h2 : tmap b u - tmap b v = b / 2 * (Real.cos u - Real.cos v) := by unfold tmap; ring
      have h3 : tmap b u - tmap b v ≤ 2 * r := by linarith [hu'.2, hv'.1]
      have h4 : b * (v - u) ^ 2 / Real.pi ^ 2 ≤ 2 * r := by
        have : b / 2 * (2 * (v - u) ^ 2 / Real.pi ^ 2) ≤ b / 2 * (Real.cos u - Real.cos v) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        have e : b / 2 * (2 * (v - u) ^ 2 / Real.pi ^ 2) = b * (v - u) ^ 2 / Real.pi ^ 2 := by ring
        linarith
      have hπ := Real.pi_pos
      have h5 : (v - u) ^ 2 ≤ Real.pi ^ 2 * (2 * r / b) := by
        have : b * (v - u) ^ 2 ≤ 2 * r * Real.pi ^ 2 := by
          rw [div_le_iff₀ (by positivity)] at h4; exact h4
        rw [show Real.pi ^ 2 * (2 * r / b) = (2 * r * Real.pi ^ 2) / b by ring,
          le_div_iff₀ hb]
        linarith
      have h6 : v - u ≤ Real.sqrt (Real.pi ^ 2 * (2 * r / b)) := Real.le_sqrt_of_sq_le h5
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hπ.le] at h6
      exact h6
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_total θ1 θ2 with h | h
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact key _ _ h1 h2 h
    · rw [abs_of_nonneg (by linarith)]; exact key _ _ h2 h1 h
  calc ENNReal.ofReal (1 / Real.pi) * volume (S ∩ Icc 0 Real.pi)
      ≤ ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal d := by gcongr
    _ = ENNReal.ofReal (Real.sqrt (2 * r / b)) := by
        rw [← ENNReal.ofReal_mul (by positivity), hd]
        congr 1
        field_simp


/-- `ν ≤ F ω` with `F = Σ|c_k| ≥ sup |f|` (ZD16, with ZD04 this gives the circle bound of ZD05). -/
theorem nu_le_omega (c : ℕ → ℝ) (N : ℕ) (b : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    nu c N b S ≤ ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) * omega b S := by
  unfold nu omega
  rw [Measure.map_apply (continuous_tmap b).measurable hS,
    Measure.map_apply (continuous_tmap b).measurable hS]
  have hP : MeasurableSet (tmap b ⁻¹' S) := (continuous_tmap b).measurable hS
  rw [withDensity_apply _ hP]
  calc ∫⁻ θ in tmap b ⁻¹' S, ENNReal.ofReal (chebF c N (Real.cos θ)) ∂arc
      ≤ ∫⁻ _θ in tmap b ⁻¹' S, ENNReal.ofReal (∑ k ∈ Finset.range (N + 1), |c k|) ∂arc := by
        refine lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_
        exact (le_abs_self _).trans (abs_chebF_le c N (cos_mem θ))
    _ = _ := by rw [setLIntegral_const]

end

end CatalanCore.Zeta5.Potential
