module

public import CatalanCore.Uniform.Decay.Polygon.Path
public import CatalanCore.Decay.Space

@[expose] public section

/-!
# The frame source on a polygon: holomorphy, high-edge decay, contour identity

For a Loewner frame `Fr` (`F = ∑ w_i ψ(z + μ_i)`, `∑ w_i = 0`) with `ContourOK`, the source
integrand is `f_ab(z) = E(z) (z-a)⁻¹ (z-b)⁻¹` with `E = Fr.EC` (the cotangent reflection term).

* `EC_differentiableAt` : `E` is holomorphic off the real poles `ℤ - μ_i`.
* `srcF_differentiableOn_halfP`, `srcF_differentiableOn_ball` : `f_ab` is holomorphic on both
  open half-planes and on the real-start pole-free disk `B(x*, min δ0 xs)` (also for `a = b`).
* `norm_EC_high` : `‖E z‖ ≤ 4π ∑|w_i| e^{-2π|Im z|}` once `|Im z| ≥ 1/8` (constant cotangent
  term cancels since `∑ w = 0`).
* `polygon_contour_identity` : the exact entry formula of `Frame.contour_identity`, with the two
  reference rays replaced by an arbitrary upper polygon `x* → pts → tail d` and its conjugate.
  The head set is unchanged.
-/

open MeasureTheory Set Filter Topology Complex
open CatalanLambda.Decay (rayPt rayI contL)

namespace CatalanCore.Uniform.Decay.Polygon

variable {Fr : Frame}

/-- The source integrand `E(z) (z-a)⁻¹ (z-b)⁻¹` of the entry `(a, b)`. -/
noncomputable def srcF (Fr : Frame) (a b : ℕ) (z : ℂ) : ℂ :=
  Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹)

/-- The points off every real pole `ℤ - μ_i`. -/
def poleFree (Fr : Frame) : Set ℂ :=
  {z | ∀ i, Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) ≠ 0}

theorem isOpen_poleFree (Fr : Frame) : IsOpen (poleFree Fr) := by
  have : poleFree Fr = ⋂ i, {z : ℂ | Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) ≠ 0} := by
    ext z; simp [poleFree]
  rw [this]
  refine isOpen_iInter_of_finite (fun i => ?_)
  exact isOpen_ne_fun (by fun_prop) continuous_const

/-- The cotangent closed form of `E`. -/
noncomputable def ecot (Fr : Frame) (z : ℂ) : ℂ :=
  -∑ i, (Fr.w i : ℂ) * ((Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) /
    Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))))

theorem EC_eq_ecot {z : ℂ} (hz : z ∈ poleFree Fr) : Fr.EC z = ecot Fr z := by
  have hz' : ∀ i, z + (Fr.μ i : ℂ) ∈ Complex.integerComplement := by
    intro i hmem
    obtain ⟨n, hn⟩ := (by simpa [Complex.integerComplement] using hmem :
      ∃ n : ℤ, (n : ℂ) = z + (Fr.μ i : ℂ))
    apply hz i
    rw [← hn, mul_comm]; exact Complex.sin_int_mul_pi n
  rw [Fr.EC_eq_cot hz', ecot]
  simp only [Complex.cot_eq_cos_div_sin]

theorem ecot_differentiableAt {z : ℂ} (hz : z ∈ poleFree Fr) :
    DifferentiableAt ℂ (ecot Fr) z := by
  unfold ecot
  refine DifferentiableAt.neg ?_
  have : (fun z : ℂ => ∑ i, (Fr.w i : ℂ) * ((Real.pi : ℂ) *
      (Complex.cos ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) /
        Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))))))
      = ∑ i, (fun z : ℂ => (Fr.w i : ℂ) * ((Real.pi : ℂ) *
      (Complex.cos ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))) /
        Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))))) := by
    funext z; simp
  rw [this]
  refine DifferentiableAt.sum (fun i _ => ?_)
  have hc : DifferentiableAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))) z :=
    Complex.differentiable_cos.differentiableAt.comp z (by fun_prop)
  have hs : DifferentiableAt ℂ (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ)))) z :=
    Complex.differentiable_sin.differentiableAt.comp z (by fun_prop)
  exact ((hc.div hs (hz i)).const_mul _).const_mul _

/-- `E` is holomorphic off the real poles. -/
theorem EC_differentiableAt {z : ℂ} (hz : z ∈ poleFree Fr) : DifferentiableAt ℂ Fr.EC z := by
  refine (ecot_differentiableAt hz).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_poleFree Fr).mem_nhds hz] with w hw
  exact EC_eq_ecot hw

theorem poleFree_of_im_ne {z : ℂ} (hz : z.im ≠ 0) : z ∈ poleFree Fr := by
  intro i h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hi := congrArg Complex.im hk
  have hzero : Real.pi * z.im = 0 := by simpa [Complex.mul_im] using hi
  exact (mul_ne_zero Real.pi_ne_zero hz) hzero

/-- The real-start disk `B(x*, δ0)` contains no real pole. -/
theorem poleFree_of_ball (hC : Fr.ContourOK) (N0 : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball ((Fr.xstar N0 : ℝ) : ℂ) (Fr.δ0 : ℝ)) : z ∈ poleFree Fr := by
  intro i h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz' : z = (k : ℂ) - (Fr.μ i : ℂ) := by
    have : (Real.pi : ℂ) * (z + (Fr.μ i : ℂ)) = (Real.pi : ℂ) * (k : ℂ) := by rw [hk]; ring
    have := mul_left_cancel₀ hpi this
    linear_combination this
  rw [Metric.mem_ball, hz'] at hz
  have hg := hC.gap.2 i (-(k : ℤ) - (N0 : ℤ))
  have hd : dist ((k : ℂ) - (Fr.μ i : ℂ)) ((Fr.xstar N0 : ℝ) : ℂ)
      = |(((-(k : ℤ) - (N0 : ℤ) : ℤ) : ℚ) + Fr.μ i - Fr.xs : ℚ)| := by
    rw [Complex.dist_eq]
    have : (k : ℂ) - (Fr.μ i : ℂ) - ((Fr.xstar N0 : ℝ) : ℂ)
        = (((k : ℝ) - (Fr.μ i : ℝ) - Fr.xstar N0 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    unfold Frame.xstar
    have : ((((-(k : ℤ) - (N0 : ℤ) : ℤ) : ℚ) + Fr.μ i - Fr.xs : ℚ) : ℝ)
        = -((k : ℝ) - (Fr.μ i : ℝ) - (-(N0 : ℝ) - (Fr.xs : ℝ))) := by push_cast; ring
    rw [← abs_neg, ← this]
    norm_cast
  rw [hd] at hz
  have : ((Fr.δ0 : ℚ) : ℝ) ≤ ((|(((-(k : ℤ) - (N0 : ℤ) : ℤ) : ℚ) + Fr.μ i - Fr.xs : ℚ)| : ℚ) : ℝ) := by
    exact_mod_cast hg
  push_cast at this hz
  linarith

/-- The radius of the real-start disk. -/
noncomputable def diskR (Fr : Frame) : ℝ := min (Fr.δ0 : ℝ) (Fr.xs : ℝ)

theorem diskR_pos (hC : Fr.ContourOK) : 0 < diskR Fr :=
  lt_min (by exact_mod_cast hC.gap.1) (by exact_mod_cast hC.xs_pos)

theorem node_ne_of_ball (hC : Fr.ContourOK) (N0 a : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball ((Fr.xstar N0 : ℝ) : ℂ) (diskR Fr)) : z - (a : ℂ) ≠ 0 := by
  intro h
  have hza : z = (a : ℂ) := sub_eq_zero.1 h
  rw [Metric.mem_ball, hza, Complex.dist_eq] at hz
  have : (a : ℂ) - ((Fr.xstar N0 : ℝ) : ℂ) = (((a : ℝ) - Fr.xstar N0 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hz
  have h1 := Frame.xs_le_dist hC N0 a
  have h2 : diskR Fr ≤ (Fr.xs : ℝ) := min_le_right _ _
  linarith

theorem srcF_differentiableAt {a b : ℕ} {z : ℂ} (hz : z ∈ poleFree Fr) (ha : z - (a : ℂ) ≠ 0)
    (hb : z - (b : ℂ) ≠ 0) : DifferentiableAt ℂ (srcF Fr a b) z := by
  unfold srcF
  refine (EC_differentiableAt hz).mul (DifferentiableAt.mul ?_ ?_)
  · exact ((differentiableAt_id.sub_const _).inv ha)
  · exact ((differentiableAt_id.sub_const _).inv hb)

theorem sub_nat_ne_of_im {z : ℂ} (hz : z.im ≠ 0) (a : ℕ) : z - (a : ℂ) ≠ 0 := by
  intro h; apply hz; have := congrArg Complex.im h; simpa using this

theorem im_ne_of_halfP {σ : ℝ} {z : ℂ} (hz : z ∈ halfP σ) : z.im ≠ 0 := by
  intro h; have : 0 < σ * z.im := hz; rw [h, mul_zero] at this; exact lt_irrefl _ this

theorem srcF_differentiableOn_halfP (σ : ℝ) (a b : ℕ) :
    DifferentiableOn ℂ (srcF Fr a b) (halfP σ) := fun z hz =>
  (srcF_differentiableAt (poleFree_of_im_ne (im_ne_of_halfP hz))
    (sub_nat_ne_of_im (im_ne_of_halfP hz) a) (sub_nat_ne_of_im (im_ne_of_halfP hz) b)).differentiableWithinAt

theorem srcF_differentiableOn_ball (hC : Fr.ContourOK) (N0 a b : ℕ) :
    DifferentiableOn ℂ (srcF Fr a b) (Metric.ball ((Fr.xstar N0 : ℝ) : ℂ) (diskR Fr)) := by
  intro z hz
  have hz0 : z ∈ Metric.ball ((Fr.xstar N0 : ℝ) : ℂ) (Fr.δ0 : ℝ) :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  exact (srcF_differentiableAt (poleFree_of_ball hC N0 hz0) (node_ne_of_ball hC N0 a hz)
    (node_ne_of_ball hC N0 b hz)).differentiableWithinAt

/-! ### High-edge exponential bound -/

/-- **High-edge bound** (`|Im z| ≥ 1/8`): `‖E z‖ ≤ 4π ∑|w_i| e^{-2π|Im z|}`. -/
theorem norm_EC_high {z : ℂ} (hz : 1 / 8 ≤ |z.im|) :
    ‖Fr.EC z‖ ≤ 4 * Real.pi * (∑ i, |(Fr.w i : ℝ)|) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hpi := Real.pi_gt_three
  have h := Fr.norm_EC_le (z := z) (κ := 1 / 4) (by norm_num) (fun i => by
    have hw : ((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).im = Real.pi * z.im := by simp
    have hge : 3 / 8 ≤ |((Real.pi : ℂ) * (z + (Fr.μ i : ℂ))).im| := by
      rw [hw, abs_mul, abs_of_pos Real.pi_pos]; nlinarith
    have := Decay.norm_sin_ge _ hge
    rw [hw, abs_mul, abs_of_pos Real.pi_pos] at this
    linarith)
  refine h.trans (le_of_eq ?_)
  ring

theorem norm_inv_sub_nat_le {z : ℂ} (hz : z.im ≠ 0) (a : ℕ) :
    ‖(z - (a : ℂ))⁻¹‖ ≤ 1 / |z.im| := by
  rw [norm_inv, ← one_div]
  refine one_div_le_one_div_of_le (abs_pos.2 hz) ?_
  have := Complex.abs_im_le_norm (z - (a : ℂ))
  simpa using this

/-- The constant of the decay hypothesis of `deform`. -/
noncomputable def Khi (Fr : Frame) : ℝ := 4 * Real.pi * ∑ i, |(Fr.w i : ℝ)|

theorem Khi_nonneg : 0 ≤ Khi Fr := by unfold Khi; positivity

/-- Decay hypothesis of `deform` for the source integrand, for `σ = ±1`. -/
theorem srcF_decay {σ : ℝ} (hσ : |σ| = 1) (a b : ℕ) :
    ∀ z : ℂ, 1 ≤ σ * z.im → ‖srcF Fr a b z‖ ≤ Khi Fr / (σ * z.im) ^ 2 := by
  intro z hz
  have habs : |z.im| = σ * z.im := by
    rw [← one_mul |z.im|, ← hσ, ← abs_mul]; exact abs_of_pos (by linarith)
  have hne : z.im ≠ 0 := by intro h; rw [h, mul_zero] at hz; linarith
  have hE := norm_EC_high (Fr := Fr) (z := z) (by rw [habs]; linarith)
  have hex : Real.exp (-(2 * Real.pi * |z.im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := Real.pi_pos; nlinarith [abs_nonneg z.im]
  have hE' : ‖Fr.EC z‖ ≤ Khi Fr := by
    refine hE.trans ?_
    have : 0 ≤ 4 * Real.pi * ∑ i, |(Fr.w i : ℝ)| := by positivity
    unfold Khi; nlinarith
  unfold srcF
  rw [norm_mul, norm_mul]
  have h1 := norm_inv_sub_nat_le hne a
  have h2 := norm_inv_sub_nat_le hne b
  rw [habs] at h1 h2
  have hpos : 0 < σ * z.im := by linarith
  calc ‖Fr.EC z‖ * (‖(z - (a : ℂ))⁻¹‖ * ‖(z - (b : ℂ))⁻¹‖)
      ≤ Khi Fr * ((1 / (σ * z.im)) * (1 / (σ * z.im))) :=
        mul_le_mul hE' (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (by positivity) Khi_nonneg
    _ = Khi Fr / (σ * z.im) ^ 2 := by field_simp

/-! ### Deformation of the two reference rays and the polygon contour identity -/

theorem rayI_eq_rayInt (x θ : ℝ) (f : ℂ → ℂ) :
    rayI x θ f = rayInt f (x : ℂ) (Complex.exp ((θ : ℂ) * I)) := rfl

/-- The reference direction used for the deformation (the slope-one ray). -/
noncomputable def phiRef : ℝ := Decay.phiS 1

theorem phiRef_gt : Real.pi / 2 < phiRef := Decay.phiS_gt 1
theorem phiRef_lt : phiRef < Real.pi := Decay.phiS_lt one_pos

theorem sin_phiRef_pos : 0 < Real.sin phiRef :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [phiRef_gt, Real.pi_pos]) phiRef_lt

/-- **Upper deformation**: the upper reference ray integral equals the upper polygon
integral. -/
theorem upper_deform (hC : Fr.ContourOK) (N0 a b : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d
      = rayI (Fr.xstar N0) phiRef (srcF Fr a b) := by
  rw [rayI_eq_rayInt]
  refine deform (σ := 1) (δ := diskR Fr) (by simp) (diskR_pos hC)
    (srcF_differentiableOn_halfP 1 a b) (srcF_differentiableOn_ball hC N0 a b) pts
    (fun z hz => by simpa using hpts z hz) (by simpa using hd) ?_ Khi_nonneg
    (srcF_decay (by simp) a b)
  rw [one_mul, Complex.exp_ofReal_mul_I_im]; exact sin_phiRef_pos

/-- **Lower deformation**: the lower reference ray integral equals the conjugate polygon
integral. -/
theorem lower_deform (hC : Fr.ContourOK) (N0 a b : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) (pts.map (starRingEnd ℂ)) (starRingEnd ℂ d)
      = rayI (Fr.xstar N0) (-phiRef) (srcF Fr a b) := by
  rw [rayI_eq_rayInt]
  refine deform (σ := -1) (δ := diskR Fr) (by simp) (diskR_pos hC)
    (srcF_differentiableOn_halfP (-1) a b) (srcF_differentiableOn_ball hC N0 a b) _
    (fun z hz => ?_) (by simpa using hd) ?_ Khi_nonneg (srcF_decay (by simp) a b)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    simpa using hpts w hw
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]; linarith [sin_phiRef_pos]

/-- **Polygon contour identity** (Part 2, Proposition `gram`, entry form).  For every upper
polygon `x* → pts → tail d` (all vertices after `x*` strictly upper, tail direction upper), and
all natural nodes `a, b` (including `a = b`):
`norm · T_ab = head + (2πi)⁻¹ (∫_{lower polygon} - ∫_{upper polygon}) E(z)/((z-a)(z-b)) dz`.
The head (the poles to the right of `x* = -N0 - xs`) is exactly the head of the ray identity. -/
theorem polygon_contour_identity (hC : Fr.ContourOK) (N0 a b : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    (((Fr.norm : ℝ) * Fr.Tent a b : ℝ) : ℂ)
      = ((Fr.atomHead N0 a b : ℝ) : ℂ) + (2 * Real.pi * I)⁻¹ *
          (polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) (pts.map (starRingEnd ℂ)) (starRingEnd ℂ d)
            - polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d) := by
  rw [upper_deform hC N0 a b pts hpts hd, lower_deform hC N0 a b pts hpts hd,
    Fr.norm_mul_Tent a b]
  exact Fr.contour_identity hC phiRef_gt phiRef_lt N0 a b

end CatalanCore.Uniform.Decay.Polygon
