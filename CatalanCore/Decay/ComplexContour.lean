module

public import CatalanCore.Decay.ComplexEnergy
public import CatalanLambda.Decay.AndreiefGeneric
public import CatalanCore.Uniform.Decay.Jet.PoleSeries
public import CatalanCore.Decay.Reflect

@[expose] public section

/-!
# Heine bound and bounded line densities (Lai decay, LD04, LD07)

* `heine_bound` (LD04): for a σ-finite space `(X, m)`, a complex density `w` and a point map
  `z : X → ℂ`, the Hankel determinant `det[∫ w z^{i+j} dm]` is bounded by
  `(1/M!) ∫ ∏ ‖w(xₗ)‖ ‖Δ(z(x))‖² dm^M` (Andréief, `norm_det_le_andreief` as is).
* `heine_complex_bound` (LD04 + LD09): combined with `complex_bound`.
* `lineDens` / `ballMaj_lineDens` / `BallMaj.add` (LD07): a finite sum of bounded densities on
  curves bounded below in chord by `λ|s-t|` (segments) satisfies `BallMajA`.
-/

open MeasureTheory Set Real Filter Topology CatalanCore.Decay.ComplexEnergy

namespace CatalanCore.Decay.ComplexContour

/-! ### LD04: the Heine bound -/

/-- **LD04**: Heine/Andréief bound for the Hankel determinant of the moments of a complex weight. -/
theorem heine_bound {X : Type*} [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    (w z : X → ℂ) (M : ℕ)
    (h : ∀ i j : Fin M, Integrable (fun x => w x * z x ^ (i : ℕ) * z x ^ (j : ℕ)) m) :
    ‖(Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ ((i : ℕ) + (j : ℕ)) ∂m).det‖ ≤
      (1 / (M.factorial : ℝ)) * ∫ x : Fin M → X, (∏ l, ‖w (x l)‖) *
        ‖(Matrix.vandermonde fun l => z (x l)).det‖ ^ 2 ∂(Measure.pi fun _ => m) := by
  have key := CatalanLambda.Decay.norm_det_le_andreief m w (fun i x => z x ^ (i : ℕ))
    (fun j x => z x ^ (j : ℕ)) h
  have e1 : (Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ (i : ℕ) * z x ^ (j : ℕ) ∂m) =
      Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ ((i : ℕ) + (j : ℕ)) ∂m := by
    ext i j
    simp only [Matrix.of_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [pow_add, mul_assoc]
  have e2 : ∀ x : Fin M → X,
      (Matrix.of fun i l : Fin M => z (x l) ^ (i : ℕ)) = Matrix.transpose (Matrix.vandermonde fun l => z (x l)) := by
    intro x; ext i l; simp [Matrix.vandermonde]
  rw [e1] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [e2, Matrix.det_transpose]
  ring

/-- **LD04 + LD09**: the Heine bound with the energy bound of `ComplexEnergy`. -/
theorem heine_complex_bound {X : Type*} [MeasurableSpace X] (m : Measure X) [SigmaFinite m]
    {σ : Measure ℂ} [IsFiniteMeasure σ] {b A α : ℝ} (hσ : BallMajA σ b A α)
    (w z : X → ℂ) {n : ℝ} (hn : 0 < n) {M : ℕ} (hM : (M : ℝ) = n * σ.real univ) {ε : ℝ} (hε : 0 < ε)
    (hint : ∀ i j : Fin M, Integrable (fun x => w x * z x ^ (i : ℕ) * z x ^ (j : ℕ)) m)
    (hG : Integrable (fun x => ‖w x‖ * Real.exp (2 * n * potC σ (z x / n))) m) :
    ‖(Matrix.of fun i j : Fin M => ∫ x, w x * z x ^ ((i : ℕ) + (j : ℕ)) ∂m).det‖ ≤
      (1 / (M.factorial : ℝ)) * (Real.exp (boundConst σ A α n M ε) *
        (∫ x, ‖w x‖ * Real.exp (2 * n * potC σ (z x / n)) ∂m) ^ M) := by
  refine (heine_bound m w z M hint).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact complex_bound m z (fun x => ‖w x‖) (fun x => norm_nonneg _) hσ hn hM hε hG

/-! ### LD07: bounded line densities satisfy `BallMajA` -/

/-- A bounded density `ρ` on `[a, b]` pushed along the curve `γ`. -/
noncomputable def lineDens (γ : ℝ → ℂ) (ρ : ℝ → ℝ) (a b : ℝ) : Measure ℂ :=
  ((volume.restrict (Icc a b)).withDensity fun t => ENNReal.ofReal (ρ t)).map γ

lemma BallMajA.add {σ₁ σ₂ : Measure ℂ} {b₁ b₂ A₁ A₂ α : ℝ} (h₁ : BallMajA σ₁ b₁ A₁ α)
    (h₂ : BallMajA σ₂ b₂ A₂ α) : BallMajA (σ₁ + σ₂) (max b₁ b₂) (A₁ + A₂) α where
  b_pos := lt_max_of_lt_left h₁.b_pos
  A_nonneg := add_nonneg h₁.A_nonneg h₂.A_nonneg
  α_pos := h₁.α_pos
  supp := by
    have e1 : σ₁ (Metric.closedBall (0 : ℂ) (max b₁ b₂))ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr (Metric.closedBall_subset_closedBall
        (le_max_left _ _))) h₁.supp
    have e2 : σ₂ (Metric.closedBall (0 : ℂ) (max b₁ b₂))ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr (Metric.closedBall_subset_closedBall
        (le_max_right _ _))) h₂.supp
    rw [Measure.add_apply, e1, e2, add_zero]
  maj := fun c r hr => by
    rw [Measure.add_apply]
    refine (add_le_add (h₁.maj c r hr) (h₂.maj c r hr)).trans ?_
    rw [← ENNReal.ofReal_add (mul_nonneg h₁.A_nonneg (Real.rpow_nonneg hr _))
      (mul_nonneg h₂.A_nonneg (Real.rpow_nonneg hr _))]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

lemma BallMajA.zero {b A α : ℝ} (hb : 0 < b) (hA : 0 ≤ A) (hα : 0 < α) :
    BallMajA (0 : Measure ℂ) b A α where
  b_pos := hb
  A_nonneg := hA
  α_pos := hα
  supp := by simp
  maj := fun c r _ => by simp

/-- A finite sum of `BallMajA` measures is `BallMajA`. -/
lemma BallMajA.finsum {ι : Type*} (s : Finset ι) (σ : ι → Measure ℂ) (b A : ι → ℝ) {α : ℝ}
    (hα : 0 < α) (h : ∀ i ∈ s, BallMajA (σ i) (b i) (A i) α) {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hb : ∀ i ∈ s, b i ≤ b₀) :
    BallMajA (∑ i ∈ s, σ i) b₀ (∑ i ∈ s, A i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BallMajA.zero hb₀ le_rfl hα
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    have h2 := BallMajA.add (h i (Finset.mem_insert_self _ _)) h1
    refine ⟨hb₀, h2.A_nonneg, hα, ?_, h2.maj⟩
    have hsub : Metric.closedBall (0 : ℂ) (max (b i) b₀) = Metric.closedBall (0 : ℂ) b₀ := by
      rw [max_eq_right (hb i (Finset.mem_insert_self _ _))]
    have := h2.supp
    rwa [hsub] at this

lemma lineDens_apply_le {γ : ℝ → ℂ} (hγc : Continuous γ) {a b : ℝ} {ρ : ℝ → ℝ} {F : ℝ}
    (hρF : ∀ t, ρ t ≤ F) {S : Set ℂ} (hS : MeasurableSet S) :
    lineDens γ ρ a b S ≤ ENNReal.ofReal F * volume (γ ⁻¹' S ∩ Icc a b) := by
  unfold lineDens
  rw [Measure.map_apply hγc.measurable hS, withDensity_apply _ (hγc.measurable hS)]
  calc ∫⁻ x in γ ⁻¹' S, ENNReal.ofReal (ρ x) ∂(volume.restrict (Icc a b))
      ≤ ∫⁻ x in γ ⁻¹' S, ENNReal.ofReal F ∂(volume.restrict (Icc a b)) :=
        setLIntegral_mono measurable_const (fun x _ => ENNReal.ofReal_le_ofReal (hρF x))
    _ = ENNReal.ofReal F * (volume.restrict (Icc a b)) (γ ⁻¹' S) := setLIntegral_const _ _
    _ = _ := by rw [Measure.restrict_apply (hγc.measurable hS)]

/-- **LD07**: a density bounded by `F` on `[a, b]`, pushed along a curve `γ` with chords
`λ|s - t| ≤ ‖γ s - γ t‖`, satisfies `BallMajA` with `A = 4F/λ` (every segment `γ t = M + h t` has
`λ = ‖h‖`). -/
theorem ballMaj_lineDens {γ : ℝ → ℂ} (hγc : Continuous γ) {a b : ℝ} {ρ : ℝ → ℝ}
    {F : ℝ} (hF : 0 ≤ F) (hρF : ∀ t, ρ t ≤ F)
    {lam : ℝ} (hlam : 0 < lam) (hγ : ∀ s t, lam * |s - t| ≤ ‖γ s - γ t‖)
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hbd : ∀ t ∈ Icc a b, ‖γ t‖ ≤ b₀) :
    BallMaj (lineDens γ ρ a b) b₀ (4 * F / lam) := by
  have hA : 0 ≤ 4 * F / lam := by positivity
  refine ⟨hb₀, hA, one_pos, ?_, ?_⟩
  · refine le_antisymm ?_ bot_le
    refine (lineDens_apply_le hγc hρF measurableSet_closedBall.compl).trans ?_
    have : γ ⁻¹' (Metric.closedBall (0 : ℂ) b₀)ᶜ ∩ Icc a b = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
        mem_empty_iff_false, iff_false, not_and, not_not]
      intro h1 h2
      exact absurd (hbd t h2) (not_le.mpr (not_le.mp h1))
    rw [this]; simp
  · intro c r hr0
    rw [Real.rpow_one]
    refine (lineDens_apply_le hγc hρF measurableSet_closedBall).trans ?_
    rcases lt_or_ge r 0 with hr | hr
    · have : γ ⁻¹' Metric.closedBall c r ∩ Icc a b = ∅ := by
        rw [Metric.closedBall_eq_empty.mpr hr]; simp
      rw [this]; simp
    · by_cases hne : (γ ⁻¹' Metric.closedBall c r ∩ Icc a b).Nonempty
      · obtain ⟨t₀, ht₀, -⟩ := hne
        have hsub : γ ⁻¹' Metric.closedBall c r ∩ Icc a b ⊆
            Icc (t₀ - 2 * r / lam) (t₀ + 2 * r / lam) := by
          rintro t ⟨ht, -⟩
          have h1 : ‖γ t - γ t₀‖ ≤ 2 * r := by
            have a1 : ‖γ t - c‖ ≤ r := by
              simpa [Metric.mem_closedBall, dist_eq_norm] using ht
            have a2 : ‖γ t₀ - c‖ ≤ r := by
              simpa [Metric.mem_closedBall, dist_eq_norm] using ht₀
            calc ‖γ t - γ t₀‖ = ‖(γ t - c) - (γ t₀ - c)‖ := by ring_nf
              _ ≤ ‖γ t - c‖ + ‖γ t₀ - c‖ := norm_sub_le _ _
              _ ≤ 2 * r := by linarith
          have h2 : lam * |t - t₀| ≤ 2 * r := (hγ t t₀).trans h1
          have h3 : |t - t₀| ≤ 2 * r / lam := by rw [le_div_iff₀ hlam]; linarith
          rw [abs_le] at h3
          constructor <;> linarith [h3.1, h3.2]
        refine (mul_le_mul' le_rfl (measure_mono hsub)).trans ?_
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul hF]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        field_simp
        ring
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        simp only [measure_empty, mul_zero, zero_le]


/-! ### LD01: the cotangent jet kernel `K_c` and its decay -/

open CatalanCore.Uniform.Decay.Jet in
/-- The jet kernel `(-1)^j (π cot πz)^{(j)}`; its principal part at an integer `m` is
`j!/(z - m)^{j+1}`, so `Res_{z=m} f · cotJet j = f^{(j)}(m)` (`cotJet_succ_eq_lattice`). -/
noncomputable def cotJet (j : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ j * iteratedDeriv j (fun w : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w)) z

/-- `K_c(z) = ∑_{j ∈ J} c_j (-1)^j (π cot πz)^{(j)}` for a finite set `J` of jets. -/
noncomputable def Kc (J : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑ j ∈ J, c j * cotJet j z

lemma sin_pi_ne_zero_of_im_ne {z : ℂ} (hz : z.im ≠ 0) : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro h0
  obtain ⟨a, ha⟩ := Complex.sin_eq_zero_iff.mp h0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : z = (a : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [ha]; ring
  rw [he] at hz
  simp at hz

open CatalanCore.Uniform.Decay.Jet in
/-- Closed form: `cotJet (n+1) z = (n+1)! · higherPoleClosed n z` off the integers. -/
lemma cotJet_succ {z : ℂ} (n : ℕ) (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    cotJet (n + 1) z = ((n + 1).factorial : ℂ) * higherPoleClosed n z := by
  unfold cotJet
  rw [iteratedDeriv_pi_cot_closed n hz]
  have : ((-1 : ℂ) ^ (n + 1)) * ((-1 : ℂ) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; simp
  calc (-1 : ℂ) ^ (n + 1) * ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) * higherPoleClosed n z)
      = ((-1 : ℂ) ^ (n + 1) * (-1 : ℂ) ^ (n + 1)) * (((n + 1).factorial : ℂ) * higherPoleClosed n z) := by ring
    _ = _ := by rw [this, one_mul]

open CatalanCore.Uniform.Decay.Jet in
/-- The lattice-sum form: for `Im z ≠ 0`, `cotJet (n+1) z = (n+1)! ∑_{m ∈ ℤ} (z + m)^{-(n+2)}`. -/
lemma cotJet_succ_eq_lattice {z : ℂ} (n : ℕ) (hz : z.im ≠ 0) :
    cotJet (n + 1) z = ((n + 1).factorial : ℂ) * ∑' m : ℤ, 1 / (z + m) ^ (n + 2) := by
  rw [cotJet_succ n (sin_pi_ne_zero_of_im_ne hz)]
  have := higherPoleSeries_eq_closed n hz
  unfold higherPoleSeries at this
  rw [this]

open CatalanCore.Uniform.Decay.Jet in
/-- **LD01** (decay): for `|Im z| ≥ 1`, `‖cotJet (n+1) z‖ ≤ (n+1)! · higherPoleK n (1/4) · e^{-2π|Im z|}`. -/
theorem norm_cotJet_succ_le (n : ℕ) {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖cotJet (n + 1) z‖ ≤
      ((n + 1).factorial : ℝ) * higherPoleK n (1 / 4) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hz0 : z.im ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  rw [cotJet_succ n (sin_pi_ne_zero_of_im_ne hz0)]
  have hsin : (1 / 4 : ℝ) * Real.exp (Real.pi * |z.im|) ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    have h3 : (3 / 8 : ℝ) ≤ |((Real.pi : ℂ) * z).im| := by
      have : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
      rw [this, abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have := CatalanCore.Decay.norm_sin_ge _ h3
    have e : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
      have : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
      rw [this, abs_mul, abs_of_pos Real.pi_pos]
    rw [e] at this
    linarith
  have hb := norm_higherPoleClosed_le n (by norm_num : (0 : ℝ) < 1 / 4) hsin
  rw [norm_mul]
  have : ‖((n + 1).factorial : ℂ)‖ = ((n + 1).factorial : ℝ) := by simp
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- The constant of the jet bound. -/
noncomputable def jetConst (n : ℕ) : ℝ := ((n + 1).factorial : ℝ) * CatalanCore.Uniform.Decay.Jet.higherPoleK n (1 / 4)

/-- **LD01**: `‖K_c z‖ ≤ (∑_j ‖c_j‖ C_j) e^{-2π|Im z|}` for `|Im z| ≥ 1` and a set of jets `j ≥ 1`. -/
theorem norm_Kc_le (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) (c : ℕ → ℂ) {z : ℂ} (hz : 1 ≤ |z.im|) :
    ‖Kc J c z‖ ≤ (∑ j ∈ J, ‖c j‖ * jetConst (j - 1)) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  unfold Kc
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by have := hJ j hj; omega⟩
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := norm_cotJet_succ_le n hz
  simpa [jetConst, mul_assoc] using this

end CatalanCore.Decay.ComplexContour
