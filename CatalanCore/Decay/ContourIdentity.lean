module

public import CatalanCore.Decay.ComplexContour
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CatalanCore.Uniform.Decay.Polygon.Deform

@[expose] public section

/-!
# The contour identity for rational functions with real poles (Lai decay, LD02)

Generic statement (`contour_identity_Kc`): for `f = ∑ᵢ (aᵢ/(z - pᵢ) + bᵢ/(z - pᵢ)²)` with real poles
`pᵢ` to the left of a non-integer real crossing `v`, `∑ aᵢ = 0`, a finite set `J` of jets `j ≥ 1`
with coefficients `c`, and any polygon `v → pts → tail d` into the upper half-plane (with its mirror
image),

`∮_Γ f(z) K_c(z) dz = -2πI ∑_{j ∈ J} c_j ∑_{B ∈ ℤ, B > v} f^{(j)}(B)`,

where `K_c = ∑ c_j cotJet j`, `cotJet j = (-1)^j (π cot πz)^{(j)}`, and `Γ` is the polygon traversed
upward (the lower polygon reversed).

Proof: the polygon is deformed to the vertical reference ray (`Polygon.Deform.deform`, as is); the
lattice-sum form of `cotJet` (`cotJet_succ_eq_lattice`) is integrated termwise (Fubini,
`line_identity`); each term is a line integral of `I (z-p)^{-s} (z-m)^{-q}` computed by the
partial-fraction recursion `G_rec` from two base facts: `∫ I (lz c)^{-r} = 0` (`r ≥ 2`) and the
principal value `∫ I ((lz a)⁻¹ - (lz b)⁻¹) = iπ (sg a - sg b)`.  No residue theorem is used.

On the line `z = v + t I` put `lz c t = c + t I` (`z - a = lz (v - a) t`).
-/

open Complex MeasureTheory Set Filter Topology

namespace CatalanCore.Decay.LineInt

noncomputable def lz (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * I

lemma norm_sq_lz (c t : ℝ) : ‖lz c t‖ ^ 2 = c ^ 2 + t ^ 2 := by
  unfold lz
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring

lemma abs_le_norm_lz (c t : ℝ) : |t| ≤ ‖lz c t‖ := by
  have h := norm_sq_lz c t
  have : |t| ^ 2 ≤ ‖lz c t‖ ^ 2 := by rw [h, sq_abs]; nlinarith [sq_nonneg c]
  exact (sq_le_sq₀ (abs_nonneg t) (norm_nonneg _)).mp this

lemma abs_le_norm_lz' (c t : ℝ) : |c| ≤ ‖lz c t‖ := by
  have h := norm_sq_lz c t
  have : |c| ^ 2 ≤ ‖lz c t‖ ^ 2 := by rw [h, sq_abs]; nlinarith [sq_nonneg t]
  exact (sq_le_sq₀ (abs_nonneg c) (norm_nonneg _)).mp this

lemma lz_ne_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) : lz c t ≠ 0 := by
  intro h
  have := abs_le_norm_lz' c t
  rw [h, norm_zero] at this
  exact hc (abs_nonpos_iff.mp this)

lemma continuous_lz (c : ℝ) : Continuous (lz c) := by unfold lz; fun_prop

lemma hasDerivAt_lz (c t : ℝ) : HasDerivAt (lz c) I t := by
  unfold lz
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  simpa using (h1.mul_const I).const_add (c : ℂ)

/-- Integrability from a bound by `C/(1+t²)`. -/
lemma integrable_of_bound {g : ℝ → ℂ} (hg : Continuous g) (C : ℝ)
    (h : ∀ t, ‖g t‖ ≤ C * (1 + t ^ 2)⁻¹) : Integrable g := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hg.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall h

lemma inv_sq_add_le {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    (c ^ 2 + t ^ 2)⁻¹ ≤ (min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹ := by
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  have h1 : min (c ^ 2) 1 ≤ c ^ 2 := min_le_left _ _
  have h2 : min (c ^ 2) 1 ≤ 1 := min_le_right _ _
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg t, mul_nonneg hm.le (sq_nonneg t)]

lemma norm_inv_pow_lz {c : ℝ} (hc : c ≠ 0) {r : ℕ} (hr : 2 ≤ r) (t : ℝ) :
    ‖1 / (lz c t) ^ r‖ ≤ (|c| ^ (r - 2))⁻¹ * ((min (c ^ 2) 1)⁻¹ * (1 + t ^ 2)⁻¹) := by
  have hn : 0 < ‖lz c t‖ := norm_pos_iff.mpr (lz_ne_zero hc t)
  rw [norm_div, norm_one, norm_pow]
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have h1 : |c| ^ (r - 2) * ‖lz c t‖ ^ 2 ≤ ‖lz c t‖ ^ r := by
    have : ‖lz c t‖ ^ r = ‖lz c t‖ ^ (r - 2) * ‖lz c t‖ ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcpos.le (abs_le_norm_lz' c t) _)
      (by positivity)
  have h2 : 1 / ‖lz c t‖ ^ r ≤ 1 / (|c| ^ (r - 2) * ‖lz c t‖ ^ 2) :=
    one_div_le_one_div_of_le (by positivity) h1
  refine h2.trans ?_
  rw [norm_sq_lz, one_div, mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_sq_add_le hc t) (by positivity)

lemma integrable_inv_pow_lz {c : ℝ} (hc : c ≠ 0) {r : ℕ} (hr : 2 ≤ r) :
    Integrable (fun t : ℝ => 1 / (lz c t) ^ r) := by
  refine integrable_of_bound ?_ ((|c| ^ (r - 2))⁻¹ * (min (c ^ 2) 1)⁻¹) (fun t => ?_)
  · have : Continuous fun t : ℝ => (lz c t) ^ r := (continuous_lz c).pow r
    exact continuous_const.div this (fun t => pow_ne_zero _ (lz_ne_zero hc t))
  · calc _ ≤ _ := norm_inv_pow_lz hc hr t
      _ = _ := by ring

/-- `∫ I (lz c t)^{-r} dt = 0` for `r ≥ 2`. -/
theorem integral_pow_inv {c : ℝ} (hc : c ≠ 0) {r : ℕ} (hr : 2 ≤ r) :
    ∫ t : ℝ, I * (1 / (lz c t) ^ r) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  set F : ℝ → ℂ := fun t => -(((↑(k + 1) : ℂ) * (lz c t) ^ (k + 1))⁻¹) with hF
  have hder : ∀ t, HasDerivAt F (I * (1 / (lz c t) ^ (k + 2))) t := by
    intro t
    have h1 := (hasDerivAt_lz c t).pow (k + 1)
    have hne : (lz c t) ^ (k + 1) ≠ 0 := pow_ne_zero _ (lz_ne_zero hc t)
    have hk : ((↑(k + 1) : ℂ) * (lz c t) ^ (k + 1)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero k) hne
    have h2 : HasDerivAt F _ t := ((h1.const_mul ((↑(k + 1) : ℂ))).inv hk).neg
    refine h2.congr_deriv ?_
    have hz := lz_ne_zero hc t
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    field_simp
    ring
  have hint : Integrable (fun t : ℝ => I * (1 / (lz c t) ^ (k + 2))) :=
    (integrable_inv_pow_lz hc (by omega)).const_mul I
  have hlim : ∀ (l : Filter ℝ), (∀ t ∈ ({s | 1 ≤ |s|} : Set ℝ), True) →
      Tendsto (fun t : ℝ => |t|) l atTop → Tendsto F l (𝓝 0) := by
    intro l _ hl
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hbd : ∀ᶠ t in l, ‖F t‖ ≤ (|t|)⁻¹ := by
      filter_upwards [hl.eventually_ge_atTop 1] with t ht
      have ht0 : 0 < |t| := by linarith
      have hn1 : 1 ≤ ‖lz c t‖ := ht.trans (abs_le_norm_lz c t)
      have hnn : 0 < ‖lz c t‖ := by linarith
      simp only [hF, norm_neg, norm_inv, norm_mul, norm_pow]
      have hk : (1 : ℝ) ≤ ‖(↑(k + 1) : ℂ)‖ := by
        rw [Complex.norm_natCast]; exact_mod_cast Nat.succ_pos k
      have hp : ‖lz c t‖ ≤ ‖lz c t‖ ^ (k + 1) := by
        simpa using pow_le_pow_right₀ hn1 (Nat.le_add_left 1 k)
      calc (‖(↑(k + 1) : ℂ)‖ * ‖lz c t‖ ^ (k + 1))⁻¹ ≤ (1 * ‖lz c t‖)⁻¹ := by
            apply inv_anti₀ (by positivity)
            exact mul_le_mul hk hp hnn.le (by positivity)
        _ = (‖lz c t‖)⁻¹ := by simp
        _ ≤ (|t|)⁻¹ := inv_anti₀ ht0 (abs_le_norm_lz c t)
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) hbd ?_
    exact tendsto_inv_atTop_zero.comp hl
  have := integral_of_hasDerivAt_of_tendsto hder hint
    (hlim atBot (fun _ _ => trivial) tendsto_abs_atBot_atTop)
    (hlim atTop (fun _ _ => trivial) tendsto_abs_atTop_atTop)
  rw [this]; simp

/-- The sign `±1` of `c`. -/
noncomputable def sg (c : ℝ) : ℝ := if 0 < c then 1 else -1

lemma I_div_lz {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    I * (1 / lz c t) = ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) + ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
  have hz := lz_ne_zero hc t
  have hz2 : (c : ℂ) - t * I ≠ 0 := by
    have := lz_ne_zero hc (-t)
    simpa [lz, sub_eq_add_neg] using this
  have e1 : (t : ℂ) + c * I = I * ((c : ℂ) - t * I) := by linear_combination (t : ℂ) * I_sq
  have e2 : (c : ℂ) ^ 2 + (t : ℂ) ^ 2 = ((c : ℂ) + t * I) * ((c : ℂ) - t * I) := by
    linear_combination ((t : ℂ) ^ 2) * I_sq
  have e3 : ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) + ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I =
      ((t : ℂ) + c * I) / ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
    push_cast
    ring
  rw [e3, e1, e2, mul_div_mul_right _ _ hz2]
  unfold lz
  ring

lemma integral_inv_sq_add {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun t : ℝ => c / (c ^ 2 + t ^ 2)) ∧
      ∫ t : ℝ, c / (c ^ 2 + t ^ 2) = Real.pi * sg c := by
  have hform : ∀ t : ℝ, c / (c ^ 2 + t ^ 2) = c⁻¹ * (1 + (t / c) ^ 2)⁻¹ := by
    intro t
    field_simp
  simp_rw [hform]
  have hdiv := Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) c
  refine ⟨?_, ?_⟩
  · refine Integrable.const_mul ?_ _
    have := (integrable_inv_one_add_sq.comp_div hc)
    exact this
  · rw [integral_const_mul]
    rw [hdiv, integral_univ_inv_one_add_sq, smul_eq_mul]
    unfold sg
    rcases lt_or_gt_of_ne hc with h | h
    · rw [if_neg (not_lt.mpr h.le), abs_of_neg h]; field_simp
    · rw [if_pos h, abs_of_pos h]; field_simp

lemma integrable_diff_simple {ca cb : ℝ} (ha : ca ≠ 0) (hb : cb ≠ 0) :
    Integrable (fun t : ℝ => I * (1 / lz ca t) - I * (1 / lz cb t)) := by
  set μ : ℝ := min (min (ca ^ 2) 1) (min (cb ^ 2) 1) with hμ
  have hμpos : 0 < μ := lt_min (lt_min (by positivity) one_pos) (lt_min (by positivity) one_pos)
  refine integrable_of_bound ?_ (|cb - ca| * μ⁻¹) (fun t => ?_)
  · have h1 : Continuous fun t : ℝ => I * (1 / lz ca t) :=
      continuous_const.mul (continuous_const.div (continuous_lz ca) (lz_ne_zero ha))
    have h2 : Continuous fun t : ℝ => I * (1 / lz cb t) :=
      continuous_const.mul (continuous_const.div (continuous_lz cb) (lz_ne_zero hb))
    exact h1.sub h2
  · have hza := lz_ne_zero ha t
    have hzb := lz_ne_zero hb t
    have e : I * (1 / lz ca t) - I * (1 / lz cb t) =
        I * ((cb - ca : ℝ) : ℂ) / (lz ca t * lz cb t) := by
      have e0 : I * (1 / lz ca t) - I * (1 / lz cb t) =
          I * (lz cb t - lz ca t) / (lz ca t * lz cb t) := by field_simp
      have e1 : lz cb t - lz ca t = ((cb - ca : ℝ) : ℂ) := by unfold lz; push_cast; ring
      rw [e0, e1]
    rw [e, norm_div, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hp : μ * (1 + t ^ 2) ≤ ‖lz ca t‖ * ‖lz cb t‖ := by
      have hna := norm_sq_lz ca t
      have hnb := norm_sq_lz cb t
      rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow (‖lz ca t‖), hna, hnb]
      have h1 : μ * (1 + t ^ 2) ≤ ca ^ 2 + t ^ 2 := by
        have := (min_le_left _ _ : μ ≤ min (ca ^ 2) 1).trans (min_le_left _ _)
        have h2 : μ ≤ 1 := (min_le_left _ _ : μ ≤ min (ca ^ 2) 1).trans (min_le_right _ _)
        nlinarith [sq_nonneg t]
      have h2 : μ * (1 + t ^ 2) ≤ cb ^ 2 + t ^ 2 := by
        have := (min_le_right _ _ : μ ≤ min (cb ^ 2) 1).trans (min_le_left _ _)
        have h2 : μ ≤ 1 := (min_le_right _ _ : μ ≤ min (cb ^ 2) 1).trans (min_le_right _ _)
        nlinarith [sq_nonneg t]
      calc (μ * (1 + t ^ 2)) ^ 2 = (μ * (1 + t ^ 2)) * (μ * (1 + t ^ 2)) := sq _
        _ ≤ (ca ^ 2 + t ^ 2) * (cb ^ 2 + t ^ 2) := mul_le_mul h1 h2 (by positivity) (by positivity)
    have hpos : 0 < ‖lz ca t‖ * ‖lz cb t‖ := by positivity
    calc |cb - ca| / (‖lz ca t‖ * ‖lz cb t‖) ≤ |cb - ca| / (μ * (1 + t ^ 2)) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hp
      _ = |cb - ca| * μ⁻¹ * (1 + t ^ 2)⁻¹ := by field_simp

/-- `∫ I ((lz a)⁻¹ - (lz b)⁻¹) dt = iπ (sg a - sg b)`: the principal value of the simple poles. -/
theorem integral_diff_simple {ca cb : ℝ} (ha : ca ≠ 0) (hb : cb ≠ 0) :
    ∫ t : ℝ, (I * (1 / lz ca t) - I * (1 / lz cb t)) =
      ((Real.pi * (sg ca - sg cb) : ℝ) : ℂ) * I := by
  set F : ℝ → ℂ := fun t => I * (1 / lz ca t) - I * (1 / lz cb t) with hF
  have hFi : Integrable F := integrable_diff_simple ha hb
  set φ : ℝ → ℝ := fun t => t / (ca ^ 2 + t ^ 2) - t / (cb ^ 2 + t ^ 2) with hφ
  set ψ : ℝ → ℝ := fun t => ca / (ca ^ 2 + t ^ 2) - cb / (cb ^ 2 + t ^ 2) with hψ
  have hFe : ∀ t, F t = (φ t : ℂ) + (ψ t : ℂ) * I := by
    intro t
    simp only [hF, I_div_lz ha, I_div_lz hb, hφ, hψ]
    push_cast; ring
  have hre : ∀ t, (F t).re = φ t := fun t => by rw [hFe]; simp
  have him : ∀ t, (F t).im = ψ t := fun t => by rw [hFe]; simp
  have hφi : Integrable φ := by simpa [hre] using hFi.re
  have hψa := integral_inv_sq_add ha
  have hψb := integral_inv_sq_add hb
  have hψi : Integrable ψ := hψa.1.sub hψb.1
  have hφ0 : ∫ t, φ t = 0 := by
    have hodd : ∀ t, φ (-t) = -φ t := by
      intro t; simp only [hφ]; rw [neg_sq]; ring
    have h1 : ∫ t, φ (-t) = ∫ t, φ t := integral_neg_eq_self φ volume
    have h2 : ∫ t, φ (-t) = -∫ t, φ t := by
      simp_rw [hodd]; rw [integral_neg]
    linarith
  have hψv : ∫ t, ψ t = Real.pi * (sg ca - sg cb) := by
    simp only [hψ]
    rw [integral_sub hψa.1 hψb.1, hψa.2, hψb.2]; ring
  have := integral_re_add_im hFi
  have this : ((∫ x, (F x).re : ℝ) : ℂ) + ((∫ x, (F x).im : ℝ) : ℂ) * Complex.I = ∫ x, F x := this
  have h1 : ∫ t, (F t).re = 0 := by
    rw [show (fun t => (F t).re) = φ from funext hre]; exact hφ0
  have h2 : ∫ t, (F t).im = Real.pi * (sg ca - sg cb) := by
    rw [show (fun t => (F t).im) = ψ from funext him]; exact hψv
  rw [← this, h1, h2]
  push_cast
  ring

/-- The integrand `I · (z - p)^{-s} (z - m)^{-q}` on the line, `z - p = lz cp t`, `z - m = lz cm t`. -/
noncomputable def G (cp cm : ℝ) (s q : ℕ) (t : ℝ) : ℂ :=
  I * (1 / (lz cp t) ^ s) * (1 / (lz cm t) ^ q)

lemma G_rec {cp cm : ℝ} (hp : cp ≠ 0) (hm : cm ≠ 0) (s q : ℕ) (t : ℝ) :
    ((cm - cp : ℝ) : ℂ) * G cp cm (s + 1) (q + 1) t = G cp cm (s + 1) q t - G cp cm s (q + 1) t := by
  have h1 := lz_ne_zero hp t
  have h2 := lz_ne_zero hm t
  have hz : lz cm t = lz cp t + ((cm - cp : ℝ) : ℂ) := by unfold lz; push_cast; ring
  unfold G
  rw [hz] at h2 ⊢
  field_simp
  ring

/-- `κ = 2πi` if the second pole `m` lies to the right of the line (`cm < 0`), else `0`. -/
noncomputable def kap (cm : ℝ) : ℂ := ((Real.pi * (1 - sg cm) : ℝ) : ℂ) * I

lemma G_one_one {cp cm : ℝ} (hp : cp ≠ 0) (hm : cm ≠ 0) (hD : cm ≠ cp) (t : ℝ) :
    G cp cm 1 1 t = (1 / ((cm - cp : ℝ) : ℂ)) * (I * (1 / lz cp t) - I * (1 / lz cm t)) := by
  have h := G_rec hp hm 0 0 t
  have hD' : ((cm - cp : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hD
  have e0 : G cp cm 1 0 t = I * (1 / lz cp t) := by simp [G]
  have e1 : G cp cm 0 1 t = I * (1 / lz cm t) := by simp [G]
  rw [e0, e1] at h
  field_simp
  field_simp at h
  linear_combination h

lemma integral_G_one {cp cm : ℝ} (hp : 0 < cp) (hm : cm ≠ 0) (hD : cm ≠ cp) :
    ∀ q : ℕ, 1 ≤ q → Integrable (G cp cm 1 q) ∧
      ∫ t : ℝ, G cp cm 1 q t = kap cm / ((cm - cp : ℝ) : ℂ) ^ q := by
  have hp' : cp ≠ 0 := hp.ne'
  have hD' : ((cm - cp : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hD
  intro q hq
  induction q, hq using Nat.le_induction with
  | base =>
    have hi := integrable_diff_simple hp' hm
    have heq : G cp cm 1 1 = fun t => (1 / ((cm - cp : ℝ) : ℂ)) *
        (I * (1 / lz cp t) - I * (1 / lz cm t)) := funext (G_one_one hp' hm hD)
    rw [heq]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, integral_diff_simple hp' hm]
    have : sg cp = 1 := by unfold sg; rw [if_pos hp]
    rw [this]; unfold kap; push_cast; ring
  | succ q hq ih =>
    obtain ⟨hi, hv⟩ := ih
    have hrec : ∀ t, G cp cm 1 (q + 1) t = (1 / ((cm - cp : ℝ) : ℂ)) *
        (G cp cm 1 q t - I * (1 / (lz cm t) ^ (q + 1))) := by
      intro t
      have h := G_rec hp' hm 0 q t
      have e1 : G cp cm 0 (q + 1) t = I * (1 / (lz cm t) ^ (q + 1)) := by simp [G]
      rw [e1] at h
      field_simp
      field_simp at h
      linear_combination h
    have hI0 : Integrable (fun t : ℝ => I * (1 / (lz cm t) ^ (q + 1))) :=
      (integrable_inv_pow_lz hm (by omega)).const_mul I
    have heq : G cp cm 1 (q + 1) = fun t => (1 / ((cm - cp : ℝ) : ℂ)) *
        (G cp cm 1 q t - I * (1 / (lz cm t) ^ (q + 1))) := funext hrec
    rw [heq]
    refine ⟨(hi.sub hI0).const_mul _, ?_⟩
    rw [integral_const_mul, integral_sub hi hI0, hv, integral_pow_inv hm (by omega)]
    field_simp
    ring

lemma integral_G_two {cp cm : ℝ} (hp : 0 < cp) (hm : cm ≠ 0) (hD : cm ≠ cp) :
    ∀ q : ℕ, Integrable (G cp cm 2 q) ∧
      ∫ t : ℝ, G cp cm 2 q t = -(q : ℂ) * kap cm / ((cm - cp : ℝ) : ℂ) ^ (q + 1) := by
  have hp' : cp ≠ 0 := hp.ne'
  have hD' : ((cm - cp : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hD
  intro q
  induction q with
  | zero =>
    have : G cp cm 2 0 = fun t => I * (1 / (lz cp t) ^ 2) := by
      funext t; simp [G]
    rw [this]
    exact ⟨(integrable_inv_pow_lz hp' le_rfl).const_mul I,
      by rw [integral_pow_inv hp' le_rfl]; simp⟩
  | succ q ih =>
    obtain ⟨hi, hv⟩ := ih
    have h1 := integral_G_one hp hm hD (q + 1) (by omega)
    have hrec : ∀ t, G cp cm 2 (q + 1) t = (1 / ((cm - cp : ℝ) : ℂ)) *
        (G cp cm 2 q t - G cp cm 1 (q + 1) t) := by
      intro t
      have h := G_rec hp' hm 1 q t
      field_simp
      field_simp at h
      linear_combination h
    have heq : G cp cm 2 (q + 1) = fun t => (1 / ((cm - cp : ℝ) : ℂ)) *
        (G cp cm 2 q t - G cp cm 1 (q + 1) t) := funext hrec
    rw [heq]
    refine ⟨(hi.sub h1.1).const_mul _, ?_⟩
    rw [integral_const_mul, integral_sub hi h1.1, hv, h1.2]
    push_cast
    field_simp
    ring

/-- Merged poles (`p = m`): `G s q = I (lz c)^{-(s+q)}` integrates to zero for `s + q ≥ 2`. -/
lemma integral_G_merged {c : ℝ} (hc : c ≠ 0) {s q : ℕ} (hsq : 2 ≤ s + q) :
    Integrable (G c c s q) ∧ ∫ t : ℝ, G c c s q t = 0 := by
  have : G c c s q = fun t => I * (1 / (lz c t) ^ (s + q)) := by
    funext t
    unfold G
    rw [pow_add]
    field_simp
  rw [this]
  exact ⟨(integrable_inv_pow_lz hc hsq).const_mul I, integral_pow_inv hc hsq⟩

/-! ### Rational functions with real poles of order at most two -/

section Rational

open CatalanCore.Decay.ComplexContour
open CatalanCore.Uniform.Decay.Polygon (polyI halfP rayInt deform)

variable {ι : Type*} [Fintype ι]

/-- `f(z) = ∑ᵢ (aᵢ/(z - pᵢ) + bᵢ/(z - pᵢ)²)`: partial fractions with real poles of order `≤ 2`. -/
noncomputable def ratF (a b : ι → ℂ) (p : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, (a i / (z - p i) + b i / (z - p i) ^ 2)

/-- The `j`-th derivative of `ratF`. -/
noncomputable def ratDeriv (j : ℕ) (a b : ι → ℂ) (p : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, ((-1) ^ j * (j.factorial : ℂ) * a i / (z - p i) ^ (j + 1) +
        (-1) ^ j * ((j + 1).factorial : ℂ) * b i / (z - p i) ^ (j + 2))

lemma ratF_line (a b : ι → ℂ) (p : ι → ℝ) (v t : ℝ) :
    ratF a b p ((v : ℂ) + t * I) =
      ∑ i, (a i * (1 / lz (v - p i) t) + b i * (1 / lz (v - p i) t ^ 2)) := by
  unfold ratF
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (v : ℂ) + t * I - p i = lz (v - p i) t := by unfold lz; push_cast; ring
  rw [this]; ring

lemma norm_sub_real_ge (z : ℂ) (x : ℝ) : |z.im| ≤ ‖z - x‖ := by
  have := Complex.abs_im_le_norm (z - x)
  simpa using this

/-- Decay of `ratF` off the real axis (needs `∑ aᵢ = 0`). -/
lemma norm_ratF_le (a b : ι → ℂ) (p : ι → ℝ) (ha : ∑ i, a i = 0) {z : ℂ} (hz : z.im ≠ 0) :
    ‖ratF a b p z‖ ≤ (∑ i, (‖a i‖ * |p i| + ‖b i‖)) / z.im ^ 2 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzp : ∀ i, z - p i ≠ 0 := fun i h => hz (by
    have := congrArg Complex.im h; simpa using this)
  have e : ratF a b p z = ∑ i, (a i * p i / ((z - p i) * z) + b i / (z - p i) ^ 2) := by
    unfold ratF
    have h1 : ∑ i, a i / z = 0 := by rw [← Finset.sum_div, ha, zero_div]
    calc ∑ i, (a i / (z - p i) + b i / (z - p i) ^ 2)
        = ∑ i, ((a i / (z - p i) - a i / z) + b i / (z - p i) ^ 2) + ∑ i, a i / z := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [h1, add_zero]
          refine Finset.sum_congr rfl fun i _ => ?_
          have := hzp i
          field_simp
          ring
  rw [e, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hy : 0 < |z.im| := abs_pos.mpr hz
  have h1 : |z.im| ≤ ‖z - p i‖ := norm_sub_real_ge z _
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hn1 : 0 < ‖z - p i‖ := norm_pos_iff.mpr (hzp i)
  have hn2 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hsq : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
  rw [hsq]
  refine (norm_add_le _ _).trans ?_
  rw [add_div]
  refine add_le_add ?_ ?_
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_div_iff₀ (mul_pos hn1 hn2) (by positivity)]
    have : |z.im| ^ 2 ≤ ‖z - p i‖ * ‖z‖ := by rw [sq]; exact mul_le_mul h1 h2 hy.le (by positivity)
    calc ‖a i‖ * |p i| * |z.im| ^ 2 ≤ ‖a i‖ * |p i| * (‖z - p i‖ * ‖z‖) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · rw [norm_div, norm_pow]
    rw [div_le_div_iff₀ (pow_pos hn1 2) (by positivity)]
    have : |z.im| ^ 2 ≤ ‖z - p i‖ ^ 2 := pow_le_pow_left₀ hy.le h1 2
    nlinarith [norm_nonneg (b i)]

end Rational

/-! ### The line integral of one lattice term -/

section Terms

lemma alg_term (w κ A B : ℂ) (hw : w ≠ 0) (j : ℕ) :
    (j.factorial : ℂ) * (A * (κ / w ^ (j + 1)) + B * (-((j + 1 : ℕ) : ℂ) * κ / w ^ (j + 1 + 1))) =
      -κ * ((-1) ^ j * (j.factorial : ℂ) * A / (-w) ^ (j + 1) +
        (-1) ^ j * ((j + 1).factorial : ℂ) * B / (-w) ^ (j + 2)) := by
  have hs : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hs0 : (-1 : ℂ) ^ j ≠ 0 := by simp
  have e1 : (-w) ^ (j + 1) = -((-1 : ℂ) ^ j) * w ^ (j + 1) := by
    rw [neg_pow, pow_succ (-1 : ℂ) j]; ring
  have e2 : (-w) ^ (j + 2) = ((-1 : ℂ) ^ j) * w ^ (j + 2) := by
    rw [neg_pow, pow_add (-1 : ℂ) j 2]; norm_num
  have hf : ((j + 1).factorial : ℂ) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [e1, e2, hf]
  push_cast
  field_simp
  ring

lemma kap_pos {cm : ℝ} (h : 0 < cm) : kap cm = 0 := by
  unfold kap sg; rw [if_pos h]; simp

lemma kap_neg {cm : ℝ} (h : cm < 0) : kap cm = ((2 * Real.pi : ℝ) : ℂ) * I := by
  unfold kap sg; rw [if_neg (not_lt.mpr h.le)]; push_cast; ring

/-- One pole `p < v` against the lattice term `(z + m)^{-(j+1)}`. -/
lemma integral_term {v p : ℝ} (hvm : ∀ n : ℤ, v ≠ n) (hpv : p < v) (j : ℕ) (m : ℤ) (ai bi : ℂ) :
    Integrable (fun t : ℝ => (j.factorial : ℂ) *
        (ai * G (v - p) (v + m) 1 (j + 1) t + bi * G (v - p) (v + m) 2 (j + 1) t)) ∧
      ∫ t : ℝ, (j.factorial : ℂ) *
        (ai * G (v - p) (v + m) 1 (j + 1) t + bi * G (v - p) (v + m) 2 (j + 1) t) =
      if v < -m then -(((2 * Real.pi : ℝ) : ℂ) * I) *
        ((-1) ^ j * (j.factorial : ℂ) * ai / ((((-m : ℤ) : ℝ) : ℂ) - p) ^ (j + 1) +
          (-1) ^ j * ((j + 1).factorial : ℂ) * bi / ((((-m : ℤ) : ℝ) : ℂ) - p) ^ (j + 2))
      else 0 := by
  have hcp : 0 < v - p := by linarith
  have hcm : v + m ≠ 0 := by
    intro h
    exact hvm (-m) (by push_cast; linarith)
  by_cases hmerge : v + m = v - p
  · have hnot : ¬ v < -m := by
      intro h
      have : (-m : ℝ) = p := by linarith
      linarith
    rw [if_neg (by exact_mod_cast hnot)]
    rw [hmerge]
    obtain ⟨h1, h1v⟩ := integral_G_merged hcp.ne' (s := 1) (q := j + 1) (by omega)
    obtain ⟨h2, h2v⟩ := integral_G_merged hcp.ne' (s := 2) (q := j + 1) (by omega)
    refine ⟨((h1.const_mul ai).add (h2.const_mul bi)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_add (h1.const_mul ai) (h2.const_mul bi), integral_const_mul,
      integral_const_mul, h1v, h2v]
    simp
  · have hD : v + m ≠ v - p := hmerge
    obtain ⟨h1, h1v⟩ := integral_G_one hcp hcm hD (j + 1) (by omega)
    obtain ⟨h2, h2v⟩ := integral_G_two hcp hcm hD (j + 1)
    refine ⟨((h1.const_mul ai).add (h2.const_mul bi)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_add (h1.const_mul ai) (h2.const_mul bi), integral_const_mul,
      integral_const_mul, h1v, h2v]
    rcases lt_or_gt_of_ne hcm with hneg | hpos
    · have hv' : v < -m := by
        have : (m : ℝ) < -v := by linarith
        linarith
      rw [if_pos (by exact_mod_cast hv'), kap_neg hneg]
      have hDc : ((v + m - (v - p) : ℝ) : ℂ) = (m : ℂ) + p := by push_cast; ring
      rw [hDc]
      have hne : ((m : ℂ) + p) ≠ 0 := by
        intro h
        apply hD
        have := congrArg Complex.re h
        simp at this
        linarith
      have e1 : ((((-m : ℤ) : ℝ) : ℂ) - p) = -((m : ℂ) + p) := by push_cast; ring
      rw [e1]
      exact alg_term _ _ _ _ hne j
    · rw [if_neg (by
        intro h
        have : (-m : ℝ) > v := by exact_mod_cast h
        linarith), kap_pos hpos]
      simp

end Terms

/-! ### Fubini over the lattice and the line identity -/

section Fubini

open CatalanCore.Decay.ComplexContour

variable {ι : Type*} [Fintype ι]

/-- `∑_m |v + m|^{-(j+1)} < ∞` for `j ≥ 1`. -/
lemma summable_lattice {v : ℝ} (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun m : ℤ => 1 / |v + m| ^ (j + 1)) := by
  have h := CatalanCore.Uniform.Decay.Jet.summable_higherPoleSeries (j + 1) (by omega) (v : ℂ)
  have h2 := (summable_norm_iff.mpr h)
  refine h2.congr fun m => ?_
  rw [norm_div, norm_one, norm_pow]
  have : ‖(v : ℂ) + (m : ℂ)‖ = |v + m| := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  rw [this]

/-- The lattice summand along the line. -/
noncomputable def Fm (j : ℕ) (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (m : ℤ) (t : ℝ) : ℂ :=
  ∑ i, (j.factorial : ℂ) * (a i * G (v - p i) (v + m) 1 (j + 1) t +
    b i * G (v - p i) (v + m) 2 (j + 1) t)

lemma Fm_eq (j : ℕ) (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (m : ℤ) (t : ℝ) :
    Fm j a b p v m t = ratF a b p ((v : ℂ) + t * I) *
      ((j.factorial : ℂ) * (1 / lz (v + m) t ^ (j + 1))) * I := by
  unfold Fm
  rw [ratF_line, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold G
  ring

lemma norm_Fm_le (j : ℕ) (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) {m : ℤ} (hm : v + m ≠ 0) (t : ℝ) :
    ‖Fm j a b p v m t‖ ≤ ‖ratF a b p ((v : ℂ) + t * I)‖ * ((j.factorial : ℝ) / |v + m| ^ (j + 1)) := by
  rw [Fm_eq, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_mul, norm_div, norm_one, norm_pow]
  have h1 : ‖(j.factorial : ℂ)‖ = (j.factorial : ℝ) := by simp
  rw [h1]
  have hn : |v + m| ≤ ‖lz (v + m) t‖ := abs_le_norm_lz' _ _
  have hpos : 0 < |v + m| := abs_pos.mpr hm
  have : 1 / ‖lz (v + m) t‖ ^ (j + 1) ≤ 1 / |v + m| ^ (j + 1) :=
    one_div_le_one_div_of_le (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hn _)
  calc ‖ratF a b p ((v : ℂ) + t * I)‖ * ((j.factorial : ℝ) * (1 / ‖lz (v + m) t‖ ^ (j + 1)))
      ≤ ‖ratF a b p ((v : ℂ) + t * I)‖ * ((j.factorial : ℝ) * (1 / |v + m| ^ (j + 1))) := by
        gcongr
    _ = _ := by ring

lemma integrable_Fm (j : ℕ) (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (hvm : ∀ n : ℤ, v ≠ n)
    (hp : ∀ i, p i < v) (m : ℤ) : Integrable (Fm j a b p v m) := by
  unfold Fm
  exact integrable_finsetSum _ fun i _ => (integral_term (hvm) (hp i) j m (a i) (b i)).1

lemma integral_Fm (j : ℕ) (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (hvm : ∀ n : ℤ, v ≠ n)
    (hp : ∀ i, p i < v) (m : ℤ) :
    ∫ t, Fm j a b p v m t =
      if v < -m then -(((2 * Real.pi : ℝ) : ℂ) * I) *
        ratDeriv j a b p (((-m : ℤ) : ℝ) : ℂ) else 0 := by
  unfold Fm
  rw [integral_finsetSum _ fun i _ => (integral_term hvm (hp i) j m (a i) (b i)).1]
  simp_rw [fun i => (integral_term hvm (hp i) j m (a i) (b i)).2]
  by_cases h : v < -m
  · simp only [if_pos h]
    unfold ratDeriv
    rw [Finset.mul_sum]
  · simp only [if_neg h, Finset.sum_const_zero]

/-- The line integrand is integrable (`∑ aᵢ = 0`, `v ∉ ℤ`, all poles left of `v`). -/
lemma integrable_Lf (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (hv0 : v ≠ 0) (hp : ∀ i, p i < v)
    (ha : ∑ i, a i = 0) : Integrable (fun t : ℝ => ratF a b p ((v : ℂ) + t * I)) := by
  have hcp : ∀ i, v - p i ≠ 0 := fun i => by have := hp i; linarith
  have e : ∀ t : ℝ, ratF a b p ((v : ℂ) + t * I) =
      ∑ i, (a i * (1 / lz (v - p i) t - 1 / lz v t) + b i * (1 / lz (v - p i) t ^ 2)) := by
    intro t
    rw [ratF_line]
    have h1 : ∑ i, a i * (1 / lz v t) = 0 := by rw [← Finset.sum_mul, ha, zero_mul]
    calc ∑ i, (a i * (1 / lz (v - p i) t) + b i * (1 / lz (v - p i) t ^ 2))
        = ∑ i, (a i * (1 / lz (v - p i) t - 1 / lz v t) + b i * (1 / lz (v - p i) t ^ 2))
          + ∑ i, a i * (1 / lz v t) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [h1, add_zero]
  simp_rw [e]
  refine integrable_finsetSum _ fun i _ => Integrable.add ?_ ?_
  · have := integrable_diff_simple (hcp i) hv0
    have h2 := this.const_mul (I⁻¹ * a i)
    refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    have : I⁻¹ * I = 1 := inv_mul_cancel₀ I_ne_zero
    calc I⁻¹ * a i * (I * (1 / lz (v - p i) t) - I * (1 / lz v t))
        = (I⁻¹ * I) * a i * (1 / lz (v - p i) t - 1 / lz v t) := by ring
      _ = _ := by rw [this, one_mul, mul_comm]
  · exact (integrable_inv_pow_lz (hcp i) (by norm_num)).const_mul _

end Fubini

/-! ### The identity on the vertical line -/

section LineId

open CatalanCore.Decay.ComplexContour
open CatalanCore.Uniform.Decay.Jet

lemma sin_pi_line_ne {v : ℝ} (hvm : ∀ n : ℤ, v ≠ n) (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((v : ℂ) + t * I)) ≠ 0 := by
  intro h0
  obtain ⟨a, ha⟩ := Complex.sin_eq_zero_iff.mp h0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : (v : ℂ) + t * I = (a : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [ha]; ring
  have := congrArg Complex.re he
  simp at this
  exact hvm a this

/-- `cotJet (n+1)` is holomorphic off the integers. -/
lemma hasDerivAt_cotJet (n : ℕ) {z : ℂ} (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    HasDerivAt (cotJet (n + 1)) (((n + 1).factorial : ℂ) *
      (-((n + 2 : ℕ) : ℂ) * higherPoleClosed (n + 1) z)) z := by
  have hc : Continuous (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) := by fun_prop
  have hev : cotJet (n + 1) =ᶠ[nhds z] fun w => ((n + 1).factorial : ℂ) * higherPoleClosed n w := by
    filter_upwards [(hc.tendsto z).eventually (isOpen_ne.mem_nhds hz)] with w hw
    exact cotJet_succ n hw
  exact ((hasDerivAt_higherPoleClosed n hz).const_mul _).congr_of_eventuallyEq hev

lemma continuous_cotJet_line {v : ℝ} (hvm : ∀ n : ℤ, v ≠ n) (n : ℕ) :
    Continuous (fun t : ℝ => cotJet (n + 1) ((v : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have h := (hasDerivAt_cotJet n (sin_pi_line_ne hvm t)).continuousAt
  have hc : Continuous (fun t : ℝ => (v : ℂ) + (t : ℂ) * I) := by fun_prop
  exact ContinuousAt.comp (f := fun t : ℝ => (v : ℂ) + (t : ℂ) * I) (g := cotJet (n + 1)) h
    hc.continuousAt

lemma continuous_Lf {ι : Type*} [Fintype ι] (a b : ι → ℂ) (p : ι → ℝ) {v : ℝ}
    (hp : ∀ i, p i < v) : Continuous (fun t : ℝ => ratF a b p ((v : ℂ) + t * I)) := by
  have : (fun t : ℝ => ratF a b p ((v : ℂ) + t * I)) = fun t : ℝ =>
      ∑ i, (a i * (1 / lz (v - p i) t) + b i * (1 / lz (v - p i) t ^ 2)) :=
    funext fun t => ratF_line a b p v t
  rw [this]
  refine continuous_finsetSum _ fun i _ => ?_
  have hne : v - p i ≠ 0 := by have := hp i; linarith
  exact (continuous_const.mul (continuous_const.div (continuous_lz _) (lz_ne_zero hne))).add
    (continuous_const.mul (continuous_const.div ((continuous_lz _).pow 2)
      (fun t => pow_ne_zero _ (lz_ne_zero hne t))))

lemma norm_lattice_le {v : ℝ} (hmne : ∀ m : ℤ, v + m ≠ 0) (t : ℝ) (j : ℕ) (m : ℤ) :
    ‖1 / ((v : ℂ) + t * I + m) ^ j‖ ≤ 1 / |v + m| ^ j := by
  rw [norm_div, norm_one, norm_pow]
  have : |v + m| ≤ ‖(v : ℂ) + t * I + m‖ := by
    have := Complex.abs_re_le_norm ((v : ℂ) + t * I + m)
    simpa using this
  have hpos : 0 < |v + m| := abs_pos.mpr (hmne m)
  exact one_div_le_one_div_of_le (pow_pos hpos _) (pow_le_pow_left₀ hpos.le this _)

lemma ae_ne_zero_real : ∀ᵐ t : ℝ, t ≠ 0 := by
  have h0 : (volume : Measure ℝ) {0} = 0 := Real.volume_singleton
  exact (measure_eq_zero_iff_ae_notMem.mp h0).mono fun t ht => by simpa using ht

variable {ι : Type*} [Fintype ι]

/-- **The line identity**: for `v ∉ ℤ`, poles `pᵢ < v`, `∑ aᵢ = 0` and `j ≥ 1`,
`∫_ℝ f(v+tI) cotJet j (v+tI) I dt = -2πI ∑_{integers B > v} f^{(j)}(B)` (summed over `ℤ`). -/
theorem line_identity (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (hvm : ∀ n : ℤ, v ≠ n)
    (hp : ∀ i, p i < v) (ha : ∑ i, a i = 0) (j : ℕ) (hj : 1 ≤ j) :
    Integrable (fun t : ℝ => ratF a b p ((v : ℂ) + t * I) * cotJet j ((v : ℂ) + t * I) * I) ∧
    ∫ t : ℝ, ratF a b p ((v : ℂ) + t * I) * cotJet j ((v : ℂ) + t * I) * I =
      ∑' m : ℤ, (if v < -m then -(((2 * Real.pi : ℝ) : ℂ) * I) *
        ratDeriv j a b p (((-m : ℤ) : ℝ) : ℂ) else 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hv0 : v ≠ 0 := by simpa using hvm 0
  have hLf := integrable_Lf a b p v hv0 hp ha
  have hmne : ∀ m : ℤ, v + m ≠ 0 := fun m h => hvm (-m) (by push_cast; linarith)
  set S : ℝ := ∑' m : ℤ, 1 / |v + m| ^ (n + 1 + 1) with hS
  have hSs := summable_lattice (v := v) (n + 1) (by omega)
  have hpt : ∀ t : ℝ, t ≠ 0 → ∑' m : ℤ, Fm (n + 1) a b p v m t =
      ratF a b p ((v : ℂ) + t * I) * cotJet (n + 1) ((v : ℂ) + t * I) * I := by
    intro t ht
    have him : ((v : ℂ) + t * I).im ≠ 0 := by simpa using ht
    rw [cotJet_succ_eq_lattice n him]
    have e : ∀ m : ℤ, Fm (n + 1) a b p v m t = ratF a b p ((v : ℂ) + t * I) *
        (((n + 1).factorial : ℂ) * (1 / ((v : ℂ) + t * I + m) ^ (n + 1 + 1))) * I := by
      intro m
      rw [Fm_eq]
      congr 3
      unfold lz; push_cast; ring
    simp_rw [e]
    rw [tsum_mul_right, tsum_mul_left, tsum_mul_left]
  have hnorm : Summable fun m : ℤ => ∫ t, ‖Fm (n + 1) a b p v m t‖ := by
    have hb : ∀ m : ℤ, ∫ t, ‖Fm (n + 1) a b p v m t‖ ≤
        (∫ t : ℝ, ‖ratF a b p ((v : ℂ) + t * I)‖) *
          (((n + 1).factorial : ℝ) / |v + m| ^ (n + 1 + 1)) := by
      intro m
      calc ∫ t, ‖Fm (n + 1) a b p v m t‖
          ≤ ∫ t : ℝ, ‖ratF a b p ((v : ℂ) + t * I)‖ *
              (((n + 1).factorial : ℝ) / |v + m| ^ (n + 1 + 1)) :=
            integral_mono (integrable_Fm (n + 1) a b p v hvm hp m).norm
              (hLf.norm.mul_const _) (fun t => norm_Fm_le (n + 1) a b p v (hmne m) t)
        _ = _ := integral_mul_const _ _
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hb ?_
    refine Summable.mul_left _ ?_
    have := hSs.mul_left ((n + 1).factorial : ℝ)
    refine this.congr fun m => ?_
    ring
  have hint := integral_tsum_of_summable_integral_norm
    (fun m => integrable_Fm (n + 1) a b p v hvm hp m) hnorm
  have hae : ∀ᵐ t : ℝ, ∑' m : ℤ, Fm (n + 1) a b p v m t =
      ratF a b p ((v : ℂ) + t * I) * cotJet (n + 1) ((v : ℂ) + t * I) * I :=
    ae_ne_zero_real.mono fun t ht => hpt t ht
  have hcont : Continuous (fun t : ℝ => ratF a b p ((v : ℂ) + t * I) *
      cotJet (n + 1) ((v : ℂ) + t * I) * I) :=
    ((continuous_Lf a b p hp).mul (continuous_cotJet_line hvm n)).mul continuous_const
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (hLf.norm.mul_const (((n + 1).factorial : ℝ) * S))
      hcont.aestronglyMeasurable ?_
    refine ae_ne_zero_real.mono fun t ht => ?_
    have him : ((v : ℂ) + t * I).im ≠ 0 := by simpa using ht
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, cotJet_succ_eq_lattice n him, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : ‖((n + 1).factorial : ℂ)‖ = ((n + 1).factorial : ℝ) := by simp
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsn : Summable fun m : ℤ => ‖1 / ((v : ℂ) + t * I + m) ^ (n + 1 + 1)‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => norm_lattice_le hmne t _ m) hSs
    exact (norm_tsum_le_tsum_norm hsn).trans
      (Summable.tsum_le_tsum (fun m => norm_lattice_le hmne t _ m) hsn hSs)
  · rw [← integral_congr_ae hae, ← hint]
    exact tsum_congr fun m => integral_Fm (n + 1) a b p v hvm hp m

end LineId

/-! ### The polygon contour identity for rational `f` -/

section Polygon

open CatalanCore.Decay.ComplexContour
open CatalanCore.Uniform.Decay.Jet
open CatalanCore.Uniform.Decay.Polygon (polyI halfP rayInt deform)

variable {ι : Type*} [Fintype ι]

lemma differentiableAt_ratF (a b : ι → ℂ) (p : ι → ℝ) {z : ℂ} (hz : ∀ i, z ≠ p i) :
    DifferentiableAt ℂ (ratF a b p) z := by
  unfold ratF
  refine DifferentiableAt.fun_sum fun i _ => ?_
  have h : z - p i ≠ 0 := sub_ne_zero.mpr (hz i)
  refine DifferentiableAt.add ?_ ?_
  · exact (differentiableAt_const _).div (by fun_prop) h
  · exact (differentiableAt_const _).div (by fun_prop) (pow_ne_zero _ h)

/-- A real `v ∉ ℤ` right of the poles has a pole-free disc. -/
lemma exists_ball (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (hvm : ∀ n : ℤ, v ≠ n) (hp : ∀ i, p i < v) :
    ∃ δ > 0, ∀ z ∈ Metric.ball (v : ℂ) δ,
      Complex.sin ((Real.pi : ℂ) * z) ≠ 0 ∧ ∀ i, z ≠ p i := by
  set U : Set ℂ := {z | Complex.sin ((Real.pi : ℂ) * z) ≠ 0} ∩ ⋂ i, {z | z ≠ (p i : ℂ)} with hU
  have hopen : IsOpen U := by
    refine (isOpen_ne_fun (by fun_prop) continuous_const).inter ?_
    exact isOpen_iInter_of_finite fun i => isOpen_ne
  have hmem : (v : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa using sin_pi_line_ne hvm 0
    · simp only [mem_iInter]
      intro i h
      have : v = p i := by exact_mod_cast h
      linarith [hp i]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  exact ⟨δ, hδ, fun z hz => ⟨(hball hz).1, fun i => by
    have := (hball hz).2
    simp only [mem_iInter] at this
    exact this i⟩⟩

/-- The lattice sum over `ℤ` as a sum over the integers `B > v`, indexed by `ℕ`. -/
lemma tsum_lattice_nat (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (j : ℕ) :
    (∑' m : ℤ, (if v < -(m : ℝ) then -(((2 * Real.pi : ℝ) : ℂ) * I) *
        ratDeriv j a b p (((-m : ℤ) : ℝ) : ℂ) else 0)) =
      -(((2 * Real.pi : ℝ) : ℂ) * I) *
        ∑' k : ℕ, ratDeriv j a b p ((((⌊v⌋ + 1 + k : ℤ) : ℝ)) : ℂ) := by
  set κ : ℂ := ((2 * Real.pi : ℝ) : ℂ) * I with hκ
  set φ : ℤ → ℂ := fun B => if v < (B : ℝ) then -κ * ratDeriv j a b p ((B : ℝ) : ℂ) else 0
    with hφ
  have hre : (∑' m : ℤ, (if v < -(m : ℝ) then -κ * ratDeriv j a b p (((-m : ℤ) : ℝ) : ℂ) else 0))
      = ∑' B : ℤ, φ B := by
    rw [← (Equiv.neg ℤ).tsum_eq φ]
    refine tsum_congr fun m => ?_
    simp only [hφ, Equiv.neg_apply, Int.cast_neg]
  rw [hre]
  have hinj : Function.Injective (fun k : ℕ => ⌊v⌋ + 1 + (k : ℤ)) := by
    intro k l hkl; simpa using hkl
  have hsupp : Function.support φ ⊆ Set.range (fun k : ℕ => ⌊v⌋ + 1 + (k : ℤ)) := by
    intro B hB
    have hvB : v < (B : ℝ) := by
      by_contra hcon; exact hB (by simp [hφ, hcon])
    have : ⌊v⌋ + 1 ≤ B := by
      have := Int.floor_lt.mpr (by exact_mod_cast hvB : v < (B : ℝ))
      omega
    exact ⟨(B - (⌊v⌋ + 1)).toNat, by show ⌊v⌋ + 1 + (((B - (⌊v⌋ + 1)).toNat : ℕ) : ℤ) = B; omega⟩
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hvk : v < ((⌊v⌋ + 1 + (k : ℤ) : ℤ) : ℝ) := by
    have h1 : v < (⌊v⌋ : ℝ) + 1 := Int.lt_floor_add_one v
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    linarith
  simp only [hφ, if_pos hvk]

/-- **LD02, the contour identity** (generic).  For `f = ratF a b p` with real poles `pᵢ < v`
(`v ∉ ℤ`), `∑ aᵢ = 0`, a finite set `J` of jets `≥ 1` with coefficients `c`, and any upper polygon
`v → pts → tail d` with its mirror image,
`∮_Γ f · K_c dz = -2πI ∑_{j ∈ J} c_j ∑_{B ∈ ℤ, B > v} f^{(j)}(B)`,
where `Γ` is the polygon traversed upward (the lower polygon reversed). -/
theorem contour_identity_Kc (a b : ι → ℂ) (p : ι → ℝ) (v : ℝ) (hvm : ∀ n : ℤ, v ≠ n)
    (hp : ∀ i, p i < v) (ha : ∑ i, a i = 0) (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) (c : ℕ → ℂ)
    (pts : List ℂ) (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    polyI (fun z => ratF a b p z * Kc J c z) (v : ℂ) pts d -
      polyI (fun z => ratF a b p z * Kc J c z) (v : ℂ) (pts.map (starRingEnd ℂ))
        (starRingEnd ℂ d) =
      -(((2 * Real.pi : ℝ) : ℂ) * I) *
        ∑ j ∈ J, c j * ∑' k : ℕ, ratDeriv j a b p ((((⌊v⌋ + 1 + k : ℤ) : ℝ)) : ℂ) := by
  set g : ℂ → ℂ := fun z => ratF a b p z * Kc J c z with hg
  obtain ⟨δ, hδ, hball⟩ := exists_ball a b p v hvm hp
  have hKdiff : ∀ z : ℂ, Complex.sin ((Real.pi : ℂ) * z) ≠ 0 → DifferentiableAt ℂ (Kc J c) z := by
    intro z hs
    unfold Kc
    refine DifferentiableAt.fun_sum fun j hj => ?_
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by have := hJ j hj; omega⟩
    exact (differentiableAt_const _).mul (hasDerivAt_cotJet n hs).differentiableAt
  have hdiffAt : ∀ z : ℂ, Complex.sin ((Real.pi : ℂ) * z) ≠ 0 → (∀ i, z ≠ p i) →
      DifferentiableAt ℂ g z := fun z hs hz =>
    (differentiableAt_ratF a b p hz).mul (hKdiff z hs)
  have hdiffH : ∀ σ : ℝ, DifferentiableOn ℂ g (halfP σ) := by
    intro σ z hz
    have him : z.im ≠ 0 := by
      intro h; have : 0 < σ * z.im := hz
      rw [h, mul_zero] at this; exact lt_irrefl _ this
    exact (hdiffAt z (sin_pi_ne_zero_of_im_ne him) (fun i h => him (by
      have := congrArg Complex.im h; simpa using this))).differentiableWithinAt
  have hdiffB : DifferentiableOn ℂ g (Metric.ball (v : ℂ) δ) := fun z hz =>
    (hdiffAt z (hball z hz).1 (hball z hz).2).differentiableWithinAt
  set C : ℝ := ∑ i, (‖a i‖ * |p i| + ‖b i‖) with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => by positivity
  set CJ : ℝ := ∑ j ∈ J, ‖c j‖ * jetConst (j - 1) with hCJ
  have hjc : ∀ n : ℕ, 0 ≤ jetConst n := fun n => mul_nonneg (by positivity)
    (higherPoleK_nonneg n (by norm_num))
  have hCJ0 : 0 ≤ CJ := Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hjc _)
  set K : ℝ := C * CJ with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 hCJ0
  have hdec : ∀ σ : ℝ, |σ| = 1 → ∀ z : ℂ, 1 ≤ σ * z.im → ‖g z‖ ≤ K / (σ * z.im) ^ 2 := by
    intro σ hσ z hz
    have hsq : (σ * z.im) ^ 2 = z.im ^ 2 := by
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hσ with h | h <;> rw [h] <;> ring
    have habs : 1 ≤ |z.im| := by
      calc 1 ≤ σ * z.im := hz
        _ ≤ |σ * z.im| := le_abs_self _
        _ = |z.im| := by rw [abs_mul, hσ, one_mul]
    have him : z.im ≠ 0 := by intro h; rw [h] at habs; simp at habs; linarith
    rw [hsq, hg]
    simp only
    rw [norm_mul]
    have h1 := norm_ratF_le a b p ha him
    have h2 := norm_Kc_le J hJ c habs
    have h3 : Real.exp (-(2 * Real.pi * |z.im|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, abs_nonneg z.im])
    have h4 : ‖Kc J c z‖ ≤ CJ := by
      refine h2.trans ?_
      calc CJ * Real.exp (-(2 * Real.pi * |z.im|)) ≤ CJ * 1 := mul_le_mul_of_nonneg_left h3 hCJ0
        _ = CJ := mul_one _
    have hy2 : 0 < z.im ^ 2 := by positivity
    calc ‖ratF a b p z‖ * ‖Kc J c z‖ ≤ (C / z.im ^ 2) * CJ :=
          mul_le_mul h1 h4 (norm_nonneg _) (div_nonneg hC0 hy2.le)
      _ = K / z.im ^ 2 := by rw [hK]; ring
  have hv : (v : ℂ).im = 0 := Complex.ofReal_im v
  have hup := deform (σ := 1) (v := (v : ℂ)) (f := g) hv hδ (hdiffH 1) hdiffB pts
    (by simpa using hpts) (d := d) (D := I) (by simpa using hd) (by simp) hK0
    (hdec 1 (by simp))
  have hlo := deform (σ := -1) (v := (v : ℂ)) (f := g) hv hδ (hdiffH (-1)) hdiffB
    (pts.map (starRingEnd ℂ)) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
      simpa using hpts w hw) (d := starRingEnd ℂ d) (D := -I) (by simpa using hd) (by simp) hK0
    (hdec (-1) (by simp))
  rw [hup, hlo]
  have hlines : ∀ j ∈ J, Integrable (fun t : ℝ => ratF a b p ((v : ℂ) + t * I) *
        cotJet j ((v : ℂ) + t * I) * I) ∧
      ∫ t : ℝ, ratF a b p ((v : ℂ) + t * I) * cotJet j ((v : ℂ) + t * I) * I =
        -(((2 * Real.pi : ℝ) : ℂ) * I) *
          ∑' k : ℕ, ratDeriv j a b p ((((⌊v⌋ + 1 + k : ℤ) : ℝ)) : ℂ) := by
    intro j hj
    obtain ⟨hint, hval⟩ := line_identity a b p v hvm hp ha j (hJ j hj)
    exact ⟨hint, by rw [hval]; exact tsum_lattice_nat a b p v j⟩
  set h : ℝ → ℂ := fun t => ratF a b p ((v : ℂ) + t * I) * Kc J c ((v : ℂ) + t * I) * I with hh
  have hexp : h = fun t : ℝ => ∑ j ∈ J, c j * (ratF a b p ((v : ℂ) + t * I) *
      cotJet j ((v : ℂ) + t * I) * I) := by
    funext t
    simp only [hh, Kc]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hint : Integrable h := by
    rw [hexp]
    exact integrable_finsetSum _ fun j hj => (hlines j hj).1.const_mul _
  have hval : ∫ t : ℝ, h t = -(((2 * Real.pi : ℝ) : ℂ) * I) *
      ∑ j ∈ J, c j * ∑' k : ℕ, ratDeriv j a b p ((((⌊v⌋ + 1 + k : ℤ) : ℝ)) : ℂ) := by
    rw [hexp, integral_finsetSum _ fun j hj => (hlines j hj).1.const_mul _]
    have e : ∀ j ∈ J, ∫ t : ℝ, c j * (ratF a b p ((v : ℂ) + t * I) *
        cotJet j ((v : ℂ) + t * I) * I) = c j * (-(((2 * Real.pi : ℝ) : ℂ) * I) *
          ∑' k : ℕ, ratDeriv j a b p ((((⌊v⌋ + 1 + k : ℤ) : ℝ)) : ℂ)) := by
      intro j hj
      rw [integral_const_mul, (hlines j hj).2]
    rw [Finset.sum_congr rfl e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hIoi : IntegrableOn h (Set.Ioi 0) := hint.integrableOn
  have hIic : IntegrableOn h (Set.Iic 0) := hint.integrableOn
  have e1 : rayInt g (v : ℂ) I = ∫ u in Set.Ioi (0 : ℝ), h u := by
    unfold rayInt; rfl
  have e2 : rayInt g (v : ℂ) (-I) = -∫ u in Set.Ioi (0 : ℝ), h (-u) := by
    unfold rayInt
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [hg, hh]
    push_cast
    ring_nf
  have e3 : (∫ u in Set.Ioi (0 : ℝ), h (-u)) = ∫ u in Set.Iic (0 : ℝ), h u := by
    have := integral_comp_neg_Ioi (0 : ℝ) h
    simpa using this
  rw [e1, e2, e3, sub_neg_eq_add, add_comm, intervalIntegral.integral_Iic_add_Ioi hIic hIoi, hval]

end Polygon

end CatalanCore.Decay.LineInt
