module

public import CatalanCore.Zeta5.Sum.OuterDefs
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The outer rate `T₀` of CONTENT-THEOREM §2, with its `z`-integrals, equals `y⁻¹`-scaled `Ex`

`T0` is the paper's definition: for `y > 1/3`
`T₀(y) = −G(y) + min(r(y), Z(y)) − 2λ⌊1/y⌋ + Σ_{j=1}^{5} (2λ − j y)₊`, where for `y < 1`
`G(y) = 2y ∫₀^{1/2} Σ_i w_i(z) dz` and `Z(y) = y ∫₀^{1/2} #{i : w_i(z) = 0} dz` with
`ℓ = ⌊x−z⌋ + ⌊x+z⌋ + 1` (`x = 1/y`), `δ(z) = 1_{z < α/y}`, `w_i = min(0, i + 3δ − (ℓ+4)/2)` for
`i < ℓ − 2` and `0` otherwise (`Sq`, `Nq` are the row sum and the zero-row count), and for `y ≥ 1`
`G = 0`, `Z = λ`; `r(y) = min(λ, (1 + 4α − 2y)₊)`.

* `integral_four_regions` : the `z`-integral of a function of `(ℓ, δ)` is a four-region sum, since
  `ℓ` is constant on `z < te` and on `z > te` (`te = min({x}, 1 − {x})`) and `δ` jumps at `ν = αx`.
* `T0_inv` : `T₀(1/x) = x⁻¹ · Ex x` for `0 < x < 3`.
* `integral_inv_comp` : the substitution `y = 1/x`.
-/

open Set MeasureTheory

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Sum

open CatalanCore.Zeta5.Profile

/-- `ℓ(x, z) = ⌊x − z⌋ + ⌊x + z⌋ + 1`. -/
noncomputable def ellR (x z : ℝ) : ℕ := (⌊x - z⌋ + ⌊x + z⌋ + 1).toNat

/-- `δ(z) = 1_{z < α/y}`. -/
noncomputable def dlt (y z : ℝ) : ℕ := if z < (al : ℝ) / y then 1 else 0

/-- `∫₀^{1/2} Σ_i w_i(z) dz`. -/
noncomputable def Gint (y : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..(1 / 2), ((Sq (ellR (1 / y) z) (dlt y z) : ℚ) : ℝ)

/-- `∫₀^{1/2} #{i : w_i(z) = 0} dz`. -/
noncomputable def Zint' (y : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..(1 / 2), ((Nq (ellR (1 / y) z) (dlt y z) : ℚ) : ℝ)

/-- `G(y)`. -/
noncomputable def Gfun (y : ℝ) : ℝ := if y < 1 then 2 * y * Gint y else 0

/-- `Z(y)`. -/
noncomputable def Zfun (y : ℝ) : ℝ := if y < 1 then y * Zint' y else (lam : ℝ)

/-- `r(y) = min(λ, (1 + 4α − 2y)₊)`. -/
noncomputable def rfun (y : ℝ) : ℝ := min (lam : ℝ) (max 0 (1 + 4 * (al : ℝ) - 2 * y))

/-- The outer rate `T₀(y)` of CONTENT-THEOREM §2, for `(s, κ, α, λ) = (5, 6, 3/40, 37/40)`. -/
noncomputable def T0 (y : ℝ) : ℝ :=
  -Gfun y + min (rfun y) (Zfun y) - 2 * (lam : ℝ) * (⌊1 / y⌋ : ℝ)
    + max 0 (2 * (lam : ℝ) - 1 * y) + max 0 (2 * (lam : ℝ) - 2 * y)
    + max 0 (2 * (lam : ℝ) - 3 * y) + max 0 (2 * (lam : ℝ) - 4 * y)
    + max 0 (2 * (lam : ℝ) - 5 * y)

/-! ### Step integrals -/

lemma step_intervalIntegrable (ν a b u v : ℝ) :
    IntervalIntegrable (fun z : ℝ => if z < ν then a else b) volume u v := by
  rcases le_total a b with h | h
  · apply Monotone.intervalIntegrable
    intro s t hst
    by_cases hs : s < ν <;> by_cases ht : t < ν <;> simp [hs, ht, h]
    exact absurd (lt_of_le_of_lt hst ht) hs
  · apply Antitone.intervalIntegrable
    intro s t hst
    by_cases hs : s < ν <;> by_cases ht : t < ν <;> simp [hs, ht, h]
    exact absurd (lt_of_le_of_lt hst ht) hs

lemma step_integral (ν a b t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    ∫ z in (0 : ℝ)..t, (if z < ν then a else b) = a * min ν t + b * (t - min ν t) := by
  rcases le_total t ν with h | h
  · rw [min_eq_right h]
    have : ∫ z in (0 : ℝ)..t, (if z < ν then a else b) = ∫ z in (0 : ℝ)..t, a := by
      apply intervalIntegral.integral_congr_uIoo
      intro z hz
      rw [Set.uIoo_of_le ht] at hz
      simp only [if_pos (lt_of_lt_of_le hz.2 h)]
    rw [this]; simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
  · rw [min_eq_left h]
    have h1 : IntervalIntegrable (fun z : ℝ => if z < ν then a else b) volume 0 ν :=
      step_intervalIntegrable ν a b 0 ν
    have h2 : IntervalIntegrable (fun z : ℝ => if z < ν then a else b) volume ν t :=
      step_intervalIntegrable ν a b ν t
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have e1 : ∫ z in (0 : ℝ)..ν, (if z < ν then a else b) = ∫ z in (0 : ℝ)..ν, a := by
      apply intervalIntegral.integral_congr_uIoo
      intro z hz
      rw [Set.uIoo_of_le hν] at hz
      simp only [if_pos hz.2]
    have e2 : ∫ z in ν..t, (if z < ν then a else b) = ∫ z in ν..t, b := by
      apply intervalIntegral.integral_congr_uIoo
      intro z hz
      rw [Set.uIoo_of_le h] at hz
      simp only [if_neg (not_lt.2 hz.1.le)]
    rw [e1, e2]; simp; ring

/-! ### `ℓ` on the two sides of `te` -/

lemma ell_lt {x z : ℝ} (hz0 : 0 < z) (hz : z < tri x) :
    ⌊x - z⌋ + ⌊x + z⌋ + 1 = 2 * ⌊x⌋ + 1 := by
  have hf : z < Int.fract x := lt_of_lt_of_le hz (min_le_left _ _)
  have hf' : z < 1 - Int.fract x := lt_of_lt_of_le hz (min_le_right _ _)
  have hx : x = ⌊x⌋ + Int.fract x := by unfold Int.fract; ring
  have e1 : ⌊x - z⌋ = ⌊x⌋ := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  have e2 : ⌊x + z⌋ = ⌊x⌋ := by
    rw [Int.floor_eq_iff]
    have := Int.fract_lt_one x
    constructor <;> linarith
  rw [e1, e2]; ring

lemma ell_gt {x z : ℝ} (hz : tri x < z) (hz2 : z < 1 / 2) :
    ⌊x - z⌋ + ⌊x + z⌋ + 1 = if Int.fract x < 1 / 2 then 2 * ⌊x⌋ else 2 * ⌊x⌋ + 2 := by
  have hx : x = ⌊x⌋ + Int.fract x := by unfold Int.fract; ring
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  by_cases hf : Int.fract x < 1 / 2
  · rw [if_pos hf]
    have hz' : Int.fract x < z := by
      have : tri x = Int.fract x := by
        unfold tri; exact min_eq_left (by linarith)
      rwa [this] at hz
    have e1 : ⌊x - z⌋ = ⌊x⌋ - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have e2 : ⌊x + z⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith
    rw [e1, e2]; ring
  · rw [if_neg hf]
    have hf2 : 1 / 2 < Int.fract x := by
      rcases lt_or_eq_of_le (not_lt.1 hf) with h | h
      · exact h
      · exfalso
        have : tri x = 1 / 2 := by
          unfold tri; rw [← h]; norm_num
        rw [this] at hz; linarith
    have hz' : 1 - Int.fract x < z := by
      have : tri x = 1 - Int.fract x := by
        unfold tri; exact min_eq_right (by linarith)
      rwa [this] at hz
    have e1 : ⌊x - z⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith
    have e2 : ⌊x + z⌋ = ⌊x⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [e1, e2]; ring

/-- The `z`-integral of a function of `(ℓ, δ)` is a four-region sum. -/
theorem integral_four_regions (Φ : ℕ → ℕ → ℝ) {x : ℝ} (hx0 : 0 < x) (hx3 : x < 3) :
    ∫ z in (0 : ℝ)..(1 / 2), Φ (ellR x z) (dlt (1 / x) z)
      = Φ (lA x) 1 * min (tri x) ((al : ℝ) * x) + Φ (lA x) 0 * max 0 (tri x - (al : ℝ) * x)
        + Φ (lB x) 1 * max 0 ((al : ℝ) * x - tri x)
        + Φ (lB x) 0 * (1 / 2 - max (tri x) ((al : ℝ) * x)) := by
  have hal : (al : ℝ) = 3 / 40 := rfl
  set ν : ℝ := (al : ℝ) * x with hν
  have hν0 : 0 ≤ ν := by rw [hν, hal]; positivity
  have hν1 : ν < 1 / 2 := by rw [hν, hal]; linarith
  have hte0 : 0 ≤ tri x := tri_nonneg x
  have hte1 : tri x ≤ 1 / 2 := tri_le_half x
  have hdl : ∀ z, dlt (1 / x) z = if z < ν then 1 else 0 := by
    intro z; unfold dlt; rw [hν]; congr 1; simp
  -- cell A: z < te
  set fA : ℝ → ℝ := fun z => if z < ν then Φ (lA x) 1 else Φ (lA x) 0 with hfA
  set fB : ℝ → ℝ := fun z => if z < ν then Φ (lB x) 1 else Φ (lB x) 0 with hfB
  have hA : ∫ z in (0 : ℝ)..tri x, Φ (ellR x z) (dlt (1 / x) z) = ∫ z in (0 : ℝ)..tri x, fA z := by
    apply intervalIntegral.integral_congr_uIoo
    intro z hz
    rw [Set.uIoo_of_le hte0] at hz
    have : ellR x z = lA x := by
      unfold ellR lA; rw [ell_lt hz.1 hz.2]
    simp only [hfA, this, hdl]
    split_ifs <;> rfl
  have hB : ∫ z in tri x..(1 / 2), Φ (ellR x z) (dlt (1 / x) z) = ∫ z in tri x..(1 / 2), fB z := by
    apply intervalIntegral.integral_congr_uIoo
    intro z hz
    rw [Set.uIoo_of_le hte1] at hz
    have : ellR x z = lB x := by
      unfold ellR lB; rw [ell_gt hz.1 hz.2]
      split_ifs <;> rfl
    simp only [hfB, this, hdl]
    split_ifs <;> rfl
  have iA : IntervalIntegrable (fun z => Φ (ellR x z) (dlt (1 / x) z)) volume 0 (tri x) := by
    refine (step_intervalIntegrable ν (Φ (lA x) 1) (Φ (lA x) 0) 0 (tri x)).congr_uIoo ?_
    intro z hz
    rw [Set.uIoo_of_le hte0] at hz
    have : ellR x z = lA x := by
      unfold ellR lA; rw [ell_lt hz.1 hz.2]
    simp only [this, hdl]
    split_ifs <;> rfl
  have iB : IntervalIntegrable (fun z => Φ (ellR x z) (dlt (1 / x) z)) volume (tri x) (1 / 2) := by
    refine (step_intervalIntegrable ν (Φ (lB x) 1) (Φ (lB x) 0) (tri x) (1 / 2)).congr_uIoo ?_
    intro z hz
    rw [Set.uIoo_of_le hte1] at hz
    have : ellR x z = lB x := by
      unfold ellR lB; rw [ell_gt hz.1 hz.2]
      split_ifs <;> rfl
    simp only [this, hdl]
    split_ifs <;> rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals iA iB, hA, hB]
  have jB : IntervalIntegrable fB volume 0 (1 / 2) := step_intervalIntegrable _ _ _ _ _
  have jB' : IntervalIntegrable fB volume 0 (tri x) := step_intervalIntegrable _ _ _ _ _
  have jB'' : IntervalIntegrable fB volume (tri x) (1 / 2) := step_intervalIntegrable _ _ _ _ _
  have hsplit : ∫ z in tri x..(1 / 2), fB z = (∫ z in (0 : ℝ)..(1 / 2), fB z) - ∫ z in (0 : ℝ)..tri x, fB z := by
    rw [← intervalIntegral.integral_add_adjacent_intervals jB' jB'']; ring
  rw [hsplit]
  simp only [hfA, hfB]
  rw [step_integral ν _ _ _ hν0 hte0, step_integral ν _ _ _ hν0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
    step_integral ν _ _ _ hν0 hte0]
  rw [min_eq_left hν1.le]
  rcases le_total (tri x) ν with h | h
  · rw [min_eq_right h, min_eq_left h, max_eq_left (sub_nonpos.2 h), max_eq_right (sub_nonneg.2 h),
      max_eq_right h]
    ring
  · rw [min_eq_left h, min_eq_right h, max_eq_right (sub_nonneg.2 h), max_eq_left (sub_nonpos.2 h),
      max_eq_left h]
    ring

/-! ### The bridge `T₀(1/x) = x⁻¹ · Ex x` -/

lemma Gint_inv {x : ℝ} (hx0 : 0 < x) (hx3 : x < 3) : Gint (1 / x) = Iint x := by
  unfold Gint
  simp only [one_div, inv_inv] at *
  have := integral_four_regions (fun l d => ((Sq l d : ℚ) : ℝ)) hx0 hx3
  simp only [one_div] at this
  unfold Iint
  simpa [one_div] using this

lemma Zint_inv {x : ℝ} (hx0 : 0 < x) (hx3 : x < 3) : Zint' (1 / x) = Zint x := by
  unfold Zint'
  simp only [one_div, inv_inv] at *
  have := integral_four_regions (fun l d => ((Nq l d : ℚ) : ℝ)) hx0 hx3
  simp only [one_div] at this
  unfold Zint
  simpa [one_div] using this

theorem T0_inv {x : ℝ} (hx0 : 0 < x) (hx3 : x < 3) : T0 (1 / x) = (1 / x) * Ex x := by
  have hxi : (0 : ℝ) < 1 / x := by positivity
  have hmul : ∀ a b : ℝ, (1 / x) * min a b = min ((1 / x) * a) ((1 / x) * b) :=
    fun a b => mul_min_of_nonneg a b hxi.le
  have hmulM : ∀ a : ℝ, (1 / x) * max 0 a = max 0 ((1 / x) * a) := by
    intro a; rw [mul_max_of_nonneg _ _ hxi.le]; simp
  have hrx : (1 / x) * rx x = rfun (1 / x) := by
    unfold rx rfun
    rw [hmul, hmulM]
    congr 1
    · field_simp
    · congr 1; field_simp
  have hs : ∀ j : ℝ, (1 / x) * max 0 (2 * (lam : ℝ) * x - j)
      = max 0 (2 * (lam : ℝ) - j * (1 / x)) := by
    intro j; rw [hmulM]; congr 1; field_simp
  have hfl : (⌊1 / (1 / x)⌋ : ℝ) = (⌊x⌋ : ℝ) := by simp
  have hG : (1 / x) * Gx x = Gfun (1 / x) := by
    unfold Gx Gfun
    by_cases h1 : 1 < x
    · have h1' : 1 / x < 1 := by rw [div_lt_one hx0]; exact h1
      rw [if_pos h1, if_pos h1', Gint_inv hx0 hx3]
      field_simp
    · have h1' : ¬ (1 / x < 1) := by rw [div_lt_one hx0]; exact h1
      rw [if_neg h1, if_neg h1']; simp
  have hZ : (1 / x) * Zx x = Zfun (1 / x) := by
    unfold Zx Zfun
    by_cases h1 : 1 < x
    · have h1' : 1 / x < 1 := by rw [div_lt_one hx0]; exact h1
      rw [if_pos h1, if_pos h1', Zint_inv hx0 hx3]
    · have h1' : ¬ (1 / x < 1) := by rw [div_lt_one hx0]; exact h1
      rw [if_neg h1, if_neg h1']
      field_simp
  have hP : (1 / x) * (2 * (lam : ℝ) * x * (⌊x⌋ : ℝ)) = 2 * (lam : ℝ) * (⌊x⌋ : ℝ) := by
    field_simp
  have eEx : (1 / x) * Ex x = -((1 / x) * Gx x) + (1 / x) * min (rx x) (Zx x)
      - 2 * (lam : ℝ) * (⌊x⌋ : ℝ) + (1 / x) * max 0 (2 * (lam : ℝ) * x - 1)
      + (1 / x) * max 0 (2 * (lam : ℝ) * x - 2) + (1 / x) * max 0 (2 * (lam : ℝ) * x - 3)
      + (1 / x) * max 0 (2 * (lam : ℝ) * x - 4) + (1 / x) * max 0 (2 * (lam : ℝ) * x - 5) := by
    unfold Ex
    linear_combination (-1 : ℝ) * hP
  rw [eEx, hmul, hrx, hZ, hG, hs 1, hs 2, hs 3, hs 4, hs 5]
  unfold T0
  rw [hfl]

/-! ### Substitution `y = 1/x` -/

theorem integral_inv_comp (g : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, g (1 / x) / x ^ 2 = ∫ y in (1 / b)..(1 / a), g y := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hle : 1 / b ≤ 1 / a := by rw [one_div, one_div]; exact inv_anti₀ ha hab
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hle]
  have himg : (fun x : ℝ => x⁻¹) '' Ioc a b = Ico b⁻¹ a⁻¹ := by
    ext y
    simp only [mem_image, mem_Ioc, mem_Ico]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      have hx : 0 < x := lt_trans ha h1
      exact ⟨inv_anti₀ hx h2, inv_strictAnti₀ ha h1⟩
    · rintro ⟨h1, h2⟩
      have hy : 0 < y := lt_of_lt_of_le (inv_pos.2 hb) h1
      refine ⟨y⁻¹, ⟨?_, ?_⟩, by simp⟩
      · have := inv_strictAnti₀ hy h2
        simpa using this
      · have := inv_anti₀ (inv_pos.2 hb) h1
        simpa using this
  have key := integral_image_eq_integral_abs_deriv_smul (s := Ioc a b) (f := fun x : ℝ => x⁻¹)
    (f' := fun x => -(x ^ 2)⁻¹) measurableSet_Ioc
    (fun x hx => (hasDerivAt_inv (ne_of_gt (lt_trans ha hx.1))).hasDerivWithinAt)
    inv_injective.injOn g
  rw [himg] at key
  have h1 : ∫ y in Ioc (1 / b) (1 / a), g y = ∫ y in Ico b⁻¹ a⁻¹, g y := by
    rw [one_div, one_div, integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  rw [h1, key]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hx0 : 0 < x := lt_trans ha hx.1
  simp only [abs_neg, smul_eq_mul]
  rw [abs_of_pos (by positivity)]
  field_simp

end CatalanCore.Zeta5.Sum
