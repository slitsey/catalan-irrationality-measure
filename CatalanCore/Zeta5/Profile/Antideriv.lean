module

public import CatalanCore.Zeta5.Profile.Defs
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# ZC21, second half: the antiderivatives `P`, `C`, `D` of the sawtooth `F`

With `g = {αx}`, `f = {x}`, `λ = 37/40`, `α = 3/40`:

* `P = 74 g(1−g) − λ f(1−f)`,
* `C = (74/α) G₀(g) − λ G₀(f)`, `G₀(v) = v²/2 − v³/3 − v/6`,
* `D = −74 B₄(g)/(12α²) + λ B₄(f)/12`, `B₄(v) = v²(1−v)² − 1/30`.

They are continuous, and off the countable set `ℤ ∪ α⁻¹ℤ` they satisfy
`P′ = F + λ`, `C′ = P − P̄`, `D′ = C` with `P̄ = 2923/240`.
-/

open Set MeasureTheory

namespace CatalanCore.Zeta5.Profile

/-- `G₀(v) = v²/2 − v³/3 − v/6`. -/
noncomputable def G0 (v : ℝ) : ℝ := v ^ 2 / 2 - v ^ 3 / 3 - v / 6

/-- `B₄(v) = v²(1−v)² − 1/30` (Bernoulli polynomial on `[0,1]`). -/
noncomputable def B4 (v : ℝ) : ℝ := v ^ 2 * (1 - v) ^ 2 - 1 / 30

/-- `P̄ = 2923/240`. -/
noncomputable def Pbar : ℝ := 2923 / 240

/-- `P`. -/
noncomputable def Pp (x : ℝ) : ℝ :=
  74 * (Int.fract (al * x) * (1 - Int.fract (al * x))) - lam * (Int.fract x * (1 - Int.fract x))

/-- `C`. -/
noncomputable def Cc (x : ℝ) : ℝ := 74 / al * G0 (Int.fract (al * x)) - lam * G0 (Int.fract x)

/-- `D`. -/
noncomputable def Dd (x : ℝ) : ℝ :=
  -74 * B4 (Int.fract (al * x)) / (12 * al ^ 2) + lam * B4 (Int.fract x) / 12

/-- The exceptional set `ℤ ∪ α⁻¹ ℤ`. -/
def exc : Set ℝ := (Set.range (fun n : ℤ => (n : ℝ))) ∪ (Set.range (fun n : ℤ => (n : ℝ) / al))

lemma exc_countable : exc.Countable :=
  (Set.countable_range _).union (Set.countable_range _)

lemma al_pos : (0 : ℝ) < al := by unfold al; norm_num

lemma not_exc {x : ℝ} (hx : x ∉ exc) : (∀ n : ℤ, x ≠ n) ∧ (∀ n : ℤ, al * x ≠ n) := by
  constructor
  · intro n h; exact hx (Or.inl ⟨n, h.symm⟩)
  · intro n h
    refine hx (Or.inr ⟨n, ?_⟩)
    have := al_pos.ne'
    show (n : ℝ) / al = x
    rw [div_eq_iff this]; linarith

lemma hasDerivAt_fract {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : HasDerivAt Int.fract (1 : ℝ) x := by
  have hev : ∀ᶠ y in nhds x, Int.fract y = y - (⌊x⌋ : ℝ) := by
    have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun h => hx ⌊x⌋ h.symm)
    have hlt2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    filter_upwards [Ioo_mem_nhds hlt hlt2] with y hy
    have : ⌊y⌋ = ⌊x⌋ := by
      rw [Int.floor_eq_iff]; exact ⟨hy.1.le, hy.2⟩
    simp [Int.fract, this]
  have h1 : HasDerivAt (fun y : ℝ => y - (⌊x⌋ : ℝ)) 1 x := (hasDerivAt_id x).sub_const _
  exact h1.congr_of_eventuallyEq hev

lemma hasDerivAt_fract_al {x : ℝ} (hx : ∀ n : ℤ, al * x ≠ n) :
    HasDerivAt (fun y : ℝ => Int.fract (al * y)) al x := by
  have h := (hasDerivAt_fract hx).comp x ((hasDerivAt_id x).const_mul al)
  exact h.congr_deriv (by simp)

lemma continuous_comp_fract_poly {φ : ℝ → ℝ} (hφ : Continuous φ) (h01 : φ 0 = φ 1) :
    Continuous (fun x : ℝ => φ (Int.fract x)) :=
  (hφ.continuousOn.comp_fract'' h01 : Continuous (φ ∘ Int.fract))

lemma continuous_comp_fract_al {φ : ℝ → ℝ} (hφ : Continuous φ) (h01 : φ 0 = φ 1) :
    Continuous (fun x : ℝ => φ (Int.fract (al * x))) :=
  (continuous_comp_fract_poly hφ h01).comp (continuous_const.mul continuous_id)

theorem continuous_Pp : Continuous Pp := by
  have h1 := continuous_comp_fract_al (φ := fun v => 74 * (v * (1 - v))) (by fun_prop) (by norm_num)
  have h2 := continuous_comp_fract_poly (φ := fun v => lam * (v * (1 - v))) (by fun_prop) (by norm_num)
  have := h1.sub h2
  unfold Pp; convert this using 1

theorem continuous_Cc : Continuous Cc := by
  have h1 := continuous_comp_fract_al (φ := fun v => 74 / al * G0 v) (by unfold G0; fun_prop)
    (by unfold G0; norm_num)
  have h2 := continuous_comp_fract_poly (φ := fun v => lam * G0 v) (by unfold G0; fun_prop)
    (by unfold G0; norm_num)
  have := h1.sub h2
  unfold Cc; convert this using 1

theorem continuous_Dd : Continuous Dd := by
  have h1 := continuous_comp_fract_al (φ := fun v => -74 * B4 v / (12 * al ^ 2))
    (by unfold B4; fun_prop) (by unfold B4; norm_num)
  have h2 := continuous_comp_fract_poly (φ := fun v => lam * B4 v / 12)
    (by unfold B4; fun_prop) (by unfold B4; norm_num)
  have := h1.add h2
  unfold Dd; convert this using 1

attribute [fun_prop] continuous_Pp continuous_Cc continuous_Dd

/-- `P′ = F + λ` off `exc`. -/
theorem hasDerivAt_Pp {x : ℝ} (hx : x ∉ exc) : HasDerivAt Pp (Fs x + lam) x := by
  obtain ⟨h1, h2⟩ := not_exc hx
  have hf := hasDerivAt_fract h1
  have hg := hasDerivAt_fract_al h2
  have := ((hg.mul (HasDerivAt.const_sub 1 hg)).const_mul 74).sub
    ((hf.mul (HasDerivAt.const_sub 1 hf)).const_mul lam)
  unfold Pp
  refine this.congr_deriv ?_
  unfold Fs lam al; ring

lemma dG0 (v : ℝ) : HasDerivAt G0 (v - v ^ 2 - 1 / 6) v := by
  have := (((hasDerivAt_pow 2 v).div_const 2).sub ((hasDerivAt_pow 3 v).div_const 3)).sub
    ((hasDerivAt_id v).div_const 6)
  unfold G0
  refine this.congr_deriv ?_
  simp

lemma dB4 (v : ℝ) : HasDerivAt B4 (4 * v ^ 3 - 6 * v ^ 2 + 2 * v) v := by
  have := ((hasDerivAt_pow 2 v).mul ((HasDerivAt.const_sub 1 (hasDerivAt_id v)).pow 2)).sub_const
    (1 / 30)
  unfold B4
  refine this.congr_deriv ?_
  simp; ring

/-- `C′ = P − P̄` off `exc`. -/
theorem hasDerivAt_Cc {x : ℝ} (hx : x ∉ exc) : HasDerivAt Cc (Pp x - Pbar) x := by
  obtain ⟨h1, h2⟩ := not_exc hx
  have hf := hasDerivAt_fract h1
  have hg := hasDerivAt_fract_al h2
  have hGg := (dG0 (Int.fract (al * x))).comp x hg
  have hGf := (dG0 (Int.fract x)).comp x hf
  have := (hGg.const_mul (74 / al)).sub (hGf.const_mul lam)
  unfold Cc
  refine this.congr_deriv ?_
  have hal := al_pos.ne'
  unfold Pp Pbar lam
  field_simp
  unfold al; ring

/-- `D′ = C` off `exc`. -/
theorem hasDerivAt_Dd {x : ℝ} (hx : x ∉ exc) : HasDerivAt Dd (Cc x) x := by
  obtain ⟨h1, h2⟩ := not_exc hx
  have hf := hasDerivAt_fract h1
  have hg := hasDerivAt_fract_al h2
  have hBg := (dB4 (Int.fract (al * x))).comp x hg
  have hBf := (dB4 (Int.fract x)).comp x hf
  have := ((hBg.const_mul (-74)).div_const (12 * al ^ 2)).add ((hBf.const_mul lam).div_const 12)
  unfold Dd
  refine this.congr_deriv ?_
  have hal := al_pos.ne'
  unfold Cc G0
  field_simp
  unfold lam al; ring

lemma B4_bounds {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) : -1 / 30 ≤ B4 v ∧ B4 v ≤ 7 / 240 := by
  unfold B4
  constructor
  · nlinarith [sq_nonneg (v * (1 - v))]
  · have hw0 : 0 ≤ v * (1 - v) := mul_nonneg h0 (sub_nonneg.2 h1.le)
    have hw1 : v * (1 - v) ≤ 1 / 4 := by nlinarith [sq_nonneg (v - 1 / 2)]
    have : v ^ 2 * (1 - v) ^ 2 = (v * (1 - v)) ^ 2 := by ring
    rw [this]; nlinarith

/-- `D ≤ D₊ = 74/(360 α²) + 7λ/2880`. -/
theorem Dd_le (x : ℝ) : Dd x ≤ 74 / (360 * (al : ℝ) ^ 2) + 7 * (lam : ℝ) / 2880 := by
  have hb1 := B4_bounds (Int.fract_nonneg (al * x)) (Int.fract_lt_one (al * x))
  have hb2 := B4_bounds (Int.fract_nonneg x) (Int.fract_lt_one x)
  have hal : (0 : ℝ) < al ^ 2 := by have := al_pos; positivity
  have hl : (0 : ℝ) < lam := by unfold lam; norm_num
  unfold Dd
  have e1 : -74 * B4 (Int.fract (al * x)) / (12 * al ^ 2) ≤ 74 / (360 * al ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hb1.1]
  have e2 : lam * B4 (Int.fract x) / 12 ≤ 7 * lam / 2880 := by
    nlinarith [hb2.2]
  linarith

lemma G0_abs {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : |G0 v| ≤ 1 := by
  unfold G0
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

lemma B4_abs {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) : |B4 v| ≤ 1 := by
  have := B4_bounds h0 h1
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem Pp_abs (x : ℝ) : |Pp x| ≤ 20 := by
  have a0 := Int.fract_nonneg (al * x); have a1 := Int.fract_lt_one (al * x)
  have b0 := Int.fract_nonneg x; have b1 := Int.fract_lt_one x
  have hl : (lam : ℝ) = 37 / 40 := rfl
  unfold Pp
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg a0 (sub_nonneg.2 a1.le),
    mul_nonneg b0 (sub_nonneg.2 b1.le), sq_nonneg (Int.fract (al * x) - 1 / 2), sq_nonneg (Int.fract x - 1 / 2)]

theorem Cc_abs (x : ℝ) : |Cc x| ≤ 2000 := by
  have a0 := Int.fract_nonneg (al * x); have a1 := Int.fract_lt_one (al * x)
  have b0 := Int.fract_nonneg x; have b1 := Int.fract_lt_one x
  have ga := G0_abs a0 a1.le; have gb := G0_abs b0 b1.le
  have hl : (lam : ℝ) = 37 / 40 := rfl
  have hal : (al : ℝ) = 3 / 40 := rfl
  unfold Cc
  rw [abs_le] at *
  generalize G0 (Int.fract (al * x)) = u at *
  generalize G0 (Int.fract x) = w at *
  rw [hal, hl]
  constructor <;> nlinarith [ga.1, ga.2, gb.1, gb.2]

theorem Dd_abs (x : ℝ) : |Dd x| ≤ 2000 := by
  have a0 := Int.fract_nonneg (al * x); have a1 := Int.fract_lt_one (al * x)
  have b0 := Int.fract_nonneg x; have b1 := Int.fract_lt_one x
  have ga := B4_abs a0 a1; have gb := B4_abs b0 b1
  have hl : (lam : ℝ) = 37 / 40 := rfl
  have hal : (al : ℝ) = 3 / 40 := rfl
  unfold Dd
  rw [abs_le] at *
  generalize B4 (Int.fract (al * x)) = u at *
  generalize B4 (Int.fract x) = w at *
  rw [hal, hl]
  have e : (-74 * u / (12 * (3 / 40 : ℝ) ^ 2)) = -(74 * 1600 / 108) * u := by ring
  rw [e]
  constructor <;> nlinarith [ga.1, ga.2, gb.1, gb.2]

theorem Fs_abs (x : ℝ) : |Fs x| ≤ 20 := by
  have a0 := Int.fract_nonneg (al * x); have a1 := Int.fract_lt_one (al * x)
  have b0 := Int.fract_nonneg x; have b1 := Int.fract_lt_one x
  have hl : (lam : ℝ) = 37 / 40 := rfl
  have hal : (al : ℝ) = 3 / 40 := rfl
  unfold Fs
  rw [abs_le]; rw [hl]
  constructor <;> nlinarith

theorem measurable_Fs : Measurable (Fs : ℝ → ℝ) := by
  unfold Fs; fun_prop

theorem measurable_Qc : Measurable (Qc : ℝ → ℝ) := by
  have : Measurable (tri : ℝ → ℝ) := by unfold tri; fun_prop
  have hsg : Measurable (sg : ℝ → ℝ) := by
    unfold sg
    exact Measurable.ite (measurableSet_lt measurable_fract measurable_const)
      measurable_const measurable_const
  unfold Qc Q1 Q2
  have h3 : Measurable (fun x : ℝ => tri (al * x)) := this.comp (by fun_prop)
  have h4 : Measurable (fun x : ℝ => sg (al * x)) := hsg.comp (by fun_prop)
  fun_prop

theorem measurable_Rg : Measurable (Rg : ℝ → ℝ) := by
  unfold Rg
  exact (measurable_id.mul measurable_Fs).add measurable_Qc

end CatalanCore.Zeta5.Profile
