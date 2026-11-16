module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CatalanCore.Zeta5.Frames.ClassSum
public import CatalanCore.Zeta5.Profile.Defs

@[expose] public section

/-!
# ZC17 (first module): the profile `Γ`, `N₀`, and the identity `-Γ - N₀ = R`

At the design `(s, κ, α, λ) = (5, 6, 3/40, 37/40)`, `H = 23/20` (CONTENT-THEOREM §2):

* `Apery.CostIn.Gam x` is `Γ(x) = ∫₀^{1/2} (T-b)(T+b-ℓ-5) dz + u(2T-q-5) + (u-v)₊`, with
  `ℓ = ℓ(x,z) = ⌊x-z⌋+⌊x+z⌋+1`, `b = 6ℓ(αx,z)/2`, `T = ⌊2Hx⌋`, `u = Hx-T/2`, `q = ⌊2x⌋`, `v = x-q/2`.
* `Apery.CostIn.N0 x` is `N₀(x) = 2λx⌊x⌋ - 2κλx⌊αx⌋ - 2J(λx)`.
* **`neg_Gam_sub_N0`**: `-Γ(x) - N₀(x) = Rg x` (the closed profile of `Profile.Defs`), for every real `x`.
* `Apery.CostIn.Phi x T e` is the allocation model: the class-sum integral with base dimension `T`
  plus `e` (in units of `p`) extra rows on the classes of largest `ℓ_K`; `Gam_eq_Phi : Γ x = Φ x ⌊2Hx⌋ u`,
  `Phi_lip` (Lipschitz in `e`), `Phi_cont` (`Φ(T+1, 0) = Φ(T, 1/2)`: allocation continuity).
* `integral_step`: `∫₀^{1/2} h(a_f(z), a_g(z)) dz = Cint h f g` (the continuous limit of
  `ClassSum.class_sum_approx`); `Cint_eval`: closed form of `Cint` in `min(f,1-f)`, `min(g,1-g)`.
-/

open Finset MeasureTheory Set

namespace Apery.CostIn

/-- `ℓ(x,z) = ⌊x - z⌋ + ⌊x + z⌋ + 1`. -/
noncomputable def ell (x z : ℝ) : ℝ := ((⌊x - z⌋ : ℤ) : ℝ) + ((⌊x + z⌋ : ℤ) : ℝ) + 1

/-- The class count `[z ≤ f] + [1 - f ≤ z]`. -/
noncomputable def acnt (f z : ℝ) : ℕ := (if z ≤ f then 1 else 0) + (if 1 - f ≤ z then 1 else 0)

lemma floor_sub_z (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    ⌊x - z⌋ = ⌊x⌋ - (if z ≤ Int.fract x then 0 else 1) := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx := Int.floor_add_fract x
  split_ifs with h
  · rw [sub_zero, Int.floor_eq_iff]; constructor <;> linarith
  · push Not at h
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

lemma floor_add_z (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    ⌊x + z⌋ = ⌊x⌋ + (if 1 - Int.fract x ≤ z then 1 else 0) := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx := Int.floor_add_fract x
  split_ifs with h
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · push Not at h
    rw [add_zero, Int.floor_eq_iff]; constructor <;> linarith

lemma ell_eq (x z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) :
    ell x z = 2 * (⌊x⌋ : ℝ) + (acnt (Int.fract x) z : ℝ) := by
  unfold ell acnt
  rw [floor_sub_z x z hz0 hz1, floor_add_z x z hz0 hz1]
  split_ifs <;> push_cast <;> ring

/-- The indicator of `[cvLo f i, cvHi f i]`. -/
noncomputable def ind (f : ℝ) (i : Fin 3) (z : ℝ) : ℝ :=
  Set.indicator (Set.Icc (cvLo f i) (cvHi f i)) (fun _ => (1 : ℝ)) z

lemma expand_one_real {f z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (h : ℕ → ℝ) :
    h (acnt f z) = ∑ i, bcoef h i * ind f i z := by
  simp only [Fin.sum_univ_three, bcoef, ind, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, acnt, Set.indicator, Set.mem_Icc]
  have hz1' : z ≤ (2 : ℝ)⁻¹ := by simpa using hz1
  by_cases h1 : z ≤ f <;> by_cases h2 : 1 - f ≤ z
  · simp [h1, h2, hz0, hz1']
  · simp [h1, h2, hz0, hz1']
  · exfalso; push Not at h1; linarith
  · simp [h1, h2, hz0, hz1']

lemma expand_two_real {f g z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (h : ℕ → ℕ → ℝ) :
    h (acnt f z) (acnt g z) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * (ind f i z * ind g j z) := by
  rw [expand_one_real hz0 hz1 (fun a => h a (acnt g z))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ a, h a (acnt g z) = ∑ j, bcoef (fun b => h a b) j * ind g j z :=
    fun a => expand_one_real hz0 hz1 (fun b => h a b)
  simp only [e]
  simp only [bcoef, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fin_cases i <;> simp <;> ring

lemma integral_indicator_Icc (a b : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), Set.indicator (Set.Icc a b) (fun _ => (1 : ℝ)) z =
      max 0 (min b (1 / 2) - max a 0) := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.setIntegral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one, MeasureTheory.Measure.real]
  have hsub1 : Set.Ioo (max a 0) (min b (1 / 2)) ⊆ Set.Ioc 0 (1 / 2) ∩ Set.Icc a b := by
    intro z hz
    simp only [Set.mem_Ioo, lt_min_iff, max_lt_iff] at hz
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
    refine ⟨⟨hz.1.2, hz.2.2.le⟩, hz.1.1.le, hz.2.1.le⟩
  have hsub2 : Set.Ioc 0 (1 / 2) ∩ Set.Icc a b ⊆ Set.Icc (max a 0) (min b (1 / 2)) := by
    intro z hz
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc] at hz
    simp only [Set.mem_Icc, max_le_iff, le_min_iff]
    refine ⟨⟨hz.2.1, hz.1.1.le⟩, hz.2.2, hz.1.2⟩
  have h1 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub1
  have h2 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hsub2
  rw [Real.volume_Ioo] at h1
  rw [Real.volume_Icc] at h2
  have h3 : MeasureTheory.volume (Set.Ioc (0 : ℝ) (1 / 2) ∩ Set.Icc a b) =
      ENNReal.ofReal (min b (1 / 2) - max a 0) := le_antisymm h2 h1
  rw [h3, ENNReal.toReal_ofReal']
  rw [max_comm]


/-- The continuous class sum `∑_{ij} coef_{ij} · ccount`, the limit of `class_sum_approx`. -/
noncomputable def Cint (h : ℕ → ℕ → ℝ) (f g : ℝ) : ℝ :=
  ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * ccount f g i j

lemma ind_mul (f g : ℝ) (i j : Fin 3) (z : ℝ) :
    ind f i z * ind g j z = Set.indicator
      (Set.Icc (max (cvLo f i) (cvLo g j)) (min (cvHi f i) (cvHi g j))) (fun _ => (1 : ℝ)) z := by
  unfold ind
  simp only [Set.indicator, Set.mem_Icc, max_le_iff, le_min_iff]
  split_ifs <;> simp_all

lemma integrable_ind (c a b : ℝ) :
    Integrable (fun z => c * Set.indicator (Set.Icc a b) (fun _ => (1 : ℝ)) z) := by
  refine Integrable.const_mul ?_ c
  exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))

lemma integral_step (f g : ℝ) (h : ℕ → ℕ → ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), h (acnt f z) (acnt g z) = Cint h f g := by
  have hcongr : ∫ z in (0 : ℝ)..(1 / 2), h (acnt f z) (acnt g z) =
      ∫ z in (0 : ℝ)..(1 / 2), ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        Set.indicator (Set.Icc (max (cvLo f i) (cvLo g j)) (min (cvHi f i) (cvHi g j)))
          (fun _ => (1 : ℝ)) z := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by norm_num)] at hz
    simp only
    rw [expand_two_real hz.1 hz.2 h]
    simp only [ind_mul]
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_indicator_Icc]
      rfl
    · intro j _
      exact (integrable_ind _ _ _).intervalIntegrable
  · intro i _
    exact (integrable_finsetSum _ fun j _ => integrable_ind _ _ _).intervalIntegrable


section cc
variable {f g : ℝ}

/-- Generic evaluation of one `ccount` by cases. -/
lemma ccount_eq_of (f g : ℝ) (i j : Fin 3) (v : ℝ)
    (h : max 0 (min (min (cvHi f i) (cvHi g j)) (1 / 2) - max (max (cvLo f i) (cvLo g j)) 0) = v) :
    ccount f g i j = v := h

lemma cc_ff (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hf : f < 1 / 2) (hg : g < 1 / 2) :
    ccount f g 0 0 = 1 / 2 ∧ ccount f g 0 1 = g ∧ ccount f g 0 2 = 0 ∧
    ccount f g 1 0 = f ∧ ccount f g 1 1 = min f g ∧ ccount f g 1 2 = 0 ∧
    ccount f g 2 0 = 0 ∧ ccount f g 2 1 = 0 ∧ ccount f g 2 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply ccount_eq_of <;>
    simp only [cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, min_def, max_def] <;>
    split_ifs <;> first | (exfalso; linarith) | linarith


lemma cc_fg (hf0 : 0 ≤ f) (hg1 : g < 1) (hf : f < 1 / 2) (hg : 1 / 2 ≤ g) :
    ccount f g 0 0 = 1 / 2 ∧ ccount f g 0 1 = 1 / 2 ∧ ccount f g 0 2 = g - 1 / 2 ∧
    ccount f g 1 0 = f ∧ ccount f g 1 1 = f ∧ ccount f g 1 2 = max 0 (f + g - 1) ∧
    ccount f g 2 0 = 0 ∧ ccount f g 2 1 = 0 ∧ ccount f g 2 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply ccount_eq_of <;>
    simp only [cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, min_def, max_def] <;>
    split_ifs <;> first | (exfalso; linarith) | linarith

lemma cc_gf (hg0 : 0 ≤ g) (hf1 : f < 1) (hf : 1 / 2 ≤ f) (hg : g < 1 / 2) :
    ccount f g 0 0 = 1 / 2 ∧ ccount f g 0 1 = g ∧ ccount f g 0 2 = 0 ∧
    ccount f g 1 0 = 1 / 2 ∧ ccount f g 1 1 = g ∧ ccount f g 1 2 = 0 ∧
    ccount f g 2 0 = f - 1 / 2 ∧ ccount f g 2 1 = max 0 (f + g - 1) ∧ ccount f g 2 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply ccount_eq_of <;>
    simp only [cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, min_def, max_def] <;>
    split_ifs <;> first | (exfalso; linarith) | linarith

lemma cc_gg (hf1 : f < 1) (hg1 : g < 1) (hf : 1 / 2 ≤ f) (hg : 1 / 2 ≤ g) :
    ccount f g 0 0 = 1 / 2 ∧ ccount f g 0 1 = 1 / 2 ∧ ccount f g 0 2 = g - 1 / 2 ∧
    ccount f g 1 0 = 1 / 2 ∧ ccount f g 1 1 = 1 / 2 ∧ ccount f g 1 2 = g - 1 / 2 ∧
    ccount f g 2 0 = f - 1 / 2 ∧ ccount f g 2 1 = f - 1 / 2 ∧ ccount f g 2 2 = min f g - 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply ccount_eq_of <;>
    simp only [cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, min_def, max_def] <;>
    split_ifs <;> first | (exfalso; linarith) | linarith

end cc

lemma Cint_eval (h : ℕ → ℕ → ℝ) {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g)
    (hg1 : g < 1) :
    Cint h f g =
      (1 / 2) * h 1 1
      + (1 / 2 - min f (1 - f)) * ((if f < 1 / 2 then h 0 1 else h 2 1) - h 1 1)
      + (1 / 2 - min g (1 - g)) * ((if g < 1 / 2 then h 1 0 else h 1 2) - h 1 1)
      + (1 / 2 - max (min f (1 - f)) (min g (1 - g))) *
        ((if f < 1 / 2 then (if g < 1 / 2 then h 0 0 else h 0 2)
            else (if g < 1 / 2 then h 2 0 else h 2 2))
          - (if f < 1 / 2 then h 0 1 else h 2 1) - (if g < 1 / 2 then h 1 0 else h 1 2) + h 1 1) := by
  unfold Cint
  simp only [Fin.sum_univ_three, bcoef, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rcases lt_or_ge f (1 / 2) with hf | hf <;> rcases lt_or_ge g (1 / 2) with hg | hg
  · obtain ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩ := cc_ff hf0 hg0 hf hg
    rw [c00, c01, c02, c10, c11, c12, c20, c21, c22]
    rw [min_eq_left (by linarith : f ≤ 1 - f), min_eq_left (by linarith : g ≤ 1 - g)]
    simp only [hf, hg, ↓reduceIte]
    rcases le_total f g with hfg | hfg
    · rw [min_eq_left hfg, max_eq_right hfg]; ring
    · rw [min_eq_right hfg, max_eq_left hfg]; ring
  · obtain ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩ := cc_fg hf0 hg1 hf hg
    rw [c00, c01, c02, c10, c11, c12, c20, c21, c22]
    rw [min_eq_left (by linarith : f ≤ 1 - f), min_eq_right (by linarith : 1 - g ≤ g)]
    simp only [hf, not_lt.mpr hg, ↓reduceIte]
    rcases le_total (f + g) 1 with hs | hs
    · rw [max_eq_left (by linarith : 0 ≥ f + g - 1), max_eq_right (by linarith : f ≤ 1 - g)]; ring
    · rw [max_eq_right (by linarith : 0 ≤ f + g - 1), max_eq_left (by linarith : 1 - g ≤ f)]; ring
  · obtain ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩ := cc_gf hg0 hf1 hf hg
    rw [c00, c01, c02, c10, c11, c12, c20, c21, c22]
    rw [min_eq_right (by linarith : 1 - f ≤ f), min_eq_left (by linarith : g ≤ 1 - g)]
    simp only [not_lt.mpr hf, hg, ↓reduceIte]
    rcases le_total (f + g) 1 with hs | hs
    · rw [max_eq_left (by linarith : 0 ≥ f + g - 1), max_eq_left (by linarith : g ≤ 1 - f)]; ring
    · rw [max_eq_right (by linarith : 0 ≤ f + g - 1), max_eq_right (by linarith : 1 - f ≤ g)]; ring
  · obtain ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩ := cc_gg hf1 hg1 hf hg
    rw [c00, c01, c02, c10, c11, c12, c20, c21, c22]
    rw [min_eq_right (by linarith : 1 - f ≤ f), min_eq_right (by linarith : 1 - g ≤ g)]
    simp only [not_lt.mpr hf, not_lt.mpr hg, ↓reduceIte]
    rcases le_total f g with hfg | hfg
    · rw [min_eq_left hfg, max_eq_left (by linarith : 1 - g ≤ 1 - f)]; ring
    · rw [min_eq_right hfg, max_eq_right (by linarith : 1 - f ≤ 1 - g)]; ring


/-! ### The profile objects of CONTENT-THEOREM §2 -/

/-- `T = ⌊2Hx⌋` with `H = 23/20`. -/
noncomputable def Tf (x : ℝ) : ℤ := ⌊2 * (23 / 20) * x⌋
/-- `u = Hx - T/2`. -/
noncomputable def uf (x : ℝ) : ℝ := 23 / 20 * x - (Tf x : ℝ) / 2
/-- `q = ⌊2x⌋`. -/
noncomputable def qf (x : ℝ) : ℤ := ⌊2 * x⌋
/-- `v = x - q/2`. -/
noncomputable def vf (x : ℝ) : ℝ := x - (qf x : ℝ) / 2

/-- The integrand `(T - b)(T + b - ℓ - s)` with `b = κ ℓ(αx, z)/2`, `κ = 6`, `s = 5`. -/
noncomputable def GamInt (x T z : ℝ) : ℝ :=
  (T - 6 * ell (3 / 40 * x) z / 2) * (T + 6 * ell (3 / 40 * x) z / 2 - ell x z - 5)

/-- **`Γ(x)`** of CONTENT-THEOREM §2 at `(s, κ, α, λ) = (5, 6, 3/40, 37/40)`:
`∫₀^{1/2} (T-b)(T+b-ℓ-s) dz + u (2T - q - s) + (u - v)₊`. -/
noncomputable def Gam (x : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(1 / 2), GamInt x (Tf x) z) + uf x * (2 * (Tf x : ℝ) - (qf x : ℝ) - 5)
    + max (uf x - vf x) 0

/-- `J(w) = m w - m (m+1)/4`, `m = ⌊2w⌋`. -/
noncomputable def Jf (w : ℝ) : ℝ :=
  ((⌊2 * w⌋ : ℤ) : ℝ) * w - ((⌊2 * w⌋ : ℤ) : ℝ) * (((⌊2 * w⌋ : ℤ) : ℝ) + 1) / 4

/-- **`N₀(x) = 2λx⌊x⌋ - 2κλx⌊αx⌋ - 2J(λx)`**, `λ = 37/40`, `κ = 6`, `α = 3/40`. -/
noncomputable def N0 (x : ℝ) : ℝ :=
  2 * (37 / 40) * x * ((⌊x⌋ : ℤ) : ℝ) - 2 * 6 * (37 / 40) * x * ((⌊3 / 40 * x⌋ : ℤ) : ℝ)
    - 2 * Jf (37 / 40 * x)

/-- The class weight `(T - b)(T + b - ℓ - 5)` with `ℓ = 2X₁ + α`, `b = 3(2X₂ + β)`
(`X₁ = ⌊x⌋`, `X₂ = ⌊αx⌋`, `α, β ∈ {0,1,2}` the class counts at `K` and `N`). -/
def Hq (T X1 X2 : ℝ) (α β : ℕ) : ℝ :=
  (T - 3 * (2 * X2 + β)) * (T + 3 * (2 * X2 + β) - (2 * X1 + α) - 5)

/-- The model of the allocated cost: the class sum with base dimension `T` plus `e·p` extra rows
on the classes of largest `ℓ_K`. `Φ(x, ⌊2Hx⌋, u) = Γ(x)`. -/
noncomputable def Phi (x T e : ℝ) : ℝ :=
  Cint (Hq T ((⌊x⌋ : ℤ) : ℝ) ((⌊3 / 40 * x⌋ : ℤ) : ℝ)) (Int.fract x) (Int.fract (3 / 40 * x))
    + e * (2 * T - 2 * ((⌊x⌋ : ℤ) : ℝ) - 4) - min e (min (Int.fract x) (1 / 2))
    - min e (max 0 (Int.fract x - 1 / 2))

lemma integral_GamInt (x T : ℝ) :
    ∫ z in (0 : ℝ)..(1 / 2), GamInt x T z =
      Cint (Hq T ((⌊x⌋ : ℤ) : ℝ) ((⌊3 / 40 * x⌋ : ℤ) : ℝ)) (Int.fract x) (Int.fract (3 / 40 * x)) := by
  rw [← integral_step]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le (by norm_num)] at hz
  simp only
  unfold GamInt Hq
  rw [ell_eq x z hz.1 hz.2, ell_eq (3 / 40 * x) z hz.1 hz.2]
  ring

lemma uf_eq (x : ℝ) : uf x = Int.fract (2 * (23 / 20) * x) / 2 := by
  unfold uf Tf Int.fract; ring

lemma uf_nonneg (x : ℝ) : 0 ≤ uf x := by
  rw [uf_eq]; have := Int.fract_nonneg (2 * (23 / 20) * x); linarith

lemma uf_lt_half (x : ℝ) : uf x < 1 / 2 := by
  rw [uf_eq]; have := Int.fract_lt_one (2 * (23 / 20) * x); linarith

lemma Tf_eq (x : ℝ) : (Tf x : ℝ) = 2 * (23 / 20) * x - 2 * uf x := by
  unfold uf; ring

lemma qf_eq (x : ℝ) : (qf x : ℝ) = 2 * ((⌊x⌋ : ℤ) : ℝ) + (if Int.fract x < 1 / 2 then 0 else 1) := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx := Int.floor_add_fract x
  unfold qf
  have : ⌊2 * x⌋ = 2 * ⌊x⌋ + (if Int.fract x < 1 / 2 then 0 else 1) := by
    split_ifs with h
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    · push Not at h
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [this]; push_cast; split_ifs <;> simp

lemma Gam_eq_Phi (x : ℝ) : Gam x = Phi x (Tf x) (uf x) := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hu0 : 0 ≤ uf x := by rw [uf_eq]; have := Int.fract_nonneg (2 * (23 / 20) * x); linarith
  have hu1 : uf x < 1 / 2 := by rw [uf_eq]; have := Int.fract_lt_one (2 * (23 / 20) * x); linarith
  have hx := Int.floor_add_fract x
  unfold Gam Phi
  rw [integral_GamInt]
  unfold vf
  rw [qf_eq]
  rcases lt_or_ge (Int.fract x) (1 / 2) with hf | hf
  · simp only [hf, ↓reduceIte]
    rw [min_eq_left hf.le, max_eq_left (by linarith : Int.fract x - 1 / 2 ≤ 0)]
    rw [min_def, min_def, max_def]
    split_ifs <;> first | (exfalso; linarith) | nlinarith
  · simp only [not_lt.mpr hf, ↓reduceIte]
    rw [min_eq_right hf, max_eq_right (by linarith : 0 ≤ Int.fract x - 1 / 2)]
    rw [min_def, min_def, max_def]
    split_ifs <;> first | (exfalso; linarith) | nlinarith


lemma fract_two_mul (x : ℝ) :
    Int.fract (2 * x) = if Int.fract x < 1 / 2 then 2 * Int.fract x else 2 * Int.fract x - 1 := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hx := Int.floor_add_fract x
  have h2 : ⌊2 * x⌋ = 2 * ⌊x⌋ + (if Int.fract x < 1 / 2 then 0 else 1) := by
    split_ifs with h
    · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    · push Not at h
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  have h3 : Int.fract (2 * x) = 2 * x - ⌊2 * x⌋ := rfl
  rw [h3, h2]
  split_ifs <;> push_cast <;> linarith

set_option maxHeartbeats 1000000 in
theorem neg_Gam_sub_N0 (x : ℝ) :
    -Gam x - N0 x = CatalanCore.Zeta5.Profile.Rg x := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hg0 := Int.fract_nonneg (3 / 40 * x)
  have hg1 := Int.fract_lt_one (3 / 40 * x)
  have hτ0 := Int.fract_nonneg (2 * (23 / 20) * x)
  have hτ1 := Int.fract_lt_one (2 * (23 / 20) * x)
  rw [Gam_eq_Phi]
  unfold Phi N0 Jf CatalanCore.Zeta5.Profile.Rg CatalanCore.Zeta5.Profile.Fs
    CatalanCore.Zeta5.Profile.Qc CatalanCore.Zeta5.Profile.Q1 CatalanCore.Zeta5.Profile.Q2
    CatalanCore.Zeta5.Profile.tri CatalanCore.Zeta5.Profile.sg CatalanCore.Zeta5.Profile.lam
    CatalanCore.Zeta5.Profile.al CatalanCore.Zeta5.Profile.hh
  rw [Cint_eval _ hf0 hf1 hg0 hg1, uf_eq]
  have e1 : 2 * (37 / 40 * x) = 2 * (37 / 40) * x := by ring
  rw [e1]
  have hT' : ((⌊2 * (23 / 20) * x⌋ : ℤ) : ℝ) = 2 * (23 / 20) * x - Int.fract (2 * (23 / 20) * x) := by
    have := Int.floor_add_fract (2 * (23 / 20) * x); linarith
  have hX1' : ((⌊x⌋ : ℤ) : ℝ) = x - Int.fract x := by
    have := Int.floor_add_fract x; linarith
  have hX2' : ((⌊3 / 40 * x⌋ : ℤ) : ℝ) = 3 / 40 * x - Int.fract (3 / 40 * x) := by
    have := Int.floor_add_fract (3 / 40 * x); linarith
  have hm' : ((⌊2 * (37 / 40) * x⌋ : ℤ) : ℝ) = 2 * (37 / 40) * x - Int.fract (2 * (37 / 40) * x) := by
    have := Int.floor_add_fract (2 * (37 / 40) * x); linarith
  have hσ := fract_two_mul x
  unfold Tf
  rw [hT', hX1', hX2', hm']
  unfold Hq
  generalize Int.fract (2 * (23 / 20) * x) = τ at *
  generalize Int.fract (2 * (37 / 40) * x) = η at *
  generalize Int.fract (3 / 40 * x) = g at *
  generalize Int.fract (2 * x) = σ at *
  generalize Int.fract x = f at *
  push_cast
  rcases lt_or_ge f (1 / 2) with hf | hf <;> rcases lt_or_ge g (1 / 2) with hg | hg
  · simp only [hf, ↓reduceIte] at hσ; subst hσ
    have a1 : min f (1 - f) = f := min_eq_left (by linarith)
    have a2 : min g (1 - g) = g := min_eq_left (by linarith)
    have a3 : min f (1 / 2) = f := min_eq_left hf.le
    have a4 : max 0 (f - 1 / 2) = 0 := max_eq_left (by linarith)
    have a5 : min (τ / 2) 0 = 0 := min_eq_right (by linarith)
    simp only [hf, hg, ↓reduceIte, a1, a2, a3, a4, a5]
    simp only [min_def, max_def]
    split_ifs <;> first | (exfalso; linarith) | ring1 | linarith
  · simp only [hf, ↓reduceIte] at hσ; subst hσ
    have a1 : min f (1 - f) = f := min_eq_left (by linarith)
    have a2 : min g (1 - g) = 1 - g := min_eq_right (by linarith)
    have a3 : min f (1 / 2) = f := min_eq_left hf.le
    have a4 : max 0 (f - 1 / 2) = 0 := max_eq_left (by linarith)
    have a5 : min (τ / 2) 0 = 0 := min_eq_right (by linarith)
    simp only [hf, not_lt.mpr hg, ↓reduceIte, a1, a2, a3, a4, a5]
    simp only [min_def, max_def]
    split_ifs <;> first | (exfalso; linarith) | ring1 | linarith
  · simp only [not_lt.mpr hf, ↓reduceIte] at hσ; subst hσ
    have a1 : min f (1 - f) = 1 - f := min_eq_right (by linarith)
    have a2 : min g (1 - g) = g := min_eq_left (by linarith)
    have a3 : min f (1 / 2) = 1 / 2 := min_eq_right hf
    have a4 : max 0 (f - 1 / 2) = f - 1 / 2 := max_eq_right (by linarith)
    have a5 : min (τ / 2) (1 / 2) = τ / 2 := min_eq_left (by linarith)
    simp only [not_lt.mpr hf, hg, ↓reduceIte, a1, a2, a3, a4, a5]
    simp only [min_def, max_def]
    split_ifs <;> first | (exfalso; linarith) | ring1 | linarith
  · simp only [not_lt.mpr hf, ↓reduceIte] at hσ; subst hσ
    have a1 : min f (1 - f) = 1 - f := min_eq_right (by linarith)
    have a2 : min g (1 - g) = 1 - g := min_eq_right (by linarith)
    have a3 : min f (1 / 2) = 1 / 2 := min_eq_right hf
    have a4 : max 0 (f - 1 / 2) = f - 1 / 2 := max_eq_right (by linarith)
    have a5 : min (τ / 2) (1 / 2) = τ / 2 := min_eq_left (by linarith)
    simp only [not_lt.mpr hf, not_lt.mpr hg, ↓reduceIte, a1, a2, a3, a4, a5]
    simp only [min_def, max_def]
    split_ifs <;> first | (exfalso; linarith) | ring1 | linarith


/-! ### Properties of the model `Φ` -/

lemma abs_min_sub_min_right (e e' a : ℝ) : |min e a - min e' a| ≤ |e - e'| := by
  have := abs_min_sub_min_le_max e a e' a
  rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at this

/-- `Φ` is Lipschitz in the extra-row fraction `e`. -/
lemma Phi_lip (x T e e' : ℝ) :
    |Phi x T e - Phi x T e'| ≤
      (|2 * T - 2 * ((⌊x⌋ : ℤ) : ℝ) - 4| + 2) * |e - e'| := by
  unfold Phi
  have h1 := abs_min_sub_min_right e e' (min (Int.fract x) (1 / 2))
  have h2 := abs_min_sub_min_right e e' (max 0 (Int.fract x - 1 / 2))
  have h3 : |(e - e') * (2 * T - 2 * ((⌊x⌋ : ℤ) : ℝ) - 4)| =
      |2 * T - 2 * ((⌊x⌋ : ℤ) : ℝ) - 4| * |e - e'| := by rw [abs_mul, mul_comm]
  have h4 : ∀ a b c d k : ℝ, a - b - (c - d) - k = (a - c) - (b - d) - k := fun a b c d k => by ring
  calc _ = |(e - e') * (2 * T - 2 * ((⌊x⌋ : ℤ) : ℝ) - 4)
          - (min e (min (Int.fract x) (1 / 2)) - min e' (min (Int.fract x) (1 / 2)))
          - (min e (max 0 (Int.fract x - 1 / 2)) - min e' (max 0 (Int.fract x - 1 / 2)))| := by
        congr 1; ring
    _ ≤ |(e - e') * (2 * T - 2 * ((⌊x⌋ : ℤ) : ℝ) - 4)|
          + |min e (min (Int.fract x) (1 / 2)) - min e' (min (Int.fract x) (1 / 2))|
          + |min e (max 0 (Int.fract x - 1 / 2)) - min e' (max 0 (Int.fract x - 1 / 2))| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by rw [h3]; linarith

/-- **Allocation continuity**: adding one row to every class (`T → T+1`) equals adding
`e = 1/2` extra rows per class (`e = 1/2` means `p/2` extra rows, one per class). -/
lemma Phi_cont (x T : ℝ) : Phi x (T + 1) 0 = Phi x T (1 / 2) := by
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  have hg0 := Int.fract_nonneg (3 / 40 * x)
  have hg1 := Int.fract_lt_one (3 / 40 * x)
  unfold Phi
  rw [Cint_eval _ hf0 hf1 hg0 hg1, Cint_eval _ hf0 hf1 hg0 hg1]
  have m1 : min (0 : ℝ) (min (Int.fract x) (1 / 2)) = 0 := min_eq_left (le_min hf0 (by norm_num))
  have m2 : min (0 : ℝ) (max 0 (Int.fract x - 1 / 2)) = 0 := min_eq_left (le_max_left _ _)
  have m3 : min (1 / 2 : ℝ) (min (Int.fract x) (1 / 2)) = min (Int.fract x) (1 / 2) :=
    min_eq_right (min_le_right _ _)
  have m4 : min (1 / 2 : ℝ) (max 0 (Int.fract x - 1 / 2)) = max 0 (Int.fract x - 1 / 2) :=
    min_eq_right (max_le (by norm_num) (by linarith))
  rw [m1, m2, m3, m4]
  unfold Hq
  generalize Int.fract (3 / 40 * x) = g at *
  generalize Int.fract x = f at *
  rcases lt_or_ge f (1 / 2) with hf | hf <;> rcases lt_or_ge g (1 / 2) with hg | hg
  · simp only [hf, hg, ↓reduceIte]
    rw [min_eq_left (by linarith : f ≤ 1 - f), min_eq_left hf.le, max_eq_left (by linarith : f - 1 / 2 ≤ 0)]
    push_cast; ring
  · simp only [hf, not_lt.mpr hg, ↓reduceIte]
    rw [min_eq_left (by linarith : f ≤ 1 - f), min_eq_left hf.le, max_eq_left (by linarith : f - 1 / 2 ≤ 0)]
    push_cast; ring
  · simp only [not_lt.mpr hf, hg, ↓reduceIte]
    rw [min_eq_right (by linarith : 1 - f ≤ f), min_eq_right hf, max_eq_right (by linarith : 0 ≤ f - 1 / 2)]
    push_cast; ring
  · simp only [not_lt.mpr hf, not_lt.mpr hg, ↓reduceIte]
    rw [min_eq_right (by linarith : 1 - f ≤ f), min_eq_right hf, max_eq_right (by linarith : 0 ≤ f - 1 / 2)]
    push_cast; ring

end Apery.CostIn
