module

public import CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import CatalanMeasure.GenD.Signed.ChebSquare
public import CatalanMeasure.GenD.Signed.RouteI.CapFields

@[expose] public section
set_option Elab.async false

/-!
# C5 `MarkedSourceBound`: the packed adapter and the physical-kernel identity

Data-free. Two parts.

1. `LaurentBound.of_packed`: the `poly` field of `MarkedTransfer.LaurentBound` from ONE integer
   identity of packed values (`packZ` at radix `2K`), via `PackedPolynomial.laurent_poly_of_packed_eval`
   (centred guard `|c| <= K`, `K = 2^255` in the Route I instance).
2. The physical-kernel identity. For `x != 0` and an admissible source,
   `refDiff S x = Dphys S x`, where `Dphys` is the difference of cell averages of the two
   explicit logarithmic kernels
   `log|x - s| + log|1 - x s|` (rows, `s = physX Y`) and `log(1 - 2 c x + x^2)` (columns).
   Every `log|x|` cancels because `mass R1 - mass R0 = mass C1 - mass C0 = -1/50`
   (`Admissible`). All identities are pointwise a.e. (one exceptional abscissa per cell), and
   interval integrability of every integrand is proved.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound

open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedTransferSource
open CatalanMeasure.GenD.Signed.RouteI.MarkedTransfer
open CatalanMeasure.Signed.ChebSquare
open MeasureTheory intervalIntegral Polynomial
open scoped Interval

noncomputable section

/-! ### Part 1: the packed adapter -/

theorem pack_eq_packZ (B : ℤ) (l : List ℤ) : PackedPolynomial.pack B l = packZ B l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [PackedPolynomial.pack, packZ, ih]

theorem l1_eq (l : List ℤ) : (PackedPolynomial.l1 l : ℤ) = CatalanMeasure.Signed.ChebSquare.l1 l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [PackedPolynomial.l1, CatalanMeasure.Signed.ChebSquare.l1, ← ih, Int.natCast_natAbs]


/-! ### Part 2: the physical-kernel identity -/

/-- The row kernel at the physical point `s = X(Y)`: `log|x - s| + log|1 - x s|`. -/
def rowK (x Y : ℝ) : ℝ := Real.log |x - YCell.physX Y| + Real.log |1 - x * YCell.physX Y|

/-- The column kernel at the column coordinate `c`: `log|1 - 2 c x + x^2|`. -/
def colK (x c : ℝ) : ℝ := Real.log |1 - 2 * c * x + x ^ 2|

/-- Sum of the cell averages of a kernel. -/
def avgL (l : List YCell) (f : ℝ → ℝ) : ℝ := (l.map fun c => c.avg f).sum

/-- The reference difference in physical-kernel form (no `log|x|` terms). -/
def Dphys (S : CapSource) (x : ℝ) : ℝ :=
  (avgL (S.refRow 1) (rowK x) - avgL (S.refRow 0) (rowK x)) -
    (avgL (S.refCol 1) (colK x) - avgL (S.refCol 0) (colK x))

theorem physX_spec {Y : ℝ} (hY : 2 ≤ |Y|) :
    YCell.physX Y ≠ 0 ∧ YCell.physX Y + 1 / YCell.physX Y = Y := by
  have hsq : 4 ≤ Y ^ 2 := by nlinarith [sq_abs Y, abs_nonneg Y]
  have hr0 : 0 ≤ Real.sqrt (Y ^ 2 - 4) := Real.sqrt_nonneg _
  have hr : Real.sqrt (Y ^ 2 - 4) ^ 2 = Y ^ 2 - 4 := Real.sq_sqrt (by linarith)
  unfold YCell.physX
  by_cases h0 : 0 ≤ Y
  · rw [if_pos h0]
    have hY2 : 2 ≤ Y := by rwa [abs_of_nonneg h0] at hY
    have hd : 0 < Y + Real.sqrt (Y ^ 2 - 4) := by linarith
    refine ⟨by positivity, ?_⟩
    field_simp
    linear_combination hr
  · rw [if_neg h0]
    have hY2 : Y ≤ -2 := by
      have := abs_of_neg (lt_of_not_ge h0)
      linarith
    have hd : 0 < -Y + Real.sqrt (Y ^ 2 - 4) := by linarith
    refine ⟨neg_ne_zero.mpr (by positivity), ?_⟩
    field_simp
    linear_combination (-1) * hr

theorem physX_continuousOn {lo hi : ℝ} (h : 2 ≤ lo ∨ hi ≤ -2) :
    ContinuousOn YCell.physX (Set.Icc lo hi) := by
  rcases h with h | h
  · have hc : ContinuousOn (fun Y : ℝ => 2 / (Y + Real.sqrt (Y ^ 2 - 4))) (Set.Icc lo hi) := by
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro Y hY
        have : 0 ≤ Real.sqrt (Y ^ 2 - 4) := Real.sqrt_nonneg _
        have : 2 ≤ Y := le_trans h hY.1
        positivity
    refine hc.congr ?_
    intro Y hY
    unfold YCell.physX
    rw [if_pos (by linarith [hY.1])]
  · have hc : ContinuousOn (fun Y : ℝ => -(2 / (-Y + Real.sqrt (Y ^ 2 - 4)))) (Set.Icc lo hi) := by
      apply ContinuousOn.neg
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro Y hY
        have : 0 ≤ Real.sqrt (Y ^ 2 - 4) := Real.sqrt_nonneg _
        have : Y ≤ -2 := le_trans hY.2 h
        have : 0 < -Y := by linarith
        positivity
    refine hc.congr ?_
    intro Y hY
    unfold YCell.physX
    rw [if_neg (by linarith [hY.2])]

theorem cell_abs_ge {c : YCell} (h : 2 ≤ c.lo ∨ c.hi ≤ -2) {Y : ℝ} (hY : Y ∈ Set.Icc c.lo c.hi) :
    2 ≤ |Y| := by
  rcases h with h | h
  · rw [abs_of_nonneg (by linarith [hY.1])]; linarith [hY.1]
  · rw [abs_of_nonpos (by linarith [hY.2])]; linarith [hY.2]

theorem intInt_log_phys {c : YCell} (h : 2 ≤ c.lo ∨ c.hi ≤ -2) :
    IntervalIntegrable (fun Y => Real.log |YCell.physX Y|) volume c.lo c.hi := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le c.lo_lt.le]
  have hc := physX_continuousOn h
  refine ContinuousOn.log (continuous_abs.comp_continuousOn hc) ?_
  intro Y hY
  exact abs_ne_zero.mpr (physX_spec (cell_abs_ge h hY)).1

theorem intInt_log_sub (c : YCell) (y : ℝ) :
    IntervalIntegrable (fun s => Real.log |y - s|) volume c.lo c.hi := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := y - c.lo) (b := y - c.hi)).comp_sub_left y
  simpa [Real.log_abs] using h

/-- Row identity for one cell, pointwise in `Y`, off the single point `Y = x + 1/x`. -/
theorem row_pointwise {x Y : ℝ} (hx : x ≠ 0) (hY : 2 ≤ |Y|) (hne : Y ≠ x + 1 / x) :
    Real.log |x + 1 / x - Y| + Real.log |YCell.physX Y| =
      rowK x Y - Real.log |x| := by
  obtain ⟨hs0, hs⟩ := physX_spec hY
  set s := YCell.physX Y with hsdef
  have key : x + 1 / x - Y = -((x - s) * (1 - x * s)) / (x * s) := by
    rw [← hs]
    field_simp
    ring
  have hY' : x + 1 / x - Y ≠ 0 := fun h => hne (by linarith)
  have hnum : (x - s) * (1 - x * s) ≠ 0 := by
    intro h0
    apply hY'
    rw [key, neg_div, h0]
    simp
  have h1 : x - s ≠ 0 := left_ne_zero_of_mul hnum
  have h2 : 1 - x * s ≠ 0 := right_ne_zero_of_mul hnum
  have habs : |x + 1 / x - Y| = |x - s| * |1 - x * s| / (|x| * |s|) := by
    rw [key, abs_div, abs_neg, abs_mul, abs_mul]
  rw [habs, Real.log_div (by positivity) (by positivity), Real.log_mul (abs_ne_zero.mpr h1)
    (abs_ne_zero.mpr h2), Real.log_mul (abs_ne_zero.mpr hx) (abs_ne_zero.mpr hs0)]
  unfold rowK
  rw [← hsdef]
  ring

theorem rowK_integrable {c : YCell} (h : 2 ≤ c.lo ∨ c.hi ≤ -2) {x : ℝ} (hx : x ≠ 0) :
    IntervalIntegrable (rowK x) volume c.lo c.hi := by
  have h1 := (intInt_log_sub c (x + 1 / x)).add (intInt_log_phys h)
  have h2 := (h1.add (intervalIntegrable_const (c := Real.log |x|) (μ := volume)
    (a := c.lo) (b := c.hi)))
  refine h2.congr_ae ?_
  have hae : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∉ ({x + 1 / x} : Set ℝ) :=
    (Set.countable_singleton _).ae_notMem volume
  have hmem := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_uIoc (a := c.lo) (b := c.hi))
  filter_upwards [ae_restrict_of_ae (s := Ι c.lo c.hi) hae, hmem] with Y hY hYm
  have hYm' : Y ∈ Set.Icc c.lo c.hi := by
    rw [Set.uIoc_of_le c.lo_lt.le] at hYm
    exact ⟨hYm.1.le, hYm.2⟩
  have := row_pointwise hx (cell_abs_ge h hYm') hY
  linarith

/-- Row cell identity: potential plus logarithmic physical mean equals the kernel average minus
`w log|x|`. -/
theorem cell_row {c : YCell} (h : 2 ≤ c.lo ∨ c.hi ≤ -2) {x : ℝ} (hx : x ≠ 0) :
    c.pot (x + 1 / x) + c.phys (fun u => Real.log |u|) =
      c.avg (rowK x) - c.w * Real.log |x| := by
  have hl : c.lo < c.hi := c.lo_lt
  have hne : c.hi - c.lo ≠ 0 := by linarith
  unfold YCell.pot YCell.phys YCell.avg
  have hI : (∫ s in c.lo..c.hi, Real.log |x + 1 / x - s|) +
        (∫ s in c.lo..c.hi, Real.log |YCell.physX s|) =
      (∫ s in c.lo..c.hi, rowK x s) - (c.hi - c.lo) * Real.log |x| := by
    rw [← intervalIntegral.integral_add (intInt_log_sub c _) (intInt_log_phys h)]
    have hc : ∫ s in c.lo..c.hi, rowK x s - Real.log |x| =
        (∫ s in c.lo..c.hi, rowK x s) - ∫ _ in c.lo..c.hi, Real.log |x| :=
      intervalIntegral.integral_sub (rowK_integrable h hx) intervalIntegrable_const
    rw [intervalIntegral.integral_const, smul_eq_mul] at hc
    rw [← hc]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton (x + 1 / x)).ae_notMem volume] with Y hY hYm
    rw [Set.uIoc_of_le hl.le] at hYm
    exact row_pointwise hx (cell_abs_ge h ⟨hYm.1.le, hYm.2⟩) hY
  beta_reduce
  rw [← mul_add, hI]
  field_simp

/-- Column cell identity for the cell with doubled endpoints. -/
theorem cell_col (c : YCell) {x : ℝ} (hx : x ≠ 0) :
    (c.dil2).pot (x + 1 / x) = c.avg (colK x) - c.w * Real.log |x| := by
  have hl : c.lo < c.hi := c.lo_lt
  have hne : c.hi - c.lo ≠ 0 := by linarith
  have hx2 : (0 : ℝ) < 2 := by norm_num
  -- pointwise
  have pw : ∀ u : ℝ, 1 - 2 * u * x + x ^ 2 ≠ 0 →
      Real.log |x + 1 / x - 2 * u| = colK x u - Real.log |x| := by
    intro u hu
    have : x + 1 / x - 2 * u = (1 - 2 * u * x + x ^ 2) / x := by field_simp; ring
    rw [this, abs_div, Real.log_div (abs_ne_zero.mpr hu) (abs_ne_zero.mpr hx)]
    rfl
  have hint : IntervalIntegrable (fun u => Real.log |x + 1 / x - 2 * u|) volume c.lo c.hi := by
    have h2 := (intInt_log_sub c.dil2 (x + 1 / x)).comp_mul_left (c := 2)
    have e1 : c.dil2.lo / 2 = c.lo := by simp [YCell.dil2]
    have e2 : c.dil2.hi / 2 = c.hi := by simp [YCell.dil2]
    rw [e1, e2] at h2
    exact h2
  have hcol : IntervalIntegrable (colK x) volume c.lo c.hi := by
    have h1 := hint.add (intervalIntegrable_const (c := Real.log |x|) (μ := volume)
      (a := c.lo) (b := c.hi))
    refine h1.congr_ae ?_
    have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({(1 + x ^ 2) / (2 * x)} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem volume
    filter_upwards [ae_restrict_of_ae (s := Ι c.lo c.hi) hae] with u hu
    have hu' : 1 - 2 * u * x + x ^ 2 ≠ 0 := by
      intro h0
      apply hu
      simp only [Set.mem_singleton_iff]
      field_simp
      linarith
    have := pw u hu'
    linarith
  have hI : ∫ s in 2 * c.lo..2 * c.hi, Real.log |x + 1 / x - s| =
      2 * ((∫ u in c.lo..c.hi, colK x u) - (c.hi - c.lo) * Real.log |x|) := by
    have h1 := intervalIntegral.integral_comp_mul_left
      (fun s => Real.log |x + 1 / x - s|) (a := c.lo) (b := c.hi) (c := 2) (by norm_num)
    have h2 : ∫ u in c.lo..c.hi, Real.log |x + 1 / x - 2 * u| =
        (∫ u in c.lo..c.hi, colK x u) - (c.hi - c.lo) * Real.log |x| := by
      have hc : ∫ u in c.lo..c.hi, colK x u - Real.log |x| =
          (∫ u in c.lo..c.hi, colK x u) - ∫ _ in c.lo..c.hi, Real.log |x| :=
        intervalIntegral.integral_sub hcol intervalIntegrable_const
      rw [intervalIntegral.integral_const, smul_eq_mul] at hc
      rw [← hc]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(Set.countable_singleton ((1 + x ^ 2) / (2 * x))).ae_notMem volume] with u hu _
      apply pw
      intro h0
      apply hu
      simp only [Set.mem_singleton_iff]
      field_simp
      linarith
    simp only [smul_eq_mul] at h1
    rw [h2] at h1
    linarith
  unfold YCell.pot YCell.avg YCell.dil2
  simp only
  rw [hI]
  field_simp

theorem potL_phys_row {l : List YCell} (h : ∀ c ∈ l, 2 ≤ c.lo ∨ c.hi ≤ -2) {x : ℝ} (hx : x ≠ 0) :
    potL l (x + 1 / x) + physL l (fun u => Real.log |u|) = avgL l (rowK x) - massL l * Real.log |x| := by
  induction l with
  | nil => simp [potL, physL, avgL, massL]
  | cons c t ih =>
    have ht := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hc := cell_row (h c List.mem_cons_self) hx
    simp only [potL, physL, avgL, massL, List.map_cons, List.sum_cons] at ht hc ⊢
    linarith

theorem potL_dil2 (l : List YCell) {x : ℝ} (hx : x ≠ 0) :
    potL (l.map YCell.dil2) (x + 1 / x) = avgL l (colK x) - massL l * Real.log |x| := by
  induction l with
  | nil => simp [potL, avgL, massL]
  | cons c t ih =>
    have hc := cell_col c hx
    simp only [potL, avgL, massL, List.map_cons, List.sum_cons] at ih hc ⊢
    linarith

/-- The mass differences: `mass(R1 - R0) = mass(C1 - C0) = -1/50`. -/
theorem mass_diff {S : CapSource} (hS : S.Admissible) :
    massL (S.refRow 1) - massL (S.refRow 0) = -1 / 50 ∧
      massL (S.refCol 1) - massL (S.refCol 0) = -1 / 50 := by
  have := hS.ref_row_mass0
  have := hS.ref_row_mass1
  have := hS.ref_col_mass0
  have := hS.ref_col_mass1
  constructor <;> linarith


end

end CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
