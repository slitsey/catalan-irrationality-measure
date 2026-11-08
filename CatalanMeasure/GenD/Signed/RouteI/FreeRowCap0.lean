module

public import CatalanMeasure.GenD.Signed.RouteI.OrdHf
public import CatalanMeasure.GenD.Signed.RouteI.KronSquare
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.CompactCap
public import CatalanMeasure.GenD.Signed.RouteI.MarkedPilot

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Route I `FreeRowCap0`: the anchor-0 free row of `capSource` from finite checks

`freeRowCap0_of_checks` proves `capSource.FreeRowCap Trunc.exact 0 (-2579777 / 1000000)` from two
certificates `RowCert`, one for each sign of `x`.

The row is one polynomial of `z = 2 t - 1`, `t = |x|`, on the physical form of the field:
twice the own gas potential, the opposite gas potential, minus the anchor-0 column, and the radial and
logarithmic rest.

* The own direct potential `∫ log |t - X(y)|` goes through its Chebyshev series and a bounded-variation
  tail (`own_stream`, `hV_of`); thin slivers of nonnegative density are dropped by sign.
* Reflection, opposite and column potentials, `log t` and `log (1 - s t)`, are bounded by atoms
  `w log |1 - r(q) t|` of rational `q` (`refl_bound`, `opp_bound`, `col_bound`, `log_t_atom`); the
  positive reflection also uses the series `reflPoly` by `refl_series`.
* The moments of the atoms and the direct moments come from one packed engine (`moments`,
  `group_ok`), whose entries are checked against the atoms.
* The radial field is the chord cover of `OrdHf`, with one further block for `log t` (`rad_of_cov`).
* The sum of the polynomials is bounded by a square on the packed integers (`kron_le`).

A real unit closes the file: the node checks of the whole positive anchor-0 column, and its first
atoms through the engine (`unit_close`).

kcost: the theorem part has no `decide +kernel`; the unit is priced at each declaration.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory intervalIntegral
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

noncomputable section

/-! ### The field in physical form -/

/-- The opposite species. -/
def opp : Sign → Sign
  | Sign.neg => Sign.pos
  | Sign.pos => Sign.neg

/-- Everything in the free row at anchor `0` that is not a gas or column kernel. -/
def rest (S : CapSource) (t : Trunc) (σ : Sign) (x : ℝ) : ℝ :=
  11 / 29 * Real.log |x| - 39 / 29 * Real.log (1 + x ^ 2) + 3 / 29 * Real.log (1 - x) - kappa σ +
    (if σ = Sign.pos then S.reflPoly x + S.reflTail else 0) + S.radialA t σ x + S.auxTail t σ

theorem avgL_append (a b : List YCell) (f : ℝ → ℝ) : avgL (a ++ b) f = avgL a f + avgL b f := by
  simp [avgL]

theorem avgL_perm {a b : List YCell} (h : a.Perm b) (f : ℝ → ℝ) : avgL a f = avgL b f := by
  unfold avgL
  exact (h.map _).sum_eq

/-- `refRow 0` is both species. -/
theorem avgL_ref0 {S : CapSource} (hS : S.Admissible) (σ : Sign) (f : ℝ → ℝ) :
    avgL (S.refRow 0) f = avgL (S.gas σ) f + avgL (S.gas (opp σ)) f := by
  rw [avgL_perm hS.ref0_perm, avgL_append]
  cases σ
  · simp only [opp]; ring
  · simp only [opp]

/-- **Physical form of the anchor-0 free row.** All `log|x|` from the potentials cancel. -/
theorem rowField_phys {S : CapSource} (hS : S.Admissible) (t : Trunc) (σ : Sign) {x : ℝ}
    (hx : x ≠ 0) :
    S.rowField t σ Flavor.free (some 0) x =
      2 * avgL (S.gas σ) (rowK x) + avgL (S.gas (opp σ)) (rowK x) -
        avgL (S.refCol 0) (colK x) + rest S t σ x := by
  have hg : ∀ c ∈ S.gas σ, 2 ≤ c.lo ∨ c.hi ≤ -2 := by
    intro c hc
    cases σ
    · exact Or.inr (hS.gas_neg c hc)
    · exact Or.inl (hS.gas_pos c hc)
  have r0 := potL_phys_row (l := S.refRow 0) (fun c hc => hS.ref_away 0 c hc) hx
  have r1 := potL_phys_row (l := S.gas σ) hg hx
  have c0 := potL_dil2 (S.refCol 0) hx
  have m0 := hS.ref_row_mass0
  have n0 := hS.ref_col_mass0
  rw [m0] at r0
  rw [n0] at c0
  have e := avgL_ref0 hS σ (rowK x)
  unfold CapSource.rowField rest
  simp only [CapSource.refR, CapSource.refC, Flavor.free]
  rw [e] at r0
  linarith

/-! ### Cell sums as profile pairings -/

theorem avg_row_same {l : List YCell} {P : List Seg} {sg t : ℝ} (hsg : sg = 1 ∨ sg = -1)
    (hl : ∀ c ∈ l, 2 ≤ c.lo ∨ c.hi ≤ -2)
    (hb : ∀ F : ℝ → ℝ, evC l F = evS P (fun y => sg * F (sg * y)))
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (h0 : 0 < t) :
    avgL l (rowK (sg * t)) = pint P (rowK t) := by
  have hx : sg * t ≠ 0 := by
    rcases hsg with rfl | rfl <;> simp [h0.ne']
  have hs : ∀ y, 0 < y → rowK (sg * t) (sg * y) = rowK t y := by
    intro y hy
    rcases hsg with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact rowK_neg_neg t hy
  rw [avgL_row hl hx, hb]
  refine evS_congr fun g hg => ?_
  obtain ⟨a, b⟩ := hP g hg
  rw [eps_row hsg hx a b.le]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le b.le] at hy
  exact hs y (by linarith [hy.1])

theorem avg_row_opp {l : List YCell} {P : List Seg} {sg t : ℝ} (hsg : sg = 1 ∨ sg = -1)
    (hl : ∀ c ∈ l, 2 ≤ c.lo ∨ c.hi ≤ -2)
    (hb : ∀ F : ℝ → ℝ, evC l F = evS P (fun y => -sg * F (-sg * y)))
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (h0 : 0 < t) :
    avgL l (rowK (sg * t)) = pint P (rowK (-t)) := by
  have hx : sg * t ≠ 0 := by
    rcases hsg with rfl | rfl <;> simp [h0.ne']
  have hneg : -sg = 1 ∨ -sg = -1 := by
    rcases hsg with rfl | rfl <;> simp
  have ho : ∀ y, 0 < y → rowK (sg * t) (-sg * y) = rowK (-t) y := by
    intro y hy
    rcases hsg with rfl | rfl
    · simp only [one_mul, neg_mul]
      have := rowK_neg_neg (-t) hy
      rwa [neg_neg] at this
    · simp
  rw [avgL_row hl hx, hb]
  refine evS_congr fun g hg => ?_
  obtain ⟨a, b⟩ := hP g hg
  rw [eps_row hneg hx a b.le]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le b.le] at hy
  exact ho y (by linarith [hy.1])

theorem avg_col {l : List YCell} {P : List Seg} {sg t : ℝ} (hsg : sg = 1 ∨ sg = -1)
    (hb : ∀ F : ℝ → ℝ, evC l F = evS P (fun y => sg * F (sg * y))) (h0 : 0 < t) :
    avgL l (colK (sg * t)) = pint P (colK t) := by
  have hx : sg * t ≠ 0 := by
    rcases hsg with rfl | rfl <;> simp [h0.ne']
  have hc : ∀ y, colK (sg * t) (sg * y) = colK t y := by
    intro y
    rcases hsg with rfl | rfl
    · simp
    · simp only [neg_mul, one_mul]
      exact colK_neg_neg t y
  rw [avgL_col _ hx, hb]
  refine evS_congr fun g _ => ?_
  rw [eps_col hsg hx]
  exact intervalIntegral.integral_congr fun y _ => hc y

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory intervalIntegral
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

noncomputable section

/-! ### Integrals below a line through the midpoint -/

/-- A function below a line at the midpoint integrates below the value at the midpoint. -/
theorem int_le_of_line {f : ℝ → ℝ} {lo hi B c : ℝ} (hlt : lo < hi)
    (hf : IntervalIntegrable f volume lo hi)
    (h : ∀ y ∈ Ioo lo hi, f y ≤ B + c * (y - (lo + hi) / 2)) :
    ∫ y in lo..hi, f y ≤ (hi - lo) * B := by
  have hg : IntervalIntegrable (fun y => B + c * (y - (lo + hi) / 2)) volume lo hi :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 := intervalIntegral.integral_mono_on_of_le_Ioo hlt.le hf hg h
  have e : ∫ y in lo..hi, (B + c * (y - (lo + hi) / 2)) = (hi - lo) * B := by
    have i1 : IntervalIntegrable (fun _ : ℝ => B) volume lo hi := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun y : ℝ => c * (y - (lo + hi) / 2)) volume lo hi :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  linarith

/-! ### The inverse branch -/

theorem physX_sum {y : ℝ} (hy : 2 ≤ y) : YCell.physX y + 1 / YCell.physX y = y :=
  (physX_spec (by rw [abs_of_pos (by linarith)]; exact hy)).2

theorem physX_lt_one {y : ℝ} (hy : 2 < y) : YCell.physX y < 1 := by
  obtain ⟨h0, h1⟩ := physX_mem hy.le
  have hs := physX_sum hy.le
  rcases h1.lt_or_eq with h | h
  · exact h
  · rw [h] at hs
    norm_num at hs
    linarith

/-- `y ↦ physX y` lies above its tangent at `m > 2`. -/
theorem physX_tangent {y m : ℝ} (hy : 2 ≤ y) (hm : 2 < m) :
    YCell.physX m + (YCell.physX m) ^ 2 / ((YCell.physX m) ^ 2 - 1) * (y - m) ≤ YCell.physX y := by
  obtain ⟨a0, a1⟩ := physX_mem hy
  obtain ⟨b0, b1⟩ := physX_mem hm.le
  have b2 := physX_lt_one hm
  have sa := physX_sum hy
  have sb := physX_sum hm.le
  set a := YCell.physX y
  set b := YCell.physX m
  have hb : b ^ 2 - 1 < 0 := by nlinarith
  have e : a - b - b ^ 2 / (b ^ 2 - 1) * (y - m) = (a - b) ^ 2 / ((1 - b ^ 2) * a) := by
    rw [← sa, ← sb]
    have h1 : 1 - b ^ 2 ≠ 0 := by linarith
    have h2 : b ^ 2 - 1 ≠ 0 := by linarith
    field_simp
    ring
  have : 0 ≤ (a - b) ^ 2 / ((1 - b ^ 2) * a) := by
    have : 0 < 1 - b ^ 2 := by linarith
    positivity
  linarith

/-- A rational test for a lower bound on `physX`. -/
theorem le_physX {r m : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hm : 2 < m) (h : m ≤ r + 1 / r) :
    r ≤ YCell.physX m := by
  obtain ⟨b0, b1⟩ := physX_mem hm.le
  have b2 := physX_lt_one hm
  have sb := physX_sum hm.le
  by_contra hc
  push Not at hc
  set b := YCell.physX m
  have h1 : r + 1 / r - (b + 1 / b) = (r - b) * (r * b - 1) / (r * b) := by
    field_simp
    ring
  have h2 : (r - b) * (r * b - 1) / (r * b) < 0 := by
    have : r * b - 1 < 0 := by nlinarith
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) this) (by positivity)
  linarith

/-! ### Real parameters -/

theorem rq_ofReal (q : ℝ) : rq (q : ℂ) = ((4 * q / (1 + q) ^ 2 : ℝ) : ℂ) := by
  unfold rq
  push_cast
  ring

/-- `KQ` at a real parameter. -/
theorem KQ_real {q r t : ℝ} (hr : r = 4 * q / (1 + q) ^ 2) (hpos : 0 ≤ 1 - r * t) :
    KQ (q : ℂ) t = Real.log (1 - r * t) := by
  unfold KQ
  rw [rq_ofReal, ← hr]
  have : (1 : ℂ) - (r : ℂ) * (t : ℂ) = ((1 - r * t : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]

/-! ### Reflection pieces -/

/-- Own reflection on one piece, by a real parameter `r ≤ physX (midpoint)`. -/
theorem refl_piece {lo hi t q r : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1)
    (hr : r = 4 * q / (1 + q) ^ 2) (hr0 : 0 < r) (hr1 : r < 1)
    (hrm : (lo + hi) / 2 ≤ r + 1 / r) :
    ∫ y in lo..hi, Real.log |1 - YCell.physX y * t| ≤ (hi - lo) * KQ (q : ℂ) t := by
  set m := (lo + hi) / 2 with hmdef
  have hm : 2 < m := by rw [hmdef]; linarith
  have hb : 0 < 1 - r * t := by nlinarith
  rw [KQ_real hr hb.le]
  have vm := le_physX hr0 hr1.le hm hrm
  obtain ⟨c0, c1⟩ := physX_mem hm.le
  have c2 := physX_lt_one hm
  refine int_le_of_line hlt (rowlog_int h2 hlt h0 h1) (c :=
    -(t * ((YCell.physX m) ^ 2 / ((YCell.physX m) ^ 2 - 1)) / (1 - r * t))) ?_
  intro y hy
  have hy2 : 2 < y := by linarith [hy.1]
  obtain ⟨a0, a1⟩ := physX_mem hy2.le
  have a2 := physX_lt_one hy2
  have hap : 0 < 1 - YCell.physX y * t := by nlinarith
  rw [abs_of_pos hap]
  have tg := physX_tangent hy2.le hm
  set D := (YCell.physX m) ^ 2 / ((YCell.physX m) ^ 2 - 1)
  -- log a ≤ log b + (a - b) / b
  have hl : Real.log ((1 - YCell.physX y * t) / (1 - r * t)) ≤
      (1 - YCell.physX y * t) / (1 - r * t) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hap hb)
  rw [Real.log_div hap.ne' hb.ne'] at hl
  have e1 : (1 - YCell.physX y * t) / (1 - r * t) - 1 = -(t * (YCell.physX y - r)) / (1 - r * t) := by
    rw [div_sub_one hb.ne']
    congr 1
    ring
  have e2 : -(t * D / (1 - r * t)) * (y - m) = -(t * (D * (y - m))) / (1 - r * t) := by
    field_simp
  rw [e1] at hl
  have h3 : -(t * (YCell.physX y - r)) / (1 - r * t) ≤ -(t * (D * (y - m))) / (1 - r * t) := by
    refine div_le_div_of_nonneg_right ?_ hb.le
    have : D * (y - m) ≤ YCell.physX y - r := by linarith
    nlinarith
  rw [← hmdef]
  linarith

/-! ### Opposite pieces -/

/-- The opposite row kernel. -/
theorem rowK_opp {y t : ℝ} (hy : 2 ≤ y) (h0 : 0 < t) :
    rowK (-t) y = Real.log (YCell.physX y) + Real.log (1 + y * t + t ^ 2) := by
  obtain ⟨a0, a1⟩ := physX_mem hy
  have sa := physX_sum hy
  have hp : 0 < 1 + y * t + t ^ 2 := by nlinarith
  set a := YCell.physX y
  have e1 : |-t - a| = t + a := by
    rw [show -t - a = -(t + a) by ring, abs_neg, abs_of_pos (by linarith)]
  have e2 : |1 - -t * a| = 1 + t * a := by
    rw [show 1 - -t * a = 1 + t * a by ring, abs_of_pos (by positivity)]
  unfold rowK
  rw [e1, e2, ← Real.log_mul (by positivity) (by positivity),
    ← Real.log_mul a0.ne' hp.ne']
  congr 1
  rw [← sa]
  field_simp
  ring

/-- The `log(1 + y t + t²)` part of an opposite piece, by midpoint concavity. -/
theorem opp_piece {lo hi t q1 q2 r1 r2 : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (h0 : 0 < t) (h1 : t ≤ 1)
    (hr1 : r1 = 4 * q1 / (1 + q1) ^ 2) (hr2 : r2 = 4 * q2 / (1 + q2) ^ 2)
    (n1 : r1 ≤ 0) (n2 : r2 ≤ 0) (hs : (lo + hi) / 2 ≤ -r1 + -r2) (hp : 1 ≤ r1 * r2) :
    ∫ y in lo..hi, Real.log (1 + y * t + t ^ 2) ≤
      (hi - lo) * (KQ (q1 : ℂ) t + KQ (q2 : ℂ) t) := by
  set m := (lo + hi) / 2 with hmdef
  have hm : 2 < m := by rw [hmdef]; linarith
  have hb : 0 < 1 + m * t + t ^ 2 := by nlinarith
  have b1 : 0 < 1 - r1 * t := by nlinarith
  have b2 : 0 < 1 - r2 * t := by nlinarith
  rw [KQ_real hr1 b1.le, KQ_real hr2 b2.le, ← Real.log_mul b1.ne' b2.ne']
  have hle : 1 + m * t + t ^ 2 ≤ (1 - r1 * t) * (1 - r2 * t) := by nlinarith
  have hint : IntervalIntegrable (fun y => Real.log (1 + y * t + t ^ 2)) volume lo hi := by
    refine ContinuousOn.intervalIntegrable_of_Icc hlt.le ?_
    refine ContinuousOn.log (by fun_prop) ?_
    intro y hy
    have : 2 ≤ y := h2.trans hy.1
    nlinarith
  refine (int_le_of_line hlt hint (B := Real.log (1 + m * t + t ^ 2))
    (c := t / (1 + m * t + t ^ 2)) ?_).trans ?_
  · intro y hy
    have hy2 : 2 < y := by linarith [hy.1]
    have hap : 0 < 1 + y * t + t ^ 2 := by nlinarith
    have hl : Real.log ((1 + y * t + t ^ 2) / (1 + m * t + t ^ 2)) ≤
        (1 + y * t + t ^ 2) / (1 + m * t + t ^ 2) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hap hb)
    rw [Real.log_div hap.ne' hb.ne'] at hl
    have e1 : (1 + y * t + t ^ 2) / (1 + m * t + t ^ 2) - 1 = t / (1 + m * t + t ^ 2) * (y - m) := by
      field_simp
      ring
    rw [e1] at hl
    rw [← hmdef]
    linarith
  · refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact Real.log_le_log hb hle

/-! ### Column panels -/

theorem col_pos {c t : ℝ} (h0 : 0 < t) (hc1 : c < 1) (hc2 : -1 < c) : 0 < 1 - 2 * c * t + t ^ 2 := by
  nlinarith [sq_nonneg (t - c), mul_pos (by linarith : 0 < 1 - c) (by linarith : 0 < 1 + c)]

/-- `-colK` is below its chord on a panel. -/
theorem col_panel {a b t : ℝ} (hab : a < b) (ha : -1 < a) (hb : b < 1) (h0 : 0 < t) :
    -(∫ y in a..b, colK t y) ≤ (b - a) * (-(colK t a + colK t b) / 2) := by
  have hint : IntervalIntegrable (fun y => -colK t y) volume a b :=
    (colK_int h0.ne' a b).neg
  have pa := col_pos h0 (by linarith : a < 1) ha
  have pb := col_pos h0 hb (by linarith : -1 < b)
  rw [← intervalIntegral.integral_neg]
  refine int_le_of_line hab hint
    (c := (-colK t b + colK t a) / (b - a)) ?_
  intro y hy
  have py := col_pos h0 (by linarith [hy.2] : y < 1) (by linarith [hy.1] : -1 < y)
  set l := (y - a) / (b - a) with hl
  have hba : 0 < b - a := by linarith
  have l0 : 0 ≤ l := div_nonneg (by linarith [hy.1]) hba.le
  have l1 : 0 ≤ 1 - l := by
    rw [hl, sub_nonneg, div_le_one hba]
    linarith [hy.2]
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr pa) (Set.mem_Ioi.mpr pb) l1 l0
    (by ring)
  simp only [smul_eq_mul] at hc
  have e : (1 - l) * (1 - 2 * a * t + t ^ 2) + l * (1 - 2 * b * t + t ^ 2) = 1 - 2 * y * t + t ^ 2 := by
    have : y = a + l * (b - a) := by
      rw [hl]; field_simp; ring
    rw [this]; ring
  rw [e] at hc
  unfold colK
  rw [abs_of_pos py, abs_of_pos pa, abs_of_pos pb]
  have e2 : (-Real.log (1 - 2 * b * t + t ^ 2) + Real.log (1 - 2 * a * t + t ^ 2)) / (b - a) *
      (y - (a + b) / 2) = -(l - 1 / 2) * (Real.log (1 - 2 * b * t + t ^ 2) -
        Real.log (1 - 2 * a * t + t ^ 2)) := by
    rw [hl]
    field_simp
    ring
  rw [e2]
  nlinarith

/-- A complex parameter that dominates a column point. -/
theorem col_atom {c t : ℝ} {q : ℂ} (hq : ‖q‖ < 1) (h0 : 0 < t) (h1 : t ≤ 1) (hc1 : c < 1)
    (hc2 : -1 < c) (hre : c ≤ (rq q).re) (hn : ‖rq q‖ ≤ 1) :
    -colK t c ≤ -(2 * KQ q t) := by
  have hne : 1 - rq q * (t : ℂ) ≠ 0 := one_sub_rq_ne hq ⟨by linarith, by linarith⟩
  have hp := col_pos h0 hc1 hc2
  have hsq : ‖1 - rq q * (t : ℂ)‖ ^ 2 ≤ 1 - 2 * c * t + t ^ 2 := by
    have e : ‖1 - rq q * (t : ℂ)‖ ^ 2 = 1 - 2 * (rq q).re * t + ‖rq q‖ ^ 2 * t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp
      ring
    rw [e]
    have : ‖rq q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (rq q)]
    nlinarith [sq_nonneg t]
  have hl := Real.log_le_log (by positivity) hsq
  rw [Real.log_pow] at hl
  unfold colK KQ
  rw [abs_of_pos hp]
  push_cast at hl
  linarith

/-! ### Endpoint barriers -/

theorem log_le_flip {t q r : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hr : r = 4 * q / (1 + q) ^ 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Real.log t ≤ KQ (q : ℂ) (1 - t) := by
  have hb : 0 ≤ 1 - r * (1 - t) := by nlinarith
  rw [KQ_real hr hb]
  exact Real.log_le_log h0 (by nlinarith)

theorem log_one_sub_le {t q r : ℝ} (h0 : 0 < t) (h1 : t < 1) (hr : r = 4 * q / (1 + q) ^ 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Real.log (1 - t) ≤ KQ (q : ℂ) t := by
  have hb : 0 ≤ 1 - r * t := by nlinarith
  rw [KQ_real hr hb]
  exact Real.log_le_log (by linarith) (by nlinarith)

theorem log_one_add_le {t q r : ℝ} (h0 : 0 < t) (hr : r = 4 * q / (1 + q) ^ 2)
    (hr1 : r ≤ -1) : Real.log (1 + t) ≤ KQ (q : ℂ) t := by
  have hb : 0 ≤ 1 - r * t := by nlinarith
  rw [KQ_real hr hb]
  exact Real.log_le_log (by linarith) (by nlinarith)

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### Ledger of a rounded power table -/

/-- A rounded power table of `v` stays within `n (2 ε + ρ)` of `v^n`. -/
theorem pow_ledger {v vh : ℂ} {p : ℕ → ℂ} {ε ρ : ℝ} {M : ℕ} (hv : ‖v‖ ≤ 1) (hε : ‖v - vh‖ ≤ ε)
    (h0 : p 0 = 1) (hs : ∀ n, ‖p (n + 1) - p n * vh‖ ≤ ρ)
    (hM : (M : ℝ) * (2 * ε + ρ) ≤ 1) :
    ∀ n ≤ M, ‖v ^ n - p n‖ ≤ n * (2 * ε + ρ) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hs 0)
  intro n
  induction n with
  | zero => intro _; simp [h0]
  | succ n ih =>
    intro hn
    have i := ih (by omega)
    have hnM : (n : ℝ) * (2 * ε + ρ) ≤ 1 := by
      refine le_trans ?_ hM
      have : (n : ℝ) ≤ M := by exact_mod_cast (by omega : n ≤ M)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hvn : ‖v ^ n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hv
    have hp : ‖p n‖ ≤ 2 := by
      have : ‖p n‖ ≤ ‖v ^ n‖ + ‖v ^ n - p n‖ := by
        have := norm_sub_le (v ^ n) (v ^ n - p n)
        simpa using this
      linarith
    have e : v ^ (n + 1) - p (n + 1) =
        v * (v ^ n - p n) + p n * (v - vh) - (p (n + 1) - p n * vh) := by
      rw [pow_succ]
      ring
    rw [e]
    have a1 : ‖v * (v ^ n - p n)‖ ≤ n * (2 * ε + ρ) := by
      rw [norm_mul]
      calc ‖v‖ * ‖v ^ n - p n‖ ≤ 1 * ‖v ^ n - p n‖ :=
            mul_le_mul_of_nonneg_right hv (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact i
    have a2 : ‖p n * (v - vh)‖ ≤ 2 * ε := by
      rw [norm_mul]
      exact mul_le_mul hp hε (norm_nonneg _) (by norm_num)
    have a3 := hs n
    calc _ ≤ ‖v * (v ^ n - p n) + p n * (v - vh)‖ + ‖p (n + 1) - p n * vh‖ := norm_sub_le _ _
      _ ≤ ‖v * (v ^ n - p n)‖ + ‖p n * (v - vh)‖ + ‖p (n + 1) - p n * vh‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by
          push_cast
          linarith

/-- The product of two table entries approximates the power of the sum. -/
theorem prod_ledger {u a b : ℂ} {i j : ℕ} {e1 e2 : ℝ} (hu : ‖u‖ ≤ 1)
    (h1 : ‖u ^ i - a‖ ≤ e1) (h2 : ‖u ^ j - b‖ ≤ e2) (hb : e2 ≤ 1) :
    ‖u ^ (i + j) - a * b‖ ≤ 2 * e1 + e2 := by
  have hi : ‖u ^ i‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
  have hj : ‖u ^ j‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
  have hb2 : ‖b‖ ≤ 2 := by
    have : ‖b‖ ≤ ‖u ^ j‖ + ‖u ^ j - b‖ := by
      have := norm_sub_le (u ^ j) (u ^ j - b)
      simpa using this
    linarith
  have e : u ^ (i + j) - a * b = u ^ i * (u ^ j - b) + (u ^ i - a) * b := by
    rw [pow_add]; ring
  rw [e]
  have a1 : ‖u ^ i * (u ^ j - b)‖ ≤ e2 := by
    rw [norm_mul]
    calc ‖u ^ i‖ * ‖u ^ j - b‖ ≤ 1 * ‖u ^ j - b‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
      _ ≤ e2 := by rw [one_mul]; exact h2
  have a2 : ‖(u ^ i - a) * b‖ ≤ e1 * 2 := by
    rw [norm_mul]
    exact mul_le_mul h1 hb2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have := norm_add_le (u ^ i * (u ^ j - b)) ((u ^ i - a) * b)
  linarith

/-! ### Atom sums and their truncation -/

/-- `T_n(-z) = (-1)^n T_n(z)`. -/
theorem basis_neg (n : ℕ) (z : ℝ) : basis n (-z) = (-1) ^ n * basis n z := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [basis]
  | more n h0 h1 =>
    rw [basis_add_two, basis_add_two, h0, h1]
    ring

theorem basis_one (n : ℕ) : basis n 1 = 1 := by
  have := basis_cos n 0
  simpa using this

/-- Value of the kernel at the left end. -/
theorem KQ_zero (q : ℂ) : KQ q 0 = 0 := by
  simp [KQ]

/-- Truncated series of an atom normalised at `t = 0`. -/
theorem atom_lo {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (L : ℕ) :
    |KQ q t + 2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re *
        (basis (n + 1) (2 * t - 1) - basis (n + 1) (-1)) / ((n : ℝ) + 1)| ≤
      4 * (‖q‖ ^ (L + 1) * (1 - ‖q‖)⁻¹ / ((L : ℝ) + 1)) := by
  have h1 := eK_bound hq (t := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ L
  have h2 := eK_bound hq (t := 0) ⟨by norm_num, by norm_num⟩ L
  have e : KQ q t + 2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re *
        (basis (n + 1) (2 * t - 1) - basis (n + 1) (-1)) / ((n : ℝ) + 1) =
      eK q t L - eK q 0 L := by
    unfold eK
    rw [KQ_zero]
    have : ∀ n ∈ Finset.range L, (q ^ (n + 1)).re *
        (basis (n + 1) (2 * t - 1) - basis (n + 1) (-1)) / ((n : ℝ) + 1) =
        (q ^ (n + 1)).re * basis (n + 1) (2 * t - 1) / ((n : ℝ) + 1) -
        (q ^ (n + 1)).re * basis (n + 1) (2 * 0 - 1) / ((n : ℝ) + 1) := by
      intro n _
      norm_num
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    ring
  rw [e]
  have := abs_sub (eK q t L) (eK q 0 L)
  linarith

/-- Truncated series of a flipped atom, normalised at `t = 1`. -/
theorem atom_hi {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (L : ℕ) :
    |KQ (-q) (1 - t) + 2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re *
        (basis (n + 1) (2 * t - 1) - 1) / ((n : ℝ) + 1)| ≤
      4 * (‖q‖ ^ (L + 1) * (1 - ‖q‖)⁻¹ / ((L : ℝ) + 1)) := by
  have hq' : ‖-q‖ < 1 := by rwa [norm_neg]
  have h := atom_lo hq' (t := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ L
  rw [norm_neg] at h
  refine le_of_eq_of_le ?_ h
  congr 2
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have e1 : 2 * (1 - t) - 1 = -(2 * t - 1) := by ring
  rw [e1, basis_neg, basis_neg (n + 1) 1, basis_one, neg_pow q (n + 1), ← Complex.ofReal_one,
    ← Complex.ofReal_neg, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hs : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← mul_pow]; simp
  have : (q ^ (n + 1)).re * (basis (n + 1) (2 * t - 1) - 1) =
      (-1) ^ (n + 1) * (q ^ (n + 1)).re * ((-1) ^ (n + 1) * basis (n + 1) (2 * t - 1) - (-1) ^ (n + 1) * 1) := by
    linear_combination (-(q ^ (n + 1)).re * (basis (n + 1) (2 * t - 1) - 1)) * hs
  rw [this]

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set

/-! ### The packed power-moment engine: kernel functions -/

/-- Strict evaluation of a natural number for the kernel. -/
def forceN {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- Strict evaluation of an integer for the kernel. -/
def forceI {α : Type} (x : ℤ) (k : ℤ → α) : α :=
  match x with
  | Int.ofNat n => forceN n fun m => k (Int.ofNat m)
  | Int.negSucc n => forceN n fun m => k (Int.negSucc m)

theorem forceN_eq {α : Type} (n : ℕ) (k : ℕ → α) : forceN n k = k n := by
  cases n <;> rfl

theorem forceI_eq {α : Type} (x : ℤ) (k : ℤ → α) : forceI x k = k x := by
  cases x <;> simp [forceI, forceN_eq]

/-- Rounded complex product at scale `D`. -/
def cmulF (D : ℤ) (x y : ℤ × ℤ) : ℤ × ℤ :=
  ((x.1 * y.1 - x.2 * y.2) / D, (x.1 * y.2 + x.2 * y.1) / D)

/-- `n` iterates of multiplication by `u` from `c`, and the next one. -/
def tabL (D : ℤ) (u : ℤ × ℤ) : ℕ → ℤ × ℤ → List (ℤ × ℤ) × (ℤ × ℤ)
  | 0, c => ([], c)
  | n + 1, c =>
    match tabL D u n (cmulF D c u) with
    | (l, e) => (c :: l, e)

/-- Packing at radix `B`. -/
def pk (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: t => a + B * pk B t

/-- One pairing level. -/
def pairUp (C : ℤ) : List ℤ → List ℤ
  | [] => []
  | [a] => [a]
  | a :: b :: t => (a + C * b) :: pairUp C t

/-- Tree packing (`pk` for lists of length at most `2^n`). -/
def packT : ℕ → ℤ → List ℤ → ℤ
  | 0, _, l => l.headD 0
  | n + 1, C, l => packT n (C * C) (pairUp C l)

/-- Parameters: scale `D`, block size `bs = 2^lg`, blocks `I = 2^lI`, radices `B`, `C = B^bs`. -/
structure EPar where
  D : ℤ
  bs : ℕ
  I : ℕ
  lg : ℕ
  lI : ℕ
  B : ℤ
  C : ℤ

/-- An entry: weight, and the complex number at scale `D`. -/
abbrev Ent := ℤ × ℤ × ℤ

/-- The packed contribution of one entry. -/
def term (p : EPar) (e : Ent) : ℤ :=
  match tabL p.D (e.2.1, e.2.2) p.bs (p.D, 0) with
  | (l, ub) =>
    match tabL p.D ub p.I (p.D, 0) with
    | (L, _) => e.1 * (packT p.lI p.C (L.map Prod.fst) * packT p.lg p.B (l.map Prod.fst) -
        packT p.lI p.C (L.map Prod.snd) * packT p.lg p.B (l.map Prod.snd))

/-- Sum of the packed contributions, strict at each entry. -/
def run (p : EPar) : List Ent → ℤ → ℤ
  | [], acc => acc
  | e :: t, acc => forceI (acc + term p e) fun a => run p t a

/-- Centred digit. -/
def sdig (B : ℤ) (X : ℤ) : ℤ := (X + B / 2) % B - B / 2

/-- Centred digits. -/
def unpk (B : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n + 1, X => forceI X fun x => sdig B x :: unpk B n ((x - sdig B x) / B)

/-! ### Algebra of packing -/

theorem run_eq (p : EPar) (E : List Ent) (acc : ℤ) :
    run p E acc = acc + (E.map (term p)).sum := by
  induction E generalizing acc with
  | nil => simp [run]
  | cons e t ih =>
    simp only [run, forceI_eq, ih, List.map_cons, List.sum_cons]
    ring

theorem pk_pairUp (C : ℤ) : ∀ l : List ℤ, pk C l = pk (C * C) (pairUp C l)
  | [] => rfl
  | [a] => by simp [pk, pairUp]
  | a :: b :: t => by
    have := pk_pairUp C t
    simp only [pk, pairUp]
    rw [← this]
    ring

theorem len_pairUp (C : ℤ) : ∀ l : List ℤ, 2 * (pairUp C l).length ≤ l.length + 1
  | [] => by simp [pairUp]
  | [a] => by simp [pairUp]
  | a :: b :: t => by
    have := len_pairUp C t
    simp only [pairUp, List.length_cons]
    omega

theorem packT_eq : ∀ (n : ℕ) (C : ℤ) (l : List ℤ), l.length ≤ 2 ^ n → packT n C l = pk C l
  | 0, C, l, h => by
    cases l with
    | nil => rfl
    | cons a t =>
      have : t = [] := by
        simp at h
        exact h
      subst this
      simp [packT, pk]
  | n + 1, C, l, h => by
    have h2 := len_pairUp C l
    have : (pairUp C l).length ≤ 2 ^ n := by
      rw [pow_succ] at h
      omega
    simp only [packT]
    rw [packT_eq n _ _ this, ← pk_pairUp]

theorem pk_append (B : ℤ) : ∀ a b : List ℤ, pk B (a ++ b) = pk B a + B ^ a.length * pk B b
  | [], b => by simp [pk]
  | x :: t, b => by
    simp only [List.cons_append, pk, pk_append B t b, List.length_cons]
    ring

/-- The digit list of one entry. -/
def rows (w : ℤ) (U P : List (ℤ × ℤ)) : List ℤ :=
  U.flatMap fun a => P.map fun b => w * (a.1 * b.1 - a.2 * b.2)

theorem pk_row (B w : ℤ) (a : ℤ × ℤ) : ∀ P : List (ℤ × ℤ),
    pk B (P.map fun b => w * (a.1 * b.1 - a.2 * b.2)) =
      w * (a.1 * pk B (P.map Prod.fst) - a.2 * pk B (P.map Prod.snd))
  | [] => by simp [pk]
  | b :: t => by
    simp only [List.map_cons, pk, pk_row B w a t]
    ring

theorem pk_rows (B w : ℤ) (P : List (ℤ × ℤ)) : ∀ U : List (ℤ × ℤ),
    pk B (rows w U P) = w * (pk (B ^ P.length) (U.map Prod.fst) * pk B (P.map Prod.fst) -
      pk (B ^ P.length) (U.map Prod.snd) * pk B (P.map Prod.snd))
  | [] => by simp [rows, pk]
  | a :: t => by
    have ih := pk_rows B w P t
    unfold rows at ih ⊢
    simp only [List.flatMap_cons, List.map_cons, pk, pk_append, pk_row, List.length_map]
    rw [ih]
    ring

theorem len_rows (w : ℤ) (U P : List (ℤ × ℤ)) : (rows w U P).length = U.length * P.length := by
  induction U with
  | nil => simp [rows]
  | cons a t ih =>
    unfold rows at ih ⊢
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    ring

theorem gd_left {a : List ℤ} (b : List ℤ) {n : ℕ} (h : n < a.length) :
    (a ++ b).getD n 0 = a.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gd_right (a b : List ℤ) (n : ℕ) : (a ++ b).getD (a.length + n) 0 = b.getD n 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_rows (w : ℤ) (P : List (ℤ × ℤ)) {j : ℕ} (hj : j < P.length) :
    ∀ (U : List (ℤ × ℤ)) (i : ℕ), i < U.length →
      (rows w U P).getD (i * P.length + j) 0 =
        w * ((U.getD i (0, 0)).1 * (P.getD j (0, 0)).1 - (U.getD i (0, 0)).2 * (P.getD j (0, 0)).2)
  | [], i, h => by simp at h
  | a :: t, 0, _ => by
    unfold rows
    simp only [List.flatMap_cons, zero_mul, zero_add]
    rw [gd_left _ (by simpa using hj)]
    simp [hj]
  | a :: t, i + 1, h => by
    have ih := getD_rows w P hj t i (by simpa using h)
    unfold rows at ih ⊢
    simp only [List.flatMap_cons]
    have e : (i + 1) * P.length + j = P.length + (i * P.length + j) := by ring
    have e2 : P.length = (P.map fun b => w * (a.1 * b.1 - a.2 * b.2)).length := by simp
    rw [e]
    conv_lhs => rw [show P.length + (i * P.length + j) =
      (P.map fun b => w * (a.1 * b.1 - a.2 * b.2)).length + (i * P.length + j) by simp]
    rw [gd_right, ih]
    simp

/-! ### Digits -/

theorem sdig_add {B a Y : ℤ} (hB : 0 < B) (hB2 : 2 ∣ B) (h1 : -(B / 2) ≤ a) (h2 : a < B / 2) :
    sdig B (a + B * Y) = a := by
  unfold sdig
  have e : a + B * Y + B / 2 = (a + B / 2) + B * Y := by ring
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  ring

theorem unpk_pk {B : ℤ} (hB : 0 < B) (hB2 : 2 ∣ B) : ∀ l : List ℤ,
    (∀ a ∈ l, -(B / 2) ≤ a ∧ a < B / 2) → unpk B l.length (pk B l) = l
  | [], _ => rfl
  | a :: t, h => by
    have h1 := h a (by simp)
    have ih := unpk_pk hB hB2 t fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, unpk, pk, forceI_eq]
    rw [sdig_add hB hB2 h1.1 h1.2]
    have e : (a + B * pk B t - a) / B = pk B t := by
      rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hB.ne']
    rw [e, ih]

end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set

/-! ### The tables -/

/-- Iterates of the rounded product. -/
def itr (D : ℤ) (u c : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => c
  | n + 1 => cmulF D (itr D u c n) u

theorem itr_shift (D : ℤ) (u c : ℤ × ℤ) (n : ℕ) :
    itr D u (cmulF D c u) n = itr D u c (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [itr]; rw [ih]; rfl

theorem tabL_eq (D : ℤ) (u : ℤ × ℤ) (n : ℕ) (c : ℤ × ℤ) :
    tabL D u n c = ((List.range n).map (itr D u c), itr D u c n) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [tabL, ih]
    refine Prod.ext ?_ ?_
    · simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      simp [itr_shift]
    · exact itr_shift D u c n

noncomputable section

/-- The complex number of a scaled pair. -/
def toC (D : ℤ) (x : ℤ × ℤ) : ℂ := ⟨(x.1 : ℝ) / D, (x.2 : ℝ) / D⟩

theorem floor_err {x D : ℤ} (hD : 0 < D) : |((x / D : ℤ) : ℝ) / D - (x : ℝ) / D / D| ≤ 1 / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have e := Int.mul_ediv_add_emod x D
  have m0 := Int.emod_nonneg x hD.ne'
  have m1 := Int.emod_lt_of_pos x hD
  have er : (D : ℝ) * ((x / D : ℤ) : ℝ) + ((x % D : ℤ) : ℝ) = x := by exact_mod_cast e
  have m0r : (0 : ℝ) ≤ ((x % D : ℤ) : ℝ) := by exact_mod_cast m0
  have m1r : ((x % D : ℤ) : ℝ) ≤ D := by exact_mod_cast m1.le
  have : ((x / D : ℤ) : ℝ) / D - (x : ℝ) / D / D = -((x % D : ℤ) : ℝ) / D / D := by
    rw [← er]
    field_simp
    ring
  rw [this, abs_div, abs_div, abs_neg, abs_of_nonneg m0r, abs_of_pos hDr]
  rw [div_le_div_iff_of_pos_right hDr]
  rw [div_le_one hDr]
  exact m1r

theorem cmulF_err {D : ℤ} (hD : 0 < D) (x y : ℤ × ℤ) :
    ‖toC D (cmulF D x y) - toC D x * toC D y‖ ≤ 2 / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 := floor_err (x := x.1 * y.1 - x.2 * y.2) hD
  have h2 := floor_err (x := x.1 * y.2 + x.2 * y.1) hD
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (toC D (cmulF D x y) - toC D x * toC D y).re =
      (((x.1 * y.1 - x.2 * y.2) / D : ℤ) : ℝ) / D - ((x.1 * y.1 - x.2 * y.2 : ℤ) : ℝ) / D / D := by
    simp only [toC, cmulF, Complex.sub_re, Complex.mul_re]
    push_cast
    field_simp
  have e2 : (toC D (cmulF D x y) - toC D x * toC D y).im =
      (((x.1 * y.2 + x.2 * y.1) / D : ℤ) : ℝ) / D - ((x.1 * y.2 + x.2 * y.1 : ℤ) : ℝ) / D / D := by
    simp only [toC, cmulF, Complex.sub_im, Complex.mul_im]
    push_cast
    field_simp
  rw [e1, e2]
  have : (2 : ℝ) / D = 1 / D + 1 / D := by ring
  linarith

theorem toC_one {D : ℤ} (hD : 0 < D) : toC D (D, 0) = 1 := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  apply Complex.ext <;> simp [toC, hDr]

theorem toC_mul_re (D : ℤ) (a b : ℤ × ℤ) :
    (toC D a * toC D b).re = ((a.1 * b.1 - a.2 * b.2 : ℤ) : ℝ) / D / D := by
  by_cases hD : (D : ℝ) = 0
  · simp [toC, hD]
  simp only [toC, Complex.mul_re]
  push_cast
  field_simp

/-- Everything known about the table of one entry. -/
theorem entry_ledger {D : ℤ} (hD : 0 < D) {u : ℂ} {uh : ℤ × ℤ} {ε : ℝ} {bs I : ℕ} (hu : ‖u‖ ≤ 1)
    (hε : ‖u - toC D uh‖ ≤ ε) (hb : (bs : ℝ) * (2 * ε + 2 / D) ≤ 1)
    (hI : (I : ℝ) * (2 * ((bs : ℝ) * (2 * ε + 2 / D)) + 2 / D) ≤ 1) {i j : ℕ} (hi : i ≤ I)
    (hj : j ≤ bs) :
    ‖u ^ (bs * i + j) - toC D (itr D (itr D uh (D, 0) bs) (D, 0) i) * toC D (itr D uh (D, 0) j)‖ ≤
      2 * ((I : ℝ) * (2 * ((bs : ℝ) * (2 * ε + 2 / D)) + 2 / D)) + (bs : ℝ) * (2 * ε + 2 / D) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  set d := 2 * ε + 2 / (D : ℝ) with hd
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have L1 := pow_ledger (v := u) (vh := toC D uh) (p := fun n => toC D (itr D uh (D, 0) n))
    (ε := ε) (ρ := 2 / D) (M := bs) hu hε (toC_one hD) (fun n => cmulF_err hD _ _) hb
  have l1j := L1 j hj
  have l1b := L1 bs le_rfl
  have hv : ‖u ^ bs‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
  have L2 := pow_ledger (v := u ^ bs) (vh := toC D (itr D uh (D, 0) bs))
    (p := fun n => toC D (itr D (itr D uh (D, 0) bs) (D, 0) n))
    (ε := (bs : ℝ) * d) (ρ := 2 / D) (M := I) hv l1b (toC_one hD) (fun n => cmulF_err hD _ _) hI
  have l2 := L2 i hi
  rw [← pow_mul] at l2
  have hjd : (j : ℝ) * d ≤ (bs : ℝ) * d :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hd0
  have hid : (i : ℝ) * (2 * ((bs : ℝ) * d) + 2 / D) ≤ (I : ℝ) * (2 * ((bs : ℝ) * d) + 2 / D) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (by positivity)
  have := prod_ledger hu (l2.trans hid) (l1j.trans hjd) hb
  exact this

/-! ### Digits of a list of entries -/

/-- Digit list of an entry. -/
def rowsE (p : EPar) (e : Ent) : List ℤ :=
  rows e.1 ((List.range p.I).map (itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0)))
    ((List.range p.bs).map (itr p.D (e.2.1, e.2.2) (p.D, 0)))

/-- Well-formed parameters. -/
structure EPar.OK (p : EPar) : Prop where
  D_pos : 0 < p.D
  B_pos : 0 < p.B
  B_even : 2 ∣ p.B
  C_eq : p.C = p.B ^ p.bs
  lg : p.bs ≤ 2 ^ p.lg
  lI : p.I ≤ 2 ^ p.lI

theorem term_eq {p : EPar} (h : p.OK) (e : Ent) : term p e = pk p.B (rowsE p e) := by
  unfold term rowsE
  simp only [tabL_eq]
  rw [packT_eq p.lI _ _ (by simpa using h.lI), packT_eq p.lI _ _ (by simpa using h.lI),
    packT_eq p.lg _ _ (by simpa using h.lg), packT_eq p.lg _ _ (by simpa using h.lg), pk_rows]
  simp only [List.length_map, List.length_range, h.C_eq]

theorem len_rowsE (p : EPar) (e : Ent) : (rowsE p e).length = p.I * p.bs := by
  simp [rowsE, len_rows]

theorem getD_rowsE (p : EPar) (e : Ent) {i j : ℕ} (hi : i < p.I) (hj : j < p.bs) :
    (rowsE p e).getD (p.bs * i + j) 0 =
      e.1 * ((itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0) i).1 *
          (itr p.D (e.2.1, e.2.2) (p.D, 0) j).1 -
        (itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0) i).2 *
          (itr p.D (e.2.1, e.2.2) (p.D, 0) j).2) := by
  unfold rowsE
  have := getD_rows e.1 ((List.range p.bs).map (itr p.D (e.2.1, e.2.2) (p.D, 0)))
    (j := j) (by simpa using hj)
    ((List.range p.I).map (itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0))) i
    (by simpa using hi)
  simp only [List.length_map, List.length_range] at this
  rw [mul_comm p.bs i, this]
  have a1 : ((List.range p.I).map (itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0))).getD i
      (0, 0) = itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0) i := by
    simp [List.getD_eq_getElem?_getD, hi]
  have a2 : ((List.range p.bs).map (itr p.D (e.2.1, e.2.2) (p.D, 0))).getD j (0, 0) =
      itr p.D (e.2.1, e.2.2) (p.D, 0) j := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [a1, a2]

theorem pk_eq_sum (B : ℤ) : ∀ l : List ℤ,
    pk B l = ∑ n ∈ Finset.range l.length, l.getD n 0 * B ^ n
  | [] => by simp [pk]
  | a :: t => by
    rw [pk, pk_eq_sum B t, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring

/-- Digit-wise sum of the entries. -/
def dsum (p : EPar) (E : List Ent) : List ℤ :=
  (List.range (p.I * p.bs)).map fun n => (E.map fun e => (rowsE p e).getD n 0).sum

theorem len_dsum (p : EPar) (E : List Ent) : (dsum p E).length = p.I * p.bs := by simp [dsum]

theorem getD_dsum (p : EPar) (E : List Ent) {n : ℕ} (hn : n < p.I * p.bs) :
    (dsum p E).getD n 0 = (E.map fun e => (rowsE p e).getD n 0).sum := by
  simp [dsum, List.getD_eq_getElem?_getD, hn]

theorem pk_dsum (p : EPar) (E : List Ent) : pk p.B (dsum p E) = (E.map fun e => pk p.B (rowsE p e)).sum := by
  rw [pk_eq_sum, len_dsum]
  have : ∀ n ∈ Finset.range (p.I * p.bs), (dsum p E).getD n 0 * p.B ^ n =
      (E.map fun e => (rowsE p e).getD n 0).sum * p.B ^ n := by
    intro n hn
    rw [getD_dsum p E (Finset.mem_range.mp hn)]
  rw [Finset.sum_congr rfl this]
  clear this
  induction E with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih]
    rw [pk_eq_sum p.B (rowsE p e), len_rowsE]

/-- The moments of an entry list: digits of the packed sum. -/
def moments (p : EPar) (E : List Ent) : List ℤ := unpk p.B (p.I * p.bs) (run p E 0)

theorem moments_eq {p : EPar} (h : p.OK) (E : List Ent)
    (hg : ∀ n < p.I * p.bs, -(p.B / 2) ≤ (dsum p E).getD n 0 ∧ (dsum p E).getD n 0 < p.B / 2) :
    moments p E = dsum p E := by
  have e : run p E 0 = pk p.B (dsum p E) := by
    rw [run_eq, zero_add, pk_dsum]
    congr 1
    exact List.map_congr_left fun e _ => term_eq h e
  unfold moments
  rw [e, ← len_dsum p E]
  refine unpk_pk h.B_pos h.B_even _ fun a ha => ?_
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem ha
  have := hg n (by rwa [len_dsum] at hn)
  simpa [List.getD_eq_getElem?_getD, hn] using this

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set

noncomputable section

/-- The error of the table of an entry. -/
def etaOf (p : EPar) (ε : ℝ) : ℝ :=
  2 * ((p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * ε + 2 / p.D)) + 2 / p.D)) +
    (p.bs : ℝ) * (2 * ε + 2 / p.D)

/-- A real weight, a true complex number and its entry. -/
abbrev Spec := ℝ × ℂ × Ent

/-- The integer value of one table product. -/
def tv (p : EPar) (e : Ent) (i j : ℕ) : ℤ :=
  (itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0) i).1 *
      (itr p.D (e.2.1, e.2.2) (p.D, 0) j).1 -
    (itr p.D (itr p.D (e.2.1, e.2.2) (p.D, 0) p.bs) (p.D, 0) i).2 *
      (itr p.D (e.2.1, e.2.2) (p.D, 0) j).2

theorem tv_close {p : EPar} (h : p.OK) {x : Spec} {ε : ℝ} (hu : ‖x.2.1‖ ≤ 1)
    (hε : ‖x.2.1 - toC p.D (x.2.2.2.1, x.2.2.2.2)‖ ≤ ε)
    (hb : (p.bs : ℝ) * (2 * ε + 2 / p.D) ≤ 1)
    (hI : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * ε + 2 / p.D)) + 2 / p.D) ≤ 1)
    {i j : ℕ} (hi : i < p.I) (hj : j < p.bs) :
    |(x.2.1 ^ (p.bs * i + j)).re - (tv p x.2.2 i j : ℝ) / p.D / p.D| ≤ etaOf p ε := by
  have L := entry_ledger h.D_pos hu hε hb hI hi.le hj.le
  have e : (tv p x.2.2 i j : ℝ) / p.D / p.D =
      (toC p.D (itr p.D (itr p.D (x.2.2.2.1, x.2.2.2.2) (p.D, 0) p.bs) (p.D, 0) i) *
        toC p.D (itr p.D (x.2.2.2.1, x.2.2.2.2) (p.D, 0) j)).re := by
    rw [toC_mul_re]
    rfl
  rw [e, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans L

theorem re_pow_le {u : ℂ} (hu : ‖u‖ ≤ 1) (n : ℕ) : |(u ^ n).re| ≤ 1 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hu

/-- **Moments of an entry list.** -/
theorem moment_close {p : EPar} (h : p.OK) {L : List Spec} {ε : ℝ} {Dw : ℝ} (hDw : 0 < Dw)
    (hu : ∀ x ∈ L, ‖x.2.1‖ ≤ 1)
    (hε : ∀ x ∈ L, ‖x.2.1 - toC p.D (x.2.2.2.1, x.2.2.2.2)‖ ≤ ε)
    (hb : (p.bs : ℝ) * (2 * ε + 2 / p.D) ≤ 1)
    (hI : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * ε + 2 / p.D)) + 2 / p.D) ≤ 1)
    (hη : etaOf p ε ≤ 1)
    (hg : ((L.map fun x => |x.2.2.1|).sum) * (2 * p.D ^ 2) < p.B / 2) {n : ℕ}
    (hn : n < p.I * p.bs) :
    |(L.map fun x => x.1 * (x.2.1 ^ n).re).sum -
        ((moments p (L.map fun x => x.2.2)).getD n 0 : ℝ) / (Dw * p.D ^ 2)| ≤
      (L.map fun x => |x.1 - (x.2.2.1 : ℝ) / Dw| + |(x.2.2.1 : ℝ)| / Dw * etaOf p ε).sum := by
  have hDr : (0 : ℝ) < p.D := by exact_mod_cast h.D_pos
  have hbs : 0 < p.bs := by
    rcases Nat.eq_zero_or_pos p.bs with h0 | h0
    · simp [h0] at hn
    · exact h0
  have hij : ∀ m < p.I * p.bs, p.bs * (m / p.bs) + m % p.bs = m ∧ m / p.bs < p.I ∧ m % p.bs < p.bs :=
    fun m hm => ⟨Nat.div_add_mod m p.bs, Nat.div_lt_of_lt_mul (by rwa [mul_comm]),
      Nat.mod_lt _ hbs⟩
  -- one entry
  have key : ∀ x ∈ L, ∀ i j, i < p.I → j < p.bs → |tv p x.2.2 i j| ≤ 2 * p.D ^ 2 := by
    intro x hx i j hi hj
    have c := tv_close h (hu x hx) (hε x hx) hb hI hi hj
    have r := re_pow_le (hu x hx) (p.bs * i + j)
    have : |(tv p x.2.2 i j : ℝ) / p.D / p.D| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub ((tv p x.2.2 i j : ℝ) / p.D / p.D)
        ((x.2.1 ^ (p.bs * i + j)).re)
      rw [abs_sub_comm ((tv p x.2.2 i j : ℝ) / p.D / p.D)] at this
      linarith
    rw [abs_div, abs_div, abs_of_pos hDr, div_div, div_le_iff₀ (by positivity)] at this
    have h2 : |(tv p x.2.2 i j : ℝ)| ≤ 2 * (p.D : ℝ) ^ 2 := by nlinarith
    exact_mod_cast h2
  have dg : ∀ e : Ent, ∀ m < p.I * p.bs, (rowsE p e).getD m 0 =
      e.1 * tv p e (m / p.bs) (m % p.bs) := by
    intro e m hm
    obtain ⟨a, b, c⟩ := hij m hm
    have := getD_rowsE p e b c
    rw [a] at this
    rw [this]
    rfl
  have sumE : ∀ m < p.I * p.bs, ((L.map fun x => x.2.2).map fun e => (rowsE p e).getD m 0).sum =
      (L.map fun x => x.2.2.1 * tv p x.2.2 (m / p.bs) (m % p.bs)).sum := by
    intro m hm
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => dg x.2.2 m hm
  have bnd : ∀ (M : List Spec), (∀ x ∈ M, x ∈ L) → ∀ i j, i < p.I → j < p.bs →
      |(M.map fun x => x.2.2.1 * tv p x.2.2 i j).sum| ≤
        (M.map fun x => |x.2.2.1|).sum * (2 * p.D ^ 2) := by
    intro M hM i j hi hj
    induction M with
    | nil => simp
    | cons x t ih =>
      have i1 := ih fun y hy => hM y (List.mem_cons_of_mem _ hy)
      have k := key x (hM x List.mem_cons_self) i j hi hj
      simp only [List.map_cons, List.sum_cons, add_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ i1)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left k (abs_nonneg _)
  have hmom : moments p (L.map fun x => x.2.2) = dsum p (L.map fun x => x.2.2) := by
    refine moments_eq h _ fun m hm => ?_
    rw [getD_dsum p _ hm, sumE m hm]
    obtain ⟨_, b, c⟩ := hij m hm
    have := bnd L (fun _ hx => hx) _ _ b c
    have h3 := this.trans_lt hg
    rw [abs_lt] at h3
    exact ⟨h3.1.le, h3.2⟩
  rw [hmom, getD_dsum p _ hn, sumE n hn]
  obtain ⟨a, b, c⟩ := hij n hn
  set i := n / p.bs
  set j := n % p.bs
  have hgen : ∀ (M : List Spec), (∀ x ∈ M, x ∈ L) →
      |(M.map fun x => x.1 * (x.2.1 ^ n).re).sum -
        (((M.map fun x => x.2.2.1 * tv p x.2.2 i j).sum : ℤ) : ℝ) / (Dw * p.D ^ 2)| ≤
      (M.map fun x => |x.1 - (x.2.2.1 : ℝ) / Dw| + |(x.2.2.1 : ℝ)| / Dw * etaOf p ε).sum := by
    intro M hM
    induction M with
    | nil => simp
    | cons x t ih =>
      have i1 := ih fun y hy => hM y (List.mem_cons_of_mem _ hy)
      have hx := hM x List.mem_cons_self
      have c1 := tv_close h (hu x hx) (hε x hx) hb hI (i := i) (j := j) b c
      rw [a] at c1
      have r := re_pow_le (hu x hx) n
      simp only [List.map_cons, List.sum_cons]
      rw [Int.cast_add, Int.cast_mul]
      set A := (t.map fun y => y.1 * (y.2.1 ^ n).re).sum
      set Bq := (((t.map fun y => y.2.2.1 * tv p y.2.2 i j).sum : ℤ) : ℝ)
      have e : x.1 * (x.2.1 ^ n).re + A -
          ((x.2.2.1 : ℝ) * (tv p x.2.2 i j : ℝ) + Bq) / (Dw * (p.D : ℝ) ^ 2) =
          ((x.1 - (x.2.2.1 : ℝ) / Dw) * (x.2.1 ^ n).re +
            (x.2.2.1 : ℝ) / Dw * ((x.2.1 ^ n).re - (tv p x.2.2 i j : ℝ) / p.D / p.D)) +
          (A - Bq / (Dw * (p.D : ℝ) ^ 2)) := by
        field_simp
        ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ i1)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        calc _ ≤ |x.1 - (x.2.2.1 : ℝ) / Dw| * 1 := mul_le_mul_of_nonneg_left r (abs_nonneg _)
          _ = _ := mul_one _
      · rw [abs_mul, abs_div, abs_of_pos hDw]
        exact mul_le_mul_of_nonneg_left c1 (by positivity)
  exact hgen L fun _ hx => hx

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

/-! ### Atom groups: from moments to a Chebyshev list -/

/-- Value of `T_k` at the normalisation point, `+1` if `s`, else `-1`. -/
def tauZ (s : Bool) (k : ℕ) : ℤ := if s then 1 else if k % 2 = 0 then 1 else -1

/-- Coefficients `-2 m / (k Sc)` at scale `dP`, floor. -/
def coefL (dP Sc : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, m :: t => (-(2 * m * dP)) / ((k : ℤ) * Sc) :: coefL dP Sc (k + 1) t

/-- `∑ c_i τ(k+i)`. -/
def hsum (s : Bool) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | k, c :: t => c * tauZ s k + hsum s (k + 1) t

/-- The Chebyshev list of a group from its moments. -/
def grpList (s : Bool) (dP Sc : ℤ) : List ℤ → List ℤ
  | [] => []
  | _ :: rest => (-hsum s 1 (coefL dP Sc 1 rest)) :: coefL dP Sc 1 rest

/-! GrpN fix (PHASE1-UNIT-COSTS §1.5): the check lists of the Grp modules are computed with the scale
`(dP, Sc) = (1, 2^16 D^2)` instead of `(2^80, 2^96 D^2)`: every quotient is equal (a common factor `2^80`
cancels in the floor division, `grpList_scale`), but no numerator or divisor is a multiple of `2^64`, so the
kernel's hash of a `Nat` literal (low 64 bits) no longer collides (A). `coefLs`, `grpListS` are the strict
forms (B): each quotient and each index is a literal when it is used. Statements and data are unchanged. -/

/-- Strict `coefL`. -/
def coefLs (dP Sc : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, m :: t =>
    forceI ((-(2 * m * dP)) / ((k : ℤ) * Sc)) fun q =>
      forceN k fun k' => q :: coefLs dP Sc (k' + 1) t

theorem coefLs_eq (dP Sc : ℤ) : ∀ (l : List ℤ) (k : ℕ), coefLs dP Sc k l = coefL dP Sc k l
  | [], _ => rfl
  | m :: t, k => by
    simp only [coefLs, coefL, forceI_eq, forceN_eq]
    rw [coefLs_eq dP Sc t (k + 1)]

/-- Strict `grpList`. -/
def grpListS (s : Bool) (dP Sc : ℤ) : List ℤ → List ℤ
  | [] => []
  | _ :: rest => forceI (-hsum s 1 (coefLs dP Sc 1 rest)) fun h => h :: coefLs dP Sc 1 rest

theorem grpListS_eq (s : Bool) (dP Sc : ℤ) (l : List ℤ) :
    grpListS s dP Sc l = grpList s dP Sc l := by
  cases l with
  | nil => rfl
  | cons a rest => simp only [grpListS, grpList, forceI_eq, coefLs_eq]

theorem coefL_scale (c dP Sc : ℤ) (hc : 0 < c) : ∀ (l : List ℤ) (k : ℕ),
    coefL (c * dP) (c * Sc) k l = coefL dP Sc k l
  | [], _ => rfl
  | m :: t, k => by
    simp only [coefL]
    rw [coefL_scale c dP Sc hc t (k + 1)]
    congr 1
    have e1 : -(2 * m * (c * dP)) = c * (-(2 * m * dP)) := by ring
    have e2 : (k : ℤ) * (c * Sc) = c * ((k : ℤ) * Sc) := by ring
    rw [e1, e2]
    exact Int.mul_ediv_mul_of_pos _ _ hc

theorem grpList_scale (s : Bool) (c dP Sc : ℤ) (hc : 0 < c) (l : List ℤ) :
    grpList s (c * dP) (c * Sc) l = grpList s dP Sc l := by
  cases l with
  | nil => rfl
  | cons a rest => simp only [grpList, coefL_scale c dP Sc hc]

noncomputable section

/-- The kernel of an atom. -/
def av (s : Bool) (q : ℂ) (t : ℝ) : ℝ := if s then KQ (-q) (1 - t) else KQ q t

theorem tauZ_eq (s : Bool) (k : ℕ) : ((tauZ s k : ℤ) : ℝ) = basis k (if s then 1 else -1) := by
  cases s
  · simp only [tauZ, Bool.false_eq_true, if_false]
    have := basis_neg k 1
    rw [basis_one, mul_one] at this
    rw [this]
    rcases Nat.even_or_odd k with h | h
    · rw [h.neg_one_pow, if_pos (Nat.even_iff.mp h)]
      simp
    · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.mp h]; norm_num)]
      simp
  · simp [tauZ, basis_one]

theorem atom_series (s : Bool) {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (L : ℕ) :
    |av s q t + 2 * ∑ n ∈ Finset.range L, (q ^ (n + 1)).re *
        (basis (n + 1) (2 * t - 1) - (tauZ s (n + 1) : ℝ)) / ((n : ℝ) + 1)| ≤
      4 * (‖q‖ ^ (L + 1) * (1 - ‖q‖)⁻¹ / ((L : ℝ) + 1)) := by
  cases s
  · have := atom_lo hq ht L
    simp only [av, Bool.false_eq_true, if_false]
    simp only [tauZ_eq, Bool.false_eq_true, if_false]
    exact this
  · have := atom_hi hq ht L
    simp only [av, if_true]
    simp only [tauZ_eq, if_true, basis_one]
    exact this

theorem abs_tau_sub_le (s : Bool) (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |basis k x - (tauZ s k : ℝ)| ≤ 2 := by
  have h1 := abs_basis_le_one k hx
  have h2 : |((tauZ s k : ℤ) : ℝ)| ≤ 1 := by
    rw [tauZ_eq]
    refine abs_basis_le_one k ?_
    cases s <;> simp
  have := abs_sub (basis k x) ((tauZ s k : ℤ) : ℝ)
  linarith

/-- The floor coefficient is close to the real one. -/
theorem coef_err {m dP Sc : ℤ} {k : ℕ} (hk : 0 < k) (hdP : 0 < dP) (hSc : 0 < Sc) :
    |(((-(2 * m * dP)) / ((k : ℤ) * Sc) : ℤ) : ℝ) / dP - (-2 * ((m : ℝ) / Sc) / k)| ≤ 1 / dP := by
  have hkZ : (0 : ℤ) < (k : ℤ) * Sc := by positivity
  have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
  have hSr : (0 : ℝ) < Sc := by exact_mod_cast hSc
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  set X : ℤ := -(2 * m * dP)
  set Y : ℤ := (k : ℤ) * Sc
  have e := Int.mul_ediv_add_emod X Y
  have m0 := Int.emod_nonneg X hkZ.ne'
  have m1 := Int.emod_lt_of_pos X hkZ
  have Yr : (Y : ℝ) = k * Sc := by simp [Y]
  have hYr : (0 : ℝ) < Y := by rw [Yr]; positivity
  have er : (Y : ℝ) * ((X / Y : ℤ) : ℝ) + ((X % Y : ℤ) : ℝ) = X := by exact_mod_cast e
  have m0r : (0 : ℝ) ≤ ((X % Y : ℤ) : ℝ) := by exact_mod_cast m0
  have m1r : ((X % Y : ℤ) : ℝ) ≤ Y := by exact_mod_cast m1.le
  have Xr : (X : ℝ) = -(2 * m * dP) := by simp [X]
  have : ((X / Y : ℤ) : ℝ) / dP - (-2 * ((m : ℝ) / Sc) / k) = -(((X % Y : ℤ) : ℝ) / Y) / dP := by
    have a : ((X / Y : ℤ) : ℝ) = ((X : ℝ) - ((X % Y : ℤ) : ℝ)) / Y := by
      rw [← er]; field_simp; ring
    rw [a, Xr, Yr]
    field_simp
    ring
  rw [this, abs_div, abs_neg, abs_of_pos hdr, div_le_div_iff_of_pos_right hdr, abs_of_nonneg
    (div_nonneg m0r hYr.le), div_le_one hYr]
  exact m1r

theorem coef_close {dP Sc : ℤ} (hdP : 0 < dP) (hSc : 0 < Sc) (s : Bool) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) {S : ℕ → ℝ} {Em : ℝ} :
    ∀ (l : List ℤ) (k : ℕ), 0 < k → (∀ i < l.length, |S (k + i) - (l.getD i 0 : ℝ) / Sc| ≤ Em) →
      |∑ i ∈ Finset.range l.length, (-2 * S (k + i) / ((k + i : ℕ) : ℝ)) *
          (basis (k + i) x - (tauZ s (k + i) : ℝ)) -
        (rawSum (coefL dP Sc k l) k x - (hsum s k (coefL dP Sc k l) : ℝ)) / dP| ≤
      (l.length : ℝ) * (2 * (1 / dP + 2 * Em))
  | [], k, _, _ => by simp [coefL, hsum]
  | m :: t, k, hk, h => by
    have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ih := coef_close hdP hSc s hx t (k + 1) (by omega) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, add_zero] at h0
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [coefL, rawSum_cons, hsum, add_zero]
    set a : ℤ := (-(2 * m * dP)) / ((k : ℤ) * Sc) with ha
    have ca := coef_err (m := m) hk hdP hSc
    rw [← ha] at ca
    have ht := abs_tau_sub_le s k hx
    set R := rawSum (coefL dP Sc (k + 1) t) (k + 1) x
    set Hs := ((hsum s (k + 1) (coefL dP Sc (k + 1) t) : ℤ) : ℝ)
    set Sum1 := ∑ i ∈ Finset.range t.length, (-2 * S (k + (i + 1)) / ((k + (i + 1) : ℕ) : ℝ)) *
      (basis (k + (i + 1)) x - (tauZ s (k + (i + 1)) : ℝ))
    have ih' : |Sum1 - (R - Hs) / dP| ≤ (t.length : ℝ) * (2 * (1 / dP + 2 * Em)) := by
      refine le_of_eq_of_le ?_ ih
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : k + 1 + i = k + (i + 1) := by omega
      rw [e]
    have e : (Sum1 + -2 * S k / (k : ℝ) * (basis k x - (tauZ s k : ℝ))) -
        ((a : ℝ) * basis k x + R - (((a * tauZ s k + hsum s (k + 1) (coefL dP Sc (k + 1) t) : ℤ)) : ℝ)) / dP =
        (Sum1 - (R - Hs) / dP) +
          ((-2 * S k / k - (a : ℝ) / dP) * (basis k x - (tauZ s k : ℝ))) := by
      simp only [Hs]
      push_cast
      field_simp
      ring
    rw [e]
    have b1 : |-2 * S k / k - (a : ℝ) / dP| ≤ 1 / dP + 2 * Em := by
      have e2 : -2 * S k / k - (a : ℝ) / dP =
          (-2 * ((m : ℝ) / Sc) / k - (a : ℝ) / dP) + (-2 / k) * (S k - (m : ℝ) / Sc) := by
        field_simp
        ring
      rw [e2]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_sub_comm]; exact ca
      · rw [abs_mul]
        have hk2 : |(-2 : ℝ) / k| ≤ 2 := by
          rw [abs_div, abs_neg, abs_two, abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
          linarith
        exact mul_le_mul hk2 h0 (abs_nonneg _) (by norm_num)
    have b2 : |(-2 * S k / k - (a : ℝ) / dP) * (basis k x - (tauZ s k : ℝ))| ≤
        (1 / dP + 2 * Em) * 2 := by
      rw [abs_mul]
      exact mul_le_mul b1 ht (abs_nonneg _) ((abs_nonneg _).trans b1)
    have := abs_add_le (Sum1 - (R - Hs) / dP)
      ((-2 * S k / k - (a : ℝ) / dP) * (basis k x - (tauZ s k : ℝ)))
    push_cast
    nlinarith

/-- An atom list with the real weights. -/
def aval (s : Bool) (L : List (ℝ × ℂ)) (t : ℝ) : ℝ := (L.map fun x => x.1 * av s x.2 t).sum

/-- Moments of an atom list. -/
def asum (L : List (ℝ × ℂ)) (n : ℕ) : ℝ := (L.map fun x => x.1 * (x.2 ^ n).re).sum

/-- Tail of an atom list. -/
def atail (L : List (ℝ × ℂ)) (N : ℕ) : ℝ :=
  (L.map fun x => |x.1| * (4 * (‖x.2‖ ^ (N + 1) * (1 - ‖x.2‖)⁻¹ / ((N : ℝ) + 1)))).sum

theorem aval_series (s : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (N : ℕ) : ∀ (L : List (ℝ × ℂ)),
    (∀ x ∈ L, ‖x.2‖ < 1) →
    |aval s L t - ∑ i ∈ Finset.range N, (-2 * asum L (1 + i) / ((1 + i : ℕ) : ℝ)) *
        (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ))| ≤ atail L N
  | [], _ => by simp [aval, asum, atail]
  | x :: M, h => by
    have ih := aval_series s ht N M fun y hy => h y (List.mem_cons_of_mem _ hy)
    have a := atom_series s (h x (by simp)) ht N
    have e : aval s (x :: M) t - ∑ i ∈ Finset.range N, (-2 * asum (x :: M) (1 + i) / ((1 + i : ℕ) : ℝ)) *
        (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ)) =
        x.1 * (av s x.2 t + 2 * ∑ n ∈ Finset.range N, (x.2 ^ (n + 1)).re *
          (basis (n + 1) (2 * t - 1) - (tauZ s (n + 1) : ℝ)) / ((n : ℝ) + 1)) +
        (aval s M t - ∑ i ∈ Finset.range N, (-2 * asum M (1 + i) / ((1 + i : ℕ) : ℝ)) *
          (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ))) := by
      simp only [aval, asum, List.map_cons, List.sum_cons]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      have : ∀ i ∈ Finset.range N, (-2 * (x.1 * (x.2 ^ (1 + i)).re +
            (M.map fun x => x.1 * (x.2 ^ (1 + i)).re).sum) / ((1 + i : ℕ) : ℝ)) *
          (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ)) =
          -(x.1 * (2 * ((x.2 ^ (i + 1)).re * (basis (i + 1) (2 * t - 1) - (tauZ s (i + 1) : ℝ)) /
            ((i : ℝ) + 1)))) +
          (-2 * (M.map fun x => x.1 * (x.2 ^ (1 + i)).re).sum / ((1 + i : ℕ) : ℝ)) *
            (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ)) := by
        intro i _
        rw [add_comm 1 i]
        push_cast
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    simp only [atail, List.map_cons, List.sum_cons]
    refine add_le_add ?_ ih
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left a (abs_nonneg _)

/-- A function within `e` of a Chebyshev list over `dP` on `(0,1]`. -/
def Close (dP : ℕ) (f : ℝ → ℝ) (c : List ℤ) (e : ℝ) : Prop :=
  ∀ t ∈ Ioc (0 : ℝ) 1, |f t - rawSum c 0 (2 * t - 1) / dP| ≤ e

theorem Close.add {dP : ℕ} {f g : ℝ → ℝ} {a b : List ℤ} {e1 e2 : ℝ} (h1 : Close dP f a e1)
    (h2 : Close dP g b e2) : Close dP (fun t => f t + g t) (addZ a b) (e1 + e2) := by
  intro t ht
  have a1 := h1 t ht
  have a2 := h2 t ht
  rw [rawSum_addZ, add_div]
  have e : f t + g t - (rawSum a 0 (2 * t - 1) / dP + rawSum b 0 (2 * t - 1) / dP) =
      (f t - rawSum a 0 (2 * t - 1) / dP) + (g t - rawSum b 0 (2 * t - 1) / dP) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add a1 a2)

/-- **A group of atoms is close to the list built from its moments.** -/
theorem group_close (s : Bool) {dP : ℕ} {Sc : ℤ} (hdP : 0 < dP) (hSc : 0 < Sc) {L : List (ℝ × ℂ)}
    (hq : ∀ x ∈ L, ‖x.2‖ < 1) {mom : List ℤ} {M : ℕ} (hlen : mom.length = M + 1) {Em : ℝ}
    (hm : ∀ n ≤ M, |asum L n - (mom.getD n 0 : ℝ) / Sc| ≤ Em) :
    Close dP (aval s L) (grpList s dP Sc mom) (atail L M + (M : ℝ) * (2 * (1 / dP + 2 * Em))) := by
  intro t ht
  have hz : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  cases mom with
  | nil => simp at hlen
  | cons m0 rest =>
    have hr : rest.length = M := by simpa using hlen
    have a := aval_series s (t := t) ⟨ht.1.le, ht.2⟩ M L hq
    have b := coef_close (dP := (dP : ℤ)) (Sc := Sc) (by exact_mod_cast hdP) hSc s hz (S := asum L)
      (Em := Em) rest 1 one_pos (fun i hi => by
        have := hm (1 + i) (by omega)
        simpa [add_comm 1 i] using this)
    rw [hr] at b
    simp only [grpList, rawSum_cons, basis_zero]
    set c := coefL (dP : ℤ) Sc 1 rest
    have e : aval s L t - (((-hsum s 1 c : ℤ) : ℝ) * 1 + rawSum c (0 + 1) (2 * t - 1)) / dP =
        (aval s L t - ∑ i ∈ Finset.range M, (-2 * asum L (1 + i) / ((1 + i : ℕ) : ℝ)) *
          (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ))) +
        (∑ i ∈ Finset.range M, (-2 * asum L (1 + i) / ((1 + i : ℕ) : ℝ)) *
          (basis (1 + i) (2 * t - 1) - (tauZ s (1 + i) : ℝ)) -
          (rawSum c 1 (2 * t - 1) - (hsum s 1 c : ℝ)) / ((dP : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add a (by simpa using b))

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

/-! ### The direct stream: the scalar chains on the moments -/

/-- `K_{n+1}` from `τ_n` (`a`) and `τ_{n+2}` (`c`). -/
def kOf (n : ℕ) (a c : ℤ) : ℤ :=
  if n = 0 then (c + a) / 4 else c / (2 * ((n : ℤ) + 2)) - a / (2 * (n : ℤ))

/-- The coefficient of `T_{n+1}`. -/
def dirC (dP Sc : ℤ) (n : ℕ) (K J : ℤ) : ℤ := (-(4 * J - K) * dP) / (((n : ℤ) + 1) * Sc)

/-- The chains: `H`, `I`, `G`, `J` at index `n`, moments from index `n`. -/
def dirLoop (dP Sc : ℤ) : ℕ → ℤ → ℤ → ℤ → ℤ → List ℤ → List ℤ
  | _, _, _, _, _, [] => []
  | n, H, I, G, J, a :: t =>
    match t with
    | [] => []
    | [_] => []
    | b :: c :: r =>
      forceI (G - J) fun J' => forceI (H - I) fun I' => forceI (kOf n a c) fun K =>
        dirC dP Sc n K J' :: dirLoop dP Sc (n + 1) (2 * K - H) I' (2 * I' - G) J' (b :: c :: r)

noncomputable section

/-- The recurrences of the exact sequences. -/
structure DirSeq (τ K H I G J : ℕ → ℝ) : Prop where
  K1 : K 1 = (τ 2 + τ 0) / 4
  K2 : ∀ n : ℕ, K (n + 2) = τ (n + 3) / (2 * ((n : ℝ) + 3)) - τ (n + 1) / (2 * ((n : ℝ) + 1))
  H1 : ∀ n, H (n + 1) = 2 * K (n + 1) - H n
  I1 : ∀ n, I (n + 1) = H n - I n
  G1 : ∀ n, G (n + 1) = 2 * I (n + 1) - G n
  J1 : ∀ n, J (n + 1) = G n - J n

theorem floor_close {X Y : ℤ} (hY : 0 < Y) : |((X / Y : ℤ) : ℝ) - (X : ℝ) / Y| ≤ 1 := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have e := Int.mul_ediv_add_emod X Y
  have m0 := Int.emod_nonneg X hY.ne'
  have m1 := Int.emod_lt_of_pos X hY
  have er : (Y : ℝ) * ((X / Y : ℤ) : ℝ) + ((X % Y : ℤ) : ℝ) = X := by exact_mod_cast e
  have m0r : (0 : ℝ) ≤ ((X % Y : ℤ) : ℝ) := by exact_mod_cast m0
  have m1r : ((X % Y : ℤ) : ℝ) ≤ Y := by exact_mod_cast m1.le
  have : ((X / Y : ℤ) : ℝ) - (X : ℝ) / Y = -(((X % Y : ℤ) : ℝ) / Y) := by
    rw [← er]
    field_simp
    ring
  rw [this, abs_neg, abs_of_nonneg (div_nonneg m0r hYr.le), div_le_one hYr]
  exact m1r

/-- `K` from two moment enclosures. -/
theorem kOf_close {τ K : ℕ → ℝ} {H I G J : ℕ → ℝ} (hd : DirSeq τ K H I G J) {Sc : ℤ} (hSc : 0 < Sc)
    {Em : ℝ} (n : ℕ) {a c : ℤ} (ha : |τ n - (a : ℝ) / Sc| ≤ Em)
    (hc : |τ (n + 2) - (c : ℝ) / Sc| ≤ Em) :
    |K (n + 1) - ((kOf n a c : ℤ) : ℝ) / Sc| ≤ Em + 2 / Sc := by
  have hSr : (0 : ℝ) < Sc := by exact_mod_cast hSc
  have hEm : 0 ≤ Em := (abs_nonneg _).trans ha
  have sc : ∀ {x y : ℝ}, |x| ≤ y → |x / Sc| ≤ y / Sc := fun {x y} h => by
    rw [abs_div, abs_of_pos hSr]
    exact div_le_div_of_nonneg_right h hSr.le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [kOf, if_true]
    have f := floor_close (X := c + a) (Y := 4) (by norm_num)
    have f' := sc f
    rw [hd.K1]
    simp only [zero_add] at hc
    push_cast at f f'
    have e : (τ 2 + τ 0) / 4 - (((c + a) / 4 : ℤ) : ℝ) / Sc =
        (τ 2 - (c : ℝ) / Sc) / 4 + (τ 0 - (a : ℝ) / Sc) / 4 -
          ((((c + a) / 4 : ℤ) : ℝ) - ((c : ℝ) + a) / 4) / Sc := by
      field_simp
      ring
    rw [e]
    have a1 := abs_le.mp ha
    have a2 := abs_le.mp hc
    have a3 := abs_le.mp f'
    rw [abs_le]
    have : (0 : ℝ) < 1 / Sc := by positivity
    have h2 : (2 : ℝ) / Sc = 1 / Sc + 1 / Sc := by ring
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hk := hd.K2 m
    simp only [kOf, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    set A : ℤ := 2 * (((m + 1 : ℕ) : ℤ) + 2) with hA
    set B : ℤ := 2 * ((m + 1 : ℕ) : ℤ) with hB
    have hA0 : 0 < A := by rw [hA]; positivity
    have hB0 : 0 < B := by rw [hB]; positivity
    have Ar : (A : ℝ) = 2 * ((m : ℝ) + 3) := by rw [hA]; push_cast; ring
    have Br : (B : ℝ) = 2 * ((m : ℝ) + 1) := by rw [hB]; push_cast; ring
    have Apos : (2 : ℝ) ≤ A := by rw [Ar]; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have Bpos : (2 : ℝ) ≤ B := by rw [Br]; nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have f1 := sc (floor_close (X := c) (Y := A) hA0)
    have f2 := sc (floor_close (X := a) (Y := B) hB0)
    have e3 : m + 1 + 2 = m + 3 := by omega
    rw [show m + 1 + 1 = m + 2 by omega, hk]
    rw [e3] at hc
    have e : τ (m + 3) / (2 * ((m : ℝ) + 3)) - τ (m + 1) / (2 * ((m : ℝ) + 1)) -
        (((c / A - a / B : ℤ)) : ℝ) / Sc =
        (τ (m + 3) - (c : ℝ) / Sc) / A - (τ (m + 1) - (a : ℝ) / Sc) / B -
          ((((c / A : ℤ) : ℝ) - (c : ℝ) / A) / Sc) + ((((a / B : ℤ) : ℝ) - (a : ℝ) / B) / Sc) := by
      rw [← Ar, ← Br]
      push_cast
      have : (A : ℝ) ≠ 0 := by linarith
      have : (B : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    have g1 : |(τ (m + 3) - (c : ℝ) / Sc) / A| ≤ Em / 2 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < A)]
      exact div_le_div₀ hEm hc (by norm_num) Apos
    have g2 : |(τ (m + 1) - (a : ℝ) / Sc) / B| ≤ Em / 2 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < B)]
      exact div_le_div₀ hEm ha (by norm_num) Bpos
    have a1 := abs_le.mp g1
    have a2 := abs_le.mp g2
    have a3 := abs_le.mp f1
    have a4 := abs_le.mp f2
    rw [abs_le]
    have h2 : (2 : ℝ) / Sc = 1 / Sc + 1 / Sc := by ring
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-- The coefficient of `T_m` of the direct stream, `m ≥ 1`. -/
def dirA (K J : ℕ → ℝ) (m : ℕ) : ℝ := -(4 * J m - K m) / m

theorem dirC_close {K J : ℕ → ℝ} {dP Sc : ℤ} (hdP : 0 < dP) (hSc : 0 < Sc) (n : ℕ) {Kh Jh : ℤ}
    {eK eJ : ℝ} (hK : |K (n + 1) - (Kh : ℝ) / Sc| ≤ eK) (hJ : |J (n + 1) - (Jh : ℝ) / Sc| ≤ eJ) :
    |dirA K J (n + 1) - ((dirC dP Sc n Kh Jh : ℤ) : ℝ) / dP| ≤ 1 / dP + (4 * eJ + eK) := by
  have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
  have hSr : (0 : ℝ) < Sc := by exact_mod_cast hSc
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hY : (0 : ℤ) < ((n : ℤ) + 1) * Sc := by positivity
  have f := floor_close (X := -(4 * Jh - Kh) * dP) hY
  have f' : |((dirC dP Sc n Kh Jh : ℤ) : ℝ) / dP - (-(4 * Jh - Kh) * dP : ℤ) / (((n : ℤ) + 1) * Sc : ℤ) / dP|
      ≤ 1 / dP := by
    rw [← sub_div, abs_div, abs_of_pos hdr]
    exact div_le_div_of_nonneg_right f hdr.le
  have e : dirA K J (n + 1) - ((dirC dP Sc n Kh Jh : ℤ) : ℝ) / dP =
      (-(4 * (J (n + 1) - (Jh : ℝ) / Sc) - (K (n + 1) - (Kh : ℝ) / Sc)) / ((n : ℝ) + 1)) -
      (((dirC dP Sc n Kh Jh : ℤ) : ℝ) / dP -
        (-(4 * Jh - Kh) * dP : ℤ) / (((n : ℤ) + 1) * Sc : ℤ) / dP) := by
    unfold dirA
    push_cast
    field_simp
    ring
  rw [e]
  have g : |-(4 * (J (n + 1) - (Jh : ℝ) / Sc) - (K (n + 1) - (Kh : ℝ) / Sc)) / ((n : ℝ) + 1)| ≤
      4 * eJ + eK := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 1), abs_neg]
    refine (div_le_self (abs_nonneg _) hn).trans ?_
    have a1 := abs_le.mp hJ
    have a2 := abs_le.mp hK
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have := abs_sub (-(4 * (J (n + 1) - (Jh : ℝ) / Sc) - (K (n + 1) - (Kh : ℝ) / Sc)) / ((n : ℝ) + 1))
    (((dirC dP Sc n Kh Jh : ℤ) : ℝ) / dP -
        (-(4 * Jh - Kh) * dP : ℤ) / (((n : ℤ) + 1) * Sc : ℤ) / dP)
  linarith

/-- Error budget of the chains. -/
structure Bud where
  h0 : ℝ
  eK : ℝ
  N : ℝ

def Bud.i1 (b : Bud) : ℝ := b.h0 + b.N * (2 * b.eK)
def Bud.g1 (b : Bud) : ℝ := 2 * (b.h0 + b.N * b.i1)
def Bud.j1 (b : Bud) : ℝ := b.h0 + b.N * b.g1
def Bud.eJ (b : Bud) : ℝ := b.h0 + b.N * b.j1

/-- **The chains stay close.** -/
theorem dirLoop_close {τ K H I G J : ℕ → ℝ} (hd : DirSeq τ K H I G J) {dP Sc : ℤ} (hdP : 0 < dP)
    (hSc : 0 < Sc) {Em : ℝ} {b : Bud} (hh0 : 0 ≤ b.h0) (hK0 : b.eK = Em + 2 / Sc)
    (hEm : 0 ≤ Em) : ∀ (l : List ℤ) (n : ℕ) (Hh Ih Gh Jh : ℤ),
    (n : ℝ) + (l.length : ℝ) - 2 ≤ b.N →
    (∀ i < l.length, |τ (n + i) - (l.getD i 0 : ℝ) / Sc| ≤ Em) →
    |H n - (Hh : ℝ) / Sc| ≤ b.h0 + n * (2 * b.eK) →
    |I n - (Ih : ℝ) / Sc| ≤ b.h0 + n * b.i1 →
    |G n - (Gh : ℝ) / Sc| ≤ b.h0 + n * b.g1 →
    |J n - (Jh : ℝ) / Sc| ≤ b.h0 + n * b.j1 →
    ∀ i < (dirLoop dP Sc n Hh Ih Gh Jh l).length,
      |dirA K J (n + i + 1) - (((dirLoop dP Sc n Hh Ih Gh Jh l).getD i 0 : ℤ) : ℝ) / dP| ≤
        1 / dP + (4 * b.eJ + b.eK)
  | [], n, _, _, _, _, _, _, _, _, _, _ => by simp [dirLoop]
  | [_], n, _, _, _, _, _, _, _, _, _, _ => by simp [dirLoop]
  | [_, _], n, _, _, _, _, _, _, _, _, _, _ => by simp [dirLoop]
  | a :: b' :: c :: r, n, Hh, Ih, Gh, Jh, hN, hl, eH, eI, eG, eJ => by
    have hSr : (0 : ℝ) < Sc := by exact_mod_cast hSc
    have heK : 0 ≤ b.eK := by rw [hK0]; positivity
    have hNr : (n : ℝ) + 1 ≤ b.N := by
      simp only [List.length_cons] at hN
      push_cast at hN
      linarith [(Nat.cast_nonneg r.length : (0 : ℝ) ≤ r.length)]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hN0 : 0 ≤ b.N := by linarith
    have i10 : 0 ≤ b.i1 := by unfold Bud.i1; positivity
    have g10 : 0 ≤ b.g1 := by unfold Bud.g1; positivity
    have j10 : 0 ≤ b.j1 := by unfold Bud.j1; positivity
    simp only [dirLoop, forceI_eq]
    set J' := Gh - Jh with hJ'
    set I' := Hh - Ih with hI'
    set Kh := kOf n a c with hKh
    -- the new errors
    have kc : |K (n + 1) - (Kh : ℝ) / Sc| ≤ b.eK := by
      have a0 := hl 0 (by simp)
      have a2 := hl 2 (by simp)
      simp only [List.getD_cons_zero, add_zero, List.getD_cons_succ] at a0 a2
      rw [hK0]
      exact kOf_close hd hSc n a0 a2
    have nJ : |J (n + 1) - (J' : ℝ) / Sc| ≤ b.h0 + ((n + 1 : ℕ) : ℝ) * b.j1 := by
      rw [hd.J1 n, hJ']
      push_cast
      have e : G n - J n - ((Gh : ℝ) - Jh) / Sc = (G n - (Gh : ℝ) / Sc) - (J n - (Jh : ℝ) / Sc) := by
        field_simp
        ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      have : b.h0 + n * b.g1 ≤ b.j1 := by
        unfold Bud.j1
        have := mul_le_mul_of_nonneg_right (by linarith : (n : ℝ) ≤ b.N) g10
        linarith
      linarith
    have nI : |I (n + 1) - (I' : ℝ) / Sc| ≤ b.h0 + ((n + 1 : ℕ) : ℝ) * b.i1 := by
      rw [hd.I1 n, hI']
      push_cast
      have e : H n - I n - ((Hh : ℝ) - Ih) / Sc = (H n - (Hh : ℝ) / Sc) - (I n - (Ih : ℝ) / Sc) := by
        field_simp
        ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      have : b.h0 + n * (2 * b.eK) ≤ b.i1 := by
        unfold Bud.i1
        have := mul_le_mul_of_nonneg_right (by linarith : (n : ℝ) ≤ b.N)
          (by positivity : 0 ≤ 2 * b.eK)
        linarith
      linarith
    have nH : |H (n + 1) - ((2 * Kh - Hh : ℤ) : ℝ) / Sc| ≤ b.h0 + ((n + 1 : ℕ) : ℝ) * (2 * b.eK) := by
      rw [hd.H1 n]
      push_cast
      have e : 2 * K (n + 1) - H n - (2 * (Kh : ℝ) - Hh) / Sc =
          2 * (K (n + 1) - (Kh : ℝ) / Sc) - (H n - (Hh : ℝ) / Sc) := by
        field_simp
        ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    have nG : |G (n + 1) - ((2 * I' - Gh : ℤ) : ℝ) / Sc| ≤ b.h0 + ((n + 1 : ℕ) : ℝ) * b.g1 := by
      rw [hd.G1 n]
      push_cast
      have e : 2 * I (n + 1) - G n - (2 * (I' : ℝ) - Gh) / Sc =
          2 * (I (n + 1) - (I' : ℝ) / Sc) - (G n - (Gh : ℝ) / Sc) := by
        rw [hI']
        field_simp
        ring
      rw [hI'] at nI ⊢
      push_cast at nI ⊢
      rw [show 2 * I (n + 1) - G n - (2 * ((Hh : ℝ) - Ih) - Gh) / Sc =
          2 * (I (n + 1) - ((Hh : ℝ) - Ih) / Sc) - (G n - (Gh : ℝ) / Sc) by field_simp; ring]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_two]
      have : b.h0 + ((n : ℝ) + 1) * b.i1 ≤ b.h0 + b.N * b.i1 := by
        have := mul_le_mul_of_nonneg_right hNr i10
        linarith
      have g1e : b.g1 = 2 * (b.h0 + b.N * b.i1) := rfl
      linarith
    intro i hi
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, add_zero]
      have hJb : |J (n + 1) - (J' : ℝ) / Sc| ≤ b.eJ := by
        refine nJ.trans ?_
        have := mul_le_mul_of_nonneg_right hNr j10
        have e : b.eJ = b.h0 + b.N * b.j1 := rfl
        push_cast
        linarith
      exact dirC_close hdP hSc n kc hJb
    | succ i =>
      simp only [List.getD_cons_succ]
      have hi' : i < (dirLoop dP Sc (n + 1) (2 * Kh - Hh) I' (2 * I' - Gh) J' (b' :: c :: r)).length := by
        simpa using hi
      have := dirLoop_close hd hdP hSc hh0 hK0 hEm (b' :: c :: r) (n + 1) (2 * Kh - Hh) I'
        (2 * I' - Gh) J' (by
          simp only [List.length_cons] at hN ⊢
          push_cast at hN ⊢
          linarith)
        (fun j hj => by
          have := hl (j + 1) (by simpa using hj)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
        nH nI nG nJ i hi'
      rw [show n + (i + 1) + 1 = n + 1 + i + 1 by omega]
      exact this

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CapFields

noncomputable section

/-- The Chebyshev variable of an abscissa. -/
def zE (y : ℝ) : ℝ := 2 * YCell.physX y - 1

theorem evE_lin (E : List (ℝ × ℝ)) (a b : ℝ) (f g : ℝ → ℝ) :
    evE E (fun y => a * f y + b * g y) = a * evE E f + b * evE E g := by
  induction E with
  | nil => simp [evE]
  | cons e t ih =>
    simp only [evE, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem evE_congr {E : List (ℝ × ℝ)} {f g : ℝ → ℝ} (h : ∀ y, f y = g y) : evE E f = evE E g := by
  have : f = g := funext h
  rw [this]

/-- The exact sequences of an atom list. -/
def sT (E : List (ℝ × ℝ)) (n : ℕ) : ℝ := evE E fun y => basis n (zE y)
def sK (E : List (ℝ × ℝ)) (n : ℕ) : ℝ := evE E fun y => kP n (zE y)
def sI (E : List (ℝ × ℝ)) (n : ℕ) : ℝ := evE E fun y => iP n (zE y)
def sH (E : List (ℝ × ℝ)) (n : ℕ) : ℝ := sI E (n + 1) + sI E n
def sJ (E : List (ℝ × ℝ)) (n : ℕ) : ℝ := evE E fun y => jP n (zE y)
def sG (E : List (ℝ × ℝ)) (n : ℕ) : ℝ := sJ E (n + 1) + sJ E n

theorem dirSeq (E : List (ℝ × ℝ)) : DirSeq (sT E) (sK E) (sH E) (sI E) (sG E) (sJ E) where
  K1 := by
    have : sK E 1 = (1 / 4) * sT E 2 + (1 / 4) * sT E 0 := by
      unfold sK sT
      rw [← evE_lin]
      refine evE_congr fun y => ?_
      have h2 := basis_add_two 0 (zE y)
      simp only [zero_add, basis_zero, basis_one'] at h2
      simp only [kP, basis_zero]
      rw [h2]
      ring
    rw [this]
    ring
  K2 n := by
    have : sK E (n + 2) = (1 / (2 * ((n : ℝ) + 3))) * sT E (n + 3) +
        (-(1 / (2 * ((n : ℝ) + 1)))) * sT E (n + 1) := by
      unfold sK sT
      rw [← evE_lin]
      refine evE_congr fun y => ?_
      simp only [kP]
      ring
    rw [this]
    ring
  H1 n := by
    have : sI E (n + 2) = 2 * sK E (n + 1) + (-2) * sI E (n + 1) + (-1) * sI E n := by
      have e : sI E (n + 2) = 1 * (evE E fun y => 2 * kP (n + 1) (zE y) + (-2) * iP (n + 1) (zE y)) +
          (-1) * sI E n := by
        unfold sI
        rw [← evE_lin]
        refine evE_congr fun y => ?_
        simp only [iP]
        ring
      rw [e, evE_lin]
      unfold sK sI
      ring
    unfold sH
    rw [show n + 1 + 1 = n + 2 from rfl, this]
    ring
  I1 n := by unfold sH; ring
  G1 n := by
    have : sJ E (n + 2) = 2 * sI E (n + 1) + (-2) * sJ E (n + 1) + (-1) * sJ E n := by
      have e : sJ E (n + 2) = 1 * (evE E fun y => 2 * iP (n + 1) (zE y) + (-2) * jP (n + 1) (zE y)) +
          (-1) * sJ E n := by
        unfold sJ
        rw [← evE_lin]
        refine evE_congr fun y => ?_
        simp only [jP]
        ring
      rw [e, evE_lin]
      unfold sI sJ
      ring
    unfold sG
    rw [show n + 1 + 1 = n + 2 from rfl, this]
    ring
  J1 n := by unfold sG; ring

theorem evS_Adir {P : List Seg} {E : List (ℝ × ℝ)} (hA : Atoms P E) (n : ℕ) :
    evS P (Adir (n + 1)) = dirA (sK E) (sJ E) (n + 1) := by
  rw [hA]
  have : evE E (Adir (n + 1)) = (4 / ((n : ℝ) + 1)) * sJ E (n + 1) +
      (-(1 / ((n : ℝ) + 1))) * sK E (n + 1) := by
    unfold sJ sK
    rw [← evE_lin]
    refine evE_congr fun y => ?_
    simp only [Adir, muP]
    unfold zE
    ring
  rw [this]
  unfold dirA
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem len_dirLoop (dP Sc : ℤ) : ∀ (l : List ℤ) (n : ℕ) (H I G J : ℤ),
    (dirLoop dP Sc n H I G J l).length = l.length - 2
  | [], _, _, _, _, _ => by simp [dirLoop]
  | [_], _, _, _, _, _ => by simp [dirLoop]
  | [_, _], _, _, _, _, _ => by simp [dirLoop]
  | a :: b :: c :: r, n, H, I, G, J => by
    simp only [dirLoop, forceI_eq, List.length_cons]
    rw [len_dirLoop dP Sc (b :: c :: r)]
    simp

theorem rawSum_close {dP : ℤ} (hdP : 0 < dP) {A : ℕ → ℝ} {e : ℝ} {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : ∀ (l : List ℤ) (k : ℕ),
    (∀ i < l.length, |A (k + i) - (l.getD i 0 : ℝ) / dP| ≤ e) →
    |∑ i ∈ Finset.range l.length, A (k + i) * basis (k + i) x - rawSum l k x / dP| ≤
      (l.length : ℝ) * e
  | [], _, _ => by simp
  | c :: t, k, h => by
    have ih := rawSum_close hdP hx t (k + 1) fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, add_zero] at h0
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [rawSum_cons, add_zero]
    have hb := abs_basis_le_one k hx
    have ee : ∑ i ∈ Finset.range t.length, A (k + (i + 1)) * basis (k + (i + 1)) x +
        A k * basis k x - ((c : ℝ) * basis k x + rawSum t (k + 1) x) / dP =
        (∑ i ∈ Finset.range t.length, A (k + 1 + i) * basis (k + 1 + i) x -
          rawSum t (k + 1) x / dP) + (A k - (c : ℝ) / dP) * basis k x := by
      have hh : ∑ i ∈ Finset.range t.length, A (k + (i + 1)) * basis (k + (i + 1)) x =
          ∑ i ∈ Finset.range t.length, A (k + 1 + i) * basis (k + 1 + i) x :=
        Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by omega]
      rw [hh]
      ring
    rw [ee]
    refine (abs_add_le _ _).trans ?_
    have g : |(A k - (c : ℝ) / dP) * basis k x| ≤ e := by
      rw [abs_mul]
      calc _ ≤ e * 1 := mul_le_mul h0 hb (abs_nonneg _) ((abs_nonneg _).trans h0)
        _ = e := mul_one e
    push_cast
    linarith

/-- **The direct stream.** -/
theorem dir_close {N : ℕ} (hN : 1 ≤ N) {P : List Seg} {E : List (ℝ × ℝ)} (hA : Atoms P E)
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E, 2 ≤ e.1) {dP : ℕ} {Sc : ℤ}
    (hdP : 0 < dP) (hSc : 0 < Sc) {mom : List ℤ} (hlen : mom.length = N + 2) {Em : ℝ} (hEm : 0 ≤ Em)
    (hm : ∀ n ≤ N + 1, |sT E n - (mom.getD n 0 : ℝ) / Sc| ≤ Em)
    {h0 : ℝ} (hh0 : 0 ≤ h0) {Hh Ih Gh Jh : ℤ}
    (e1 : |sH E 0 - (Hh : ℝ) / Sc| ≤ h0) (e2 : |sI E 0 - (Ih : ℝ) / Sc| ≤ h0)
    (e3 : |sG E 0 - (Gh : ℝ) / Sc| ≤ h0) (e4 : |sJ E 0 - (Jh : ℝ) / Sc| ≤ h0)
    {c0 : ℤ} {δ0 Mx : ℝ} (hc0 : |evS P (Adir 0) - (c0 : ℝ) / dP| ≤ δ0)
    (hV : ∀ t ∈ Ioc (0 : ℝ) 1, dirV N P E t ≤ Mx) :
    Close dP (fun t => pint P fun y => Real.log |t - YCell.physX y|)
      (c0 :: dirLoop (dP : ℤ) Sc 0 Hh Ih Gh Jh mom)
      (2 / N * Mx + δ0 + (N : ℝ) * (1 / dP + (4 * (Bud.eJ ⟨h0, Em + 2 / Sc, N⟩) + (Em + 2 / Sc)))) := by
  intro t ht
  have hz : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdZ : (0 : ℤ) < (dP : ℤ) := by exact_mod_cast hdP
  have s := dir_stream hN hA hP hE ht.1 ht.2
  set b : Bud := ⟨h0, Em + 2 / Sc, N⟩ with hb
  have L := dirLoop_close (dirSeq E) hdZ hSc (b := b) hh0 rfl hEm mom 0 Hh Ih Gh Jh
    (by rw [hlen]; simp [hb]) (fun i hi => by
      have := hm i (by omega)
      simpa using this)
    (by simpa using e1) (by simpa using e2) (by simpa using e3) (by simpa using e4)
  set cs := dirLoop (dP : ℤ) Sc 0 Hh Ih Gh Jh mom with hcs
  have hl : cs.length = N := by rw [hcs, len_dirLoop, hlen]; simp
  have R := rawSum_close hdZ hz (A := fun k => evS P (Adir k))
    (e := 1 / dP + (4 * b.eJ + b.eK)) cs 1 (fun i hi => by
      have := L i hi
      rw [show 1 + i = i + 1 by omega, evS_Adir hA]
      simpa [Nat.add_comm] using this)
  rw [hl] at R
  rw [Finset.sum_range_succ'] at s
  simp only [rawSum_cons, basis_zero, mul_one]
  have hs : ∑ k ∈ Finset.range N, evS P (Adir (k + 1)) * basis (k + 1) (2 * t - 1) =
      ∑ i ∈ Finset.range N, evS P (Adir (1 + i)) * basis (1 + i) (2 * t - 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm i 1]
  rw [hs] at s
  set S := ∑ i ∈ Finset.range N, evS P (Adir (1 + i)) * basis (1 + i) (2 * t - 1)
  set p := pint P fun y => Real.log |t - YCell.physX y|
  have ee : p - ((c0 : ℝ) * 1 + rawSum cs (0 + 1) (2 * t - 1)) / dP =
      (p - (S + evS P (Adir 0) * 1)) + (evS P (Adir 0) - (c0 : ℝ) / dP) +
        (S - rawSum cs 1 (2 * t - 1) / ((dP : ℤ) : ℝ)) := by
    push_cast
    ring
  have hVt := hV t ht
  have : 2 / (N : ℝ) * dirV N P E t ≤ 2 / N * Mx :=
    mul_le_mul_of_nonneg_left hVt (by positivity)
  simp only [mul_one] at ee
  simp only [basis_zero, mul_one] at s
  rw [ee]
  have a1 := abs_add_le ((p - (S + evS P (Adir 0))) + (evS P (Adir 0) - (c0 : ℝ) / dP))
    (S - rawSum cs 1 (2 * t - 1) / ((dP : ℤ) : ℝ))
  have a2 := abs_add_le (p - (S + evS P (Adir 0))) (evS P (Adir 0) - (c0 : ℝ) / dP)
  have hb' : b.eK = Em + 2 / Sc := rfl
  rw [← hb']
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CapFields

/-! ### Pieces to atoms -/

/-- An atom: weight, real and imaginary part of `q`. -/
abbrev QA := ℚ × ℚ × ℚ

/-- A chain segment: keys and density. -/
abbrev GS := ℤ × ℤ × ℚ

/-- The mass of a chain segment. -/
def gW (g : GS) : ℚ := g.2.2 * ((g.2.1 - g.1 : ℤ) : ℚ) / 10 ^ 12

/-- The real `r` of a real `q`. -/
def rQ (q : ℚ) : ℚ := 4 * q / (1 + q) ^ 2

def reflOK (g : GS) (q : ℚ) : Bool :=
  decide (2000000000000 ≤ g.1) && decide (g.1 < g.2.1) && decide (0 ≤ g.2.2) &&
  decide (0 < rQ q) && decide (rQ q < 1) &&
  decide (((g.1 + g.2.1 : ℤ) : ℚ) / (2 * 10 ^ 12) ≤ rQ q + 1 / rQ q)

def reflB : List GS → List ℚ → Bool
  | [], [] => true
  | g :: G, q :: qs => reflOK g q && reflB G qs
  | _, _ => false

def reflL (c : ℚ) : List GS → List ℚ → List QA
  | g :: G, q :: qs => (c * gW g, q, 0) :: reflL c G qs
  | _, _ => []

def oppOK (g : GS) (q : ℚ × ℚ) : Bool :=
  decide (2000000000000 ≤ g.1) && decide (g.1 < g.2.1) && decide (0 ≤ g.2.2) &&
  decide (rQ q.1 ≤ 0) && decide (rQ q.2 ≤ 0) &&
  decide (((g.1 + g.2.1 : ℤ) : ℚ) / (2 * 10 ^ 12) ≤ -rQ q.1 + -rQ q.2) &&
  decide (1 ≤ rQ q.1 * rQ q.2)

def oppB : List GS → List (ℚ × ℚ) → Bool
  | [], [] => true
  | g :: G, q :: qs => oppOK g q && oppB G qs
  | _, _ => false

def oppL : List GS → List (ℚ × ℚ) → List QA
  | g :: G, q :: qs => (gW g, q.1, 0) :: (gW g, q.2, 0) :: oppL G qs
  | _, _ => []

/-- The real and imaginary part of `r` of a complex `q`, and its squared modulus. -/
def rRe (q : ℚ × ℚ) : ℚ :=
  4 * (q.1 * ((1 + q.1) ^ 2 - q.2 ^ 2) + q.2 * (2 * (1 + q.1) * q.2)) / ((1 + q.1) ^ 2 + q.2 ^ 2) ^ 2

def rIm (q : ℚ × ℚ) : ℚ :=
  4 * (q.2 * ((1 + q.1) ^ 2 - q.2 ^ 2) - q.1 * (2 * (1 + q.1) * q.2)) / ((1 + q.1) ^ 2 + q.2 ^ 2) ^ 2

def nodeOK (k : ℤ) (q : ℚ × ℚ) : Bool :=
  decide (q.1 ^ 2 + q.2 ^ 2 < 1) && decide (-1000000000000 < k) && decide (k < 1000000000000) &&
  decide ((k : ℚ) / 10 ^ 12 ≤ rRe q) && decide (rRe q ^ 2 + rIm q ^ 2 ≤ 1)

def colB : List GS → List (ℚ × ℚ) → Bool
  | [], [_] => true
  | g :: G, q :: q' :: qs =>
    decide (g.1 < g.2.1) && decide (0 ≤ g.2.2) && nodeOK g.1 q && nodeOK g.2.1 q' &&
      colB G (q' :: qs)
  | _, _ => false

def colL (acc : ℚ) : List GS → List (ℚ × ℚ) → List QA
  | [], [q] => [(-2 * acc, q.1, q.2)]
  | g :: G, q :: q' :: qs =>
    (-2 * (acc + gW g / 2), q.1, q.2) :: colL (gW g / 2) G (q' :: qs)
  | _, _ => []

noncomputable section

def qOf (a : ℚ × ℚ) : ℂ := ⟨(a.1 : ℝ), (a.2 : ℝ)⟩

def aR (a : QA) : ℝ × ℂ := ((a.1 : ℝ), qOf a.2)

/-- The value of an atom list. -/
def avQ (s : Bool) (L : List QA) (t : ℝ) : ℝ := aval s (L.map aR) t

theorem avQ_nil (s : Bool) (t : ℝ) : avQ s [] t = 0 := by simp [avQ, aval]

theorem avQ_cons (s : Bool) (a : QA) (L : List QA) (t : ℝ) :
    avQ s (a :: L) t = (a.1 : ℝ) * av s (qOf a.2) t + avQ s L t := by
  simp [avQ, aval, aR]

theorem avQ_append (s : Bool) (A B : List QA) (t : ℝ) :
    avQ s (A ++ B) t = avQ s A t + avQ s B t := by
  simp [avQ, aval]

theorem qOf_real (q : ℚ) : qOf (q, 0) = (((q : ℚ) : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [qOf]

theorem pint_cons (g : Seg) (P : List Seg) (f : ℝ → ℝ) :
    pint (g :: P) f = g.rho * (∫ y in g.lo..g.hi, f y) + pint P f := by
  simp [pint]

theorem pint_nil (f : ℝ → ℝ) : pint [] f = 0 := by simp [pint]

theorem gW_real (g : GS) : ((gW g : ℚ) : ℝ) = (segR g).rho * ((segR g).hi - (segR g).lo) := by
  simp only [gW, segR]
  push_cast
  ring

theorem rQ_real (q : ℚ) : ((rQ q : ℚ) : ℝ) = 4 * (q : ℝ) / (1 + (q : ℝ)) ^ 2 := by
  simp only [rQ]
  push_cast
  ring

theorem refl_bound (c : ℚ) (hc : 0 ≤ c) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∀ (G : List GS) (qs : List ℚ), reflB G qs = true →
      (c : ℝ) * pint (G.map segR) (fun y => Real.log |1 - YCell.physX y * t|) ≤
        avQ false (reflL c G qs) t
  | [], [], _ => by simp [pint_nil, reflL, avQ_nil]
  | [], _ :: _, h => by simp [reflB] at h
  | _ :: _, [], h => by simp [reflB] at h
  | g :: G, q :: qs, h => by
    simp only [reflB, reflOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h2, hlt⟩, hρ⟩, r0⟩, r1⟩, hm⟩, hr⟩ := h
    have ih := refl_bound c hc h0 h1 G qs hr
    have r0' : (0 : ℝ) < ((rQ q : ℚ) : ℝ) := by exact_mod_cast r0
    have r1' : ((rQ q : ℚ) : ℝ) < 1 := by exact_mod_cast r1
    have hlo : (2 : ℝ) ≤ (segR g).lo := by
      have : ((2000000000000 : ℤ) : ℝ) ≤ g.1 := by exact_mod_cast h2
      simp only [segR]
      rw [le_div_iff₀ (by positivity)]
      norm_num at this ⊢
      linarith
    have hl : (segR g).lo < (segR g).hi := by
      have : (g.1 : ℝ) < g.2.1 := by exact_mod_cast hlt
      simp only [segR]
      gcongr
    have hmid : ((segR g).lo + (segR g).hi) / 2 ≤ ((rQ q : ℚ) : ℝ) + 1 / ((rQ q : ℚ) : ℝ) := by
      have : ((((g.1 + g.2.1 : ℤ) : ℚ) / (2 * 10 ^ 12) : ℚ) : ℝ) ≤
          ((rQ q + 1 / rQ q : ℚ) : ℝ) := by exact_mod_cast hm
      push_cast at this
      simp only [segR]
      refine le_of_eq_of_le ?_ this
      ring
    have p := refl_piece hlo hl h0 h1 (rQ_real q) r0' r1' hmid
    have hρ' : (0 : ℝ) ≤ (segR g).rho := by simp only [segR]; exact_mod_cast hρ
    have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    rw [List.map_cons, pint_cons]
    simp only [reflL]
    rw [avQ_cons]
    have e : ((c * gW g : ℚ) : ℝ) * av false (qOf (q, 0)) t =
        (c : ℝ) * ((segR g).rho * (((segR g).hi - (segR g).lo) * KQ ((q : ℝ) : ℂ) t)) := by
      rw [Rat.cast_mul, gW_real, qOf_real]
      simp only [av, Bool.false_eq_true, ite_false]
      ring
    simp only [] at e ⊢
    rw [e, mul_add]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p hρ') hc'
    linarith

theorem opp_bound {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∀ (G : List GS) (qs : List (ℚ × ℚ)), oppB G qs = true →
      pint (G.map segR) (fun y => Real.log (1 + y * t + t ^ 2)) ≤ avQ false (oppL G qs) t
  | [], [], _ => by simp [pint_nil, oppL, avQ_nil]
  | [], _ :: _, h => by simp [oppB] at h
  | _ :: _, [], h => by simp [oppB] at h
  | g :: G, q :: qs, h => by
    simp only [oppB, oppOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h2, hlt⟩, hρ⟩, n1⟩, n2⟩, hm⟩, hp⟩, hr⟩ := h
    have ih := opp_bound h0 h1 G qs hr
    have n1' : ((rQ q.1 : ℚ) : ℝ) ≤ 0 := by exact_mod_cast n1
    have n2' : ((rQ q.2 : ℚ) : ℝ) ≤ 0 := by exact_mod_cast n2
    have hp' : (1 : ℝ) ≤ ((rQ q.1 : ℚ) : ℝ) * ((rQ q.2 : ℚ) : ℝ) := by exact_mod_cast hp
    have hlo : (2 : ℝ) ≤ (segR g).lo := by
      have : ((2000000000000 : ℤ) : ℝ) ≤ g.1 := by exact_mod_cast h2
      simp only [segR]
      rw [le_div_iff₀ (by positivity)]
      norm_num at this ⊢
      linarith
    have hl : (segR g).lo < (segR g).hi := by
      have : (g.1 : ℝ) < g.2.1 := by exact_mod_cast hlt
      simp only [segR]
      gcongr
    have hmid : ((segR g).lo + (segR g).hi) / 2 ≤ -((rQ q.1 : ℚ) : ℝ) + -((rQ q.2 : ℚ) : ℝ) := by
      have : ((((g.1 + g.2.1 : ℤ) : ℚ) / (2 * 10 ^ 12) : ℚ) : ℝ) ≤
          ((-rQ q.1 + -rQ q.2 : ℚ) : ℝ) := by exact_mod_cast hm
      push_cast at this
      simp only [segR]
      refine le_of_eq_of_le ?_ this
      ring
    have p := opp_piece hlo hl h0 h1 (rQ_real q.1) (rQ_real q.2) n1' n2' hmid hp'
    have hρ' : (0 : ℝ) ≤ (segR g).rho := by simp only [segR]; exact_mod_cast hρ
    rw [List.map_cons, pint_cons]
    simp only [oppL]
    rw [avQ_cons, avQ_cons]
    simp only [av, Bool.false_eq_true, ite_false]
    rw [qOf_real, qOf_real, gW_real]
    have := mul_le_mul_of_nonneg_left p hρ'
    nlinarith [this, ih]

theorem one_add_ne_q {q : ℚ × ℚ} (h : q.1 ^ 2 + q.2 ^ 2 < 1) :
    ((1 + (q.1 : ℝ)) ^ 2 + (q.2 : ℝ) ^ 2) ≠ 0 := by
  have h' : ((q.1 : ℝ)) ^ 2 + (q.2 : ℝ) ^ 2 < 1 := by exact_mod_cast h
  have : 0 < (1 + (q.1 : ℝ)) ^ 2 + (q.2 : ℝ) ^ 2 := by
    by_contra hc
    have a := sq_nonneg (1 + (q.1 : ℝ))
    have b := sq_nonneg (q.2 : ℝ)
    have e1 : (1 + (q.1 : ℝ)) ^ 2 = 0 := by linarith
    have e2 : (q.2 : ℝ) ^ 2 = 0 := by linarith
    have e3 : (q.1 : ℝ) = -1 := by nlinarith [pow_eq_zero_iff (two_ne_zero) |>.1 e1]
    rw [e3] at h'
    nlinarith
  exact this.ne'

theorem norm_qOf_sq (q : ℚ × ℚ) : ‖qOf q‖ ^ 2 = (q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [qOf]
  ring

theorem norm_qOf_lt {q : ℚ × ℚ} (h : q.1 ^ 2 + q.2 ^ 2 < 1) : ‖qOf q‖ < 1 := by
  have h' : ((q.1 : ℝ)) ^ 2 + (q.2 : ℝ) ^ 2 < 1 := by exact_mod_cast h
  have := norm_qOf_sq q
  have hn := norm_nonneg (qOf q)
  nlinarith

theorem rq_eq {q : ℚ × ℚ} (h : q.1 ^ 2 + q.2 ^ 2 < 1) :
    rq (qOf q) = ⟨((rRe q : ℚ) : ℝ), ((rIm q : ℚ) : ℝ)⟩ := by
  have hN := one_add_ne_q h
  have h1 : (1 + qOf q) ≠ 0 := one_add_ne_of_norm_lt (norm_qOf_lt h)
  unfold rq
  rw [div_eq_iff (pow_ne_zero 2 h1)]
  apply Complex.ext
  · simp only [qOf, rRe, rIm, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    field_simp
    ring
  · simp only [qOf, rRe, rIm, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    field_simp
    ring

theorem node_atom {k : ℤ} {q : ℚ × ℚ} (h : nodeOK k q = true) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    -colK t ((k : ℝ) / 10 ^ 12) ≤ -(2 * KQ (qOf q) t) := by
  simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hq, ka⟩, kb⟩, hre⟩, hn⟩ := h
  have ka' : (-1000000000000 : ℝ) < k := by exact_mod_cast ka
  have kb' : (k : ℝ) < 1000000000000 := by exact_mod_cast kb
  have hre' : (k : ℝ) / 10 ^ 12 ≤ ((rRe q : ℚ) : ℝ) := by exact_mod_cast hre
  have hn' : ((rRe q : ℚ) : ℝ) ^ 2 + ((rIm q : ℚ) : ℝ) ^ 2 ≤ 1 := by exact_mod_cast hn
  refine col_atom (norm_qOf_lt hq) h0 h1 ?_ ?_ ?_ ?_
  · rw [div_lt_one (by positivity)]
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    linarith
  · rw [rq_eq hq]
    exact hre'
  · rw [rq_eq hq]
    have : ‖(⟨((rRe q : ℚ) : ℝ), ((rIm q : ℚ) : ℝ)⟩ : ℂ)‖ ^ 2 ≤ 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only
      nlinarith
    have hn0 := norm_nonneg (⟨((rRe q : ℚ) : ℝ), ((rIm q : ℚ) : ℝ)⟩ : ℂ)
    nlinarith

theorem col_bound {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∀ (G : List GS) (q : ℚ × ℚ) (qs : List (ℚ × ℚ)) (acc : ℚ), colB G (q :: qs) = true →
      -pint (G.map segR) (colK t) + -2 * (acc : ℝ) * KQ (qOf q) t ≤
        avQ false (colL acc G (q :: qs)) t
  | [], q, [], acc, _ => by
    simp only [List.map_nil, pint_nil, colL]
    rw [avQ_cons, avQ_nil]
    simp only [av, Bool.false_eq_true, ite_false]
    push_cast
    linarith
  | [], _, _ :: _, _, h => by simp [colB] at h
  | _ :: _, _, [], _, h => by simp [colB] at h
  | g :: G, q, q' :: qs, acc, h => by
    simp only [colB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hlt, hρ⟩, n1⟩, n2⟩, hr⟩ := h
    have ih := col_bound h0 h1 G q' qs (gW g / 2) hr
    have a1 := node_atom n1 h0 h1
    have a2 := node_atom n2 h0 h1
    have hρ' : (0 : ℝ) ≤ (segR g).rho := by simp only [segR]; exact_mod_cast hρ
    have hl : (segR g).lo < (segR g).hi := by
      have : (g.1 : ℝ) < g.2.1 := by exact_mod_cast hlt
      simp only [segR]
      gcongr
    have bd : ∀ {k : ℤ} {q : ℚ × ℚ}, nodeOK k q = true →
        -1 < (k : ℝ) / 10 ^ 12 ∧ (k : ℝ) / 10 ^ 12 < 1 := by
      intro k q h
      simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at h
      have ka' : (-1000000000000 : ℝ) < k := by exact_mod_cast h.1.1.1.2
      have kb' : (k : ℝ) < 1000000000000 := by exact_mod_cast h.1.1.2
      constructor
      · rw [lt_div_iff₀ (by positivity)]
        linarith
      · rw [div_lt_one (by positivity)]
        linarith
    have p := col_panel hl (bd n1).1 (bd n2).2 h0
    simp only [segR] at p hρ' hl
    rw [List.map_cons, pint_cons]
    simp only [colL]
    rw [avQ_cons]
    simp only [av, Bool.false_eq_true, ite_false]
    have hg := gW_real g
    simp only [segR] at hg
    simp only [segR]
    set w : ℝ := ((gW g : ℚ) : ℝ) with hw
    set I := ∫ y in (g.1 : ℝ) / 10 ^ 12..(g.2.1 : ℝ) / 10 ^ 12, colK t y
    set ρ : ℝ := ((g.2.2 : ℚ) : ℝ)
    set A := KQ (qOf q) t
    set B := KQ (qOf q') t
    set ca := colK t ((g.1 : ℝ) / 10 ^ 12)
    set cb := colK t ((g.2.1 : ℝ) / 10 ^ 12)
    have p' : ρ * (-I) ≤ ρ * (((g.2.1 : ℝ) / 10 ^ 12 - (g.1 : ℝ) / 10 ^ 12) * (-(ca + cb) / 2)) :=
      mul_le_mul_of_nonneg_left p hρ'
    have q1 : ρ * (((g.2.1 : ℝ) / 10 ^ 12 - (g.1 : ℝ) / 10 ^ 12) * (-(ca + cb) / 2)) =
        w / 2 * (-ca + -cb) := by
      rw [hg]
      ring
    have w0 : 0 ≤ w / 2 := by
      rw [hg]
      have := sub_pos.2 hl
      positivity
    have q2 : w / 2 * (-ca + -cb) ≤ w / 2 * (-(2 * A) + -(2 * B)) :=
      mul_le_mul_of_nonneg_left (add_le_add a1 a2) w0
    push_cast at ih ⊢
    rw [← hw] at ih ⊢
    nlinarith [p', q1, q2, ih]

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CapFields

/-! ### Entries: rational data against the moment engine -/

/-- A weight and a complex atom against an entry. -/
def qClose (D Dz : ℤ) (ε δ : ℚ) (a : QA) (e : Ent) : Bool :=
  decide (a.2.1 ^ 2 + a.2.2 ^ 2 < 1) && decide (|a.2.1 - (e.2.1 : ℚ) / D| ≤ ε / 2) &&
  decide (|a.2.2 - (e.2.2 : ℚ) / D| ≤ ε / 2) && decide (|a.1 - (e.1 : ℚ) / Dz| ≤ δ)

def entB (D Dz : ℤ) (ε δ : ℚ) : List QA → List Ent → Bool
  | [], [] => true
  | a :: A, e :: E => qClose D Dz ε δ a e && entB D Dz ε δ A E
  | _, _ => false

noncomputable section

theorem len_unpk (B : ℤ) : ∀ (n : ℕ) (X : ℤ), (unpk B n X).length = n
  | 0, _ => rfl
  | n + 1, X => by simp [unpk, forceI_eq, len_unpk B n]

theorem len_moments (p : EPar) (E : List Ent) : (moments p E).length = p.I * p.bs :=
  len_unpk _ _ _

/-- The sum of the weight and table errors. -/
theorem spec_sum_le {p : EPar} {ε : ℝ} {Dw δ : ℝ} (hDw : 0 < Dw) (hη : 0 ≤ etaOf p ε) :
    ∀ L : List Spec, (∀ x ∈ L, |x.1 - (x.2.2.1 : ℝ) / Dw| ≤ δ) →
      (L.map fun x => |x.1 - (x.2.2.1 : ℝ) / Dw| + |(x.2.2.1 : ℝ)| / Dw * etaOf p ε).sum ≤
        (L.length : ℝ) * δ + (((L.map fun x => |x.2.2.1|).sum : ℤ) : ℝ) / Dw * etaOf p ε
  | [], _ => by simp
  | x :: t, h => by
    have ih := spec_sum_le hDw hη t fun y hy => h y (List.mem_cons_of_mem _ hy)
    have h0 := h x List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Int.cast_add, Int.cast_abs, Nat.cast_add, Nat.cast_one]
    set S : ℝ := (((t.map fun x => |x.2.2.1|).sum : ℤ) : ℝ)
    have e : (|(x.2.2.1 : ℝ)| + S) / Dw * etaOf p ε =
        |(x.2.2.1 : ℝ)| / Dw * etaOf p ε + S / Dw * etaOf p ε := by
      ring
    rw [e]
    linarith

/-- **Moments of a spec list, in budget form.** -/
theorem spec_close {p : EPar} (h : p.OK) {L : List Spec} {ε δ : ℝ} {Dz : ℤ} (hDz : 0 < Dz)
    (hu : ∀ x ∈ L, ‖x.2.1‖ ≤ 1)
    (hε : ∀ x ∈ L, ‖x.2.1 - toC p.D (x.2.2.2.1, x.2.2.2.2)‖ ≤ ε)
    (hw : ∀ x ∈ L, |x.1 - (x.2.2.1 : ℝ) / Dz| ≤ δ)
    (hb : (p.bs : ℝ) * (2 * ε + 2 / p.D) ≤ 1)
    (hI : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * ε + 2 / p.D)) + 2 / p.D) ≤ 1)
    (hη : etaOf p ε ≤ 1) (hη0 : 0 ≤ etaOf p ε)
    (hg : ((L.map fun x => |x.2.2.1|).sum) * (2 * p.D ^ 2) < p.B / 2) {n : ℕ}
    (hn : n < p.I * p.bs) :
    |(L.map fun x => x.1 * (x.2.1 ^ n).re).sum -
        ((moments p (L.map fun x => x.2.2)).getD n 0 : ℝ) / ((Dz * p.D ^ 2 : ℤ) : ℝ)| ≤
      (L.length : ℝ) * δ + (((L.map fun x => |x.2.2.1|).sum : ℤ) : ℝ) / Dz * etaOf p ε := by
  have hDr : (0 : ℝ) < Dz := by exact_mod_cast hDz
  have a := moment_close h hDr hu hε hb hI hη hg hn
  have b := spec_sum_le hDr hη0 L hw
  push_cast at a b ⊢
  exact a.trans b

/-- The spec list of atoms and entries. -/
def specA : List QA → List Ent → List Spec
  | a :: A, e :: E => ((a.1 : ℝ), qOf a.2, e) :: specA A E
  | _, _ => []

theorem specA_ents : ∀ {A : List QA} {E : List Ent} {D Dz : ℤ} {ε δ : ℚ},
    entB D Dz ε δ A E = true → (specA A E).map (fun x => x.2.2) = E
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h => by simp [entB] at h
  | _ :: _, [], _, _, _, _, h => by simp [entB] at h
  | a :: A, e :: E, D, Dz, ε, δ, h => by
    simp only [entB, Bool.and_eq_true] at h
    simp only [specA, List.map_cons]
    rw [specA_ents h.2]

theorem specA_len : ∀ {A : List QA} {E : List Ent} {D Dz : ℤ} {ε δ : ℚ},
    entB D Dz ε δ A E = true → (specA A E).length = A.length
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h => by simp [entB] at h
  | _ :: _, [], _, _, _, _, h => by simp [entB] at h
  | a :: A, e :: E, D, Dz, ε, δ, h => by
    simp only [entB, Bool.and_eq_true] at h
    simp only [specA, List.length_cons]
    rw [specA_len h.2]

theorem specA_asum : ∀ {A : List QA} {E : List Ent} {D Dz : ℤ} {ε δ : ℚ},
    entB D Dz ε δ A E = true → ∀ n : ℕ,
    ((specA A E).map fun x => x.1 * (x.2.1 ^ n).re).sum = asum (A.map aR) n
  | [], [], _, _, _, _, _, n => by simp [specA, asum]
  | [], _ :: _, _, _, _, _, h, _ => by simp [entB] at h
  | _ :: _, [], _, _, _, _, h, _ => by simp [entB] at h
  | a :: A, e :: E, D, Dz, ε, δ, h, n => by
    simp only [entB, Bool.and_eq_true] at h
    have ih := specA_asum h.2 n
    simp only [specA, List.map_cons, List.sum_cons, ih]
    simp [asum, aR]

theorem specA_ok : ∀ {A : List QA} {E : List Ent} {D Dz : ℤ} {ε δ : ℚ},
    0 < Dz → 0 < D → entB D Dz ε δ A E = true → ∀ x ∈ specA A E,
      ‖x.2.1‖ < 1 ∧ ‖x.2.1 - toC D (x.2.2.2.1, x.2.2.2.2)‖ ≤ (ε : ℝ) ∧
        |x.1 - (x.2.2.1 : ℝ) / Dz| ≤ (δ : ℝ)
  | [], [], _, _, _, _, _, _, _, x, hx => by simp [specA] at hx
  | [], _ :: _, _, _, _, _, _, _, h, _, _ => by simp [entB] at h
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => by simp [entB] at h
  | a :: A, e :: E, D, Dz, ε, δ, h0, h1, h, x, hx => by
    simp only [entB, qClose, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hq, ha⟩, hb⟩, hw⟩, hr⟩ := h
    simp only [specA, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have ha' : |(a.2.1 : ℝ) - (e.2.1 : ℝ) / D| ≤ (ε : ℝ) / 2 := by exact_mod_cast ha
      have hb' : |(a.2.2 : ℝ) - (e.2.2 : ℝ) / D| ≤ (ε : ℝ) / 2 := by exact_mod_cast hb
      have hw' : |(a.1 : ℝ) - (e.1 : ℝ) / Dz| ≤ (δ : ℝ) := by exact_mod_cast hw
      refine ⟨norm_qOf_lt hq, ?_, hw'⟩
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [qOf, toC, Complex.sub_re, Complex.sub_im]
      linarith
    · exact specA_ok h0 h1 hr x hx

theorem entB_q : ∀ {A : List QA} {E : List Ent} {D Dz : ℤ} {ε δ : ℚ},
    entB D Dz ε δ A E = true → ∀ a ∈ A, a.2.1 ^ 2 + a.2.2 ^ 2 < 1
  | [], [], _, _, _, _, _, a, ha => by simp at ha
  | [], _ :: _, _, _, _, _, h, _, _ => by simp [entB] at h
  | _ :: _, [], _, _, _, _, h, _, _ => by simp [entB] at h
  | a :: A, e :: E, D, Dz, ε, δ, h, b, hb => by
    simp only [entB, qClose, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1.1.1.1
    · exact entB_q h.2 b hb

/-- **A group of atoms from its entries.** -/
theorem group_ok (s : Bool) {p : EPar} (h : p.OK) {dP : ℕ} (hdP : 0 < dP) {Dz : ℤ} (hDz : 0 < Dz)
    {ε δ : ℚ} {A : List QA} {E : List Ent} (hc : entB p.D Dz ε δ A E = true)
    (hb : (p.bs : ℝ) * (2 * (ε : ℝ) + 2 / p.D) ≤ 1)
    (hI : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * (ε : ℝ) + 2 / p.D)) + 2 / p.D) ≤ 1)
    (hη : etaOf p ε ≤ 1) (hη0 : 0 ≤ etaOf p ε)
    (hg : ((E.map fun e => |e.1|).sum) * (2 * p.D ^ 2) < p.B / 2)
    {M : ℕ} (hM : M + 1 = p.I * p.bs) :
    Close dP (avQ s A) (grpList s dP (Dz * p.D ^ 2) (moments p E))
      (atail (A.map aR) M + (M : ℝ) * (2 * (1 / dP + 2 * ((A.length : ℝ) * δ +
        (((E.map fun e => |e.1|).sum : ℤ) : ℝ) / Dz * etaOf p ε)))) := by
  have hk := specA_ents hc
  have hok := specA_ok hDz h.D_pos hc
  have hS : 0 < Dz * p.D ^ 2 := by have := h.D_pos; positivity
  have hsum : ((specA A E).map fun x => |x.2.2.1|).sum = (E.map fun e => |e.1|).sum := by
    conv_rhs => rw [← hk]
    rw [List.map_map]
    rfl
  refine group_close s hdP hS (fun x hx => ?_) ?_ fun n hn => ?_
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact norm_qOf_lt (entB_q hc a ha)
  · rw [len_moments]
    exact hM.symm
  · have c := spec_close h (L := specA A E) (ε := ε) (δ := δ) hDz (fun x hx => (hok x hx).1.le)
      (fun x hx => (hok x hx).2.1) (fun x hx => (hok x hx).2.2) hb hI hη hη0
      (by rw [hsum]; exact hg) (n := n) (by omega)
    rw [specA_asum hc, hk, specA_len hc, hsum] at c
    exact c

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CapFields

/-! ### The direct atoms against the moment engine -/

/-- Lower and upper rational enclosure of `physX` at a key. -/
def xLo (kP A : ℕ) : ℚ := ((pxLo kP A).1 : ℚ) / (pxLo kP A).2
def xHi (kP A : ℕ) : ℚ := ((pxHi kP A).1 : ℚ) / (pxHi kP A).2

/-- A direct atom against its entry. -/
def oClose (kP : ℕ) (D Dz : ℤ) (ε1 ε2 δ : ℚ) (a : Ev) (e : Ent) : Bool :=
  decide (2000000000000 ≤ a.1) && pxOK kP a.1.toNat &&
  decide ((e.2.1 : ℚ) / D - ε1 ≤ 2 * xLo kP a.1.toNat - 1) &&
  decide (2 * xHi kP a.1.toNat - 1 ≤ (e.2.1 : ℚ) / D + ε1) &&
  decide (0 < e.2.2) && decide (|(e.2.1 : ℚ) / D| ≤ 2) &&
  decide (|1 - ((e.2.1 : ℚ) / D) ^ 2 - ((e.2.2 : ℚ) / D) ^ 2| + 3 * ε1 ≤ ε2 * ((e.2.2 : ℚ) / D)) &&
  decide (|a.2 - (e.1 : ℚ) / Dz| ≤ δ)

def ownB (kP : ℕ) (D Dz : ℤ) (ε1 ε2 δ : ℚ) : List Ev → List Ent → Bool
  | [], [] => true
  | a :: A, e :: E => oClose kP D Dz ε1 ε2 δ a e && ownB kP D Dz ε1 ε2 δ A E
  | _, _ => false

noncomputable section

/-- The point of the unit circle above `z`. -/
def uOf (z : ℝ) : ℂ := ⟨z, √(1 - z ^ 2)⟩

theorem uOf_eq {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    uOf z = Complex.exp ((Real.arccos z : ℝ) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_arccos hz.1 hz.2]
    rfl
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_arccos]
    rfl

theorem uOf_pow_re {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (n : ℕ) : (uOf z ^ n).re = basis n z := by
  rw [uOf_eq hz, ← Complex.exp_nat_mul]
  have e : (n : ℂ) * ((Real.arccos z : ℝ) * Complex.I) =
      (((n : ℝ) * Real.arccos z : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.exp_ofReal_mul_I_re]
  have := basis_cos n (Real.arccos z)
  rw [Real.cos_arccos hz.1 hz.2] at this
  exact this.symm

theorem norm_uOf {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : ‖uOf z‖ ≤ 1 := by
  rw [uOf_eq hz, Complex.norm_exp_ofReal_mul_I]

theorem zE_mem {y : ℝ} (hy : 2 ≤ y) : zE y ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨a, b⟩ := physX_mem hy
  unfold zE
  constructor <;> linarith

theorem key_cast {k : ℤ} (h : 2000000000000 ≤ k) :
    (((k.toNat : ℕ) : ℝ)) / 10 ^ 12 = (k : ℝ) / 10 ^ 12 := by
  rw [cast_toNat (by omega)]

theorem key_ge {k : ℤ} (h : 2000000000000 ≤ k) : (2 : ℝ) ≤ (k : ℝ) / 10 ^ 12 := by
  have : ((2000000000000 : ℤ) : ℝ) ≤ k := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  norm_num at this ⊢
  linarith

theorem x_enc {k : ℤ} {kP : ℕ} (h : 2000000000000 ≤ k) (hk : pxOK kP k.toNat = true) :
    ((xLo kP k.toNat : ℚ) : ℝ) ≤ YCell.physX ((k : ℝ) / 10 ^ 12) ∧
      YCell.physX ((k : ℝ) / 10 ^ 12) ≤ ((xHi kP k.toNat : ℚ) : ℝ) := by
  have hA : 2000000000000 ≤ k.toNat := by omega
  have a := pxLo_le hA hk
  have b := le_pxHi hA hk
  rw [key_cast h] at a b
  unfold xLo xHi
  push_cast
  exact ⟨a, b⟩

/-- One direct atom is close to its entry. -/
theorem oClose_spec {kP : ℕ} {D Dz : ℤ} (hD : 0 < D) {ε1 ε2 δ : ℚ} {a : Ev} {e : Ent}
    (h : oClose kP D Dz ε1 ε2 δ a e = true) :
    ‖uOf (zE ((a.1 : ℝ) / 10 ^ 12)) - toC D (e.2.1, e.2.2)‖ ≤ (ε1 : ℝ) + ε2 ∧
      |((a.2 : ℚ) : ℝ) - (e.1 : ℝ) / Dz| ≤ (δ : ℝ) := by
  simp only [oClose, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h2, hx⟩, l⟩, u⟩, b0⟩, ba⟩, hs⟩, hw⟩ := h
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨x1, x2⟩ := x_enc h2 hx
  set z := zE ((a.1 : ℝ) / 10 ^ 12) with hz
  have hmem := zE_mem (key_ge h2)
  rw [← hz] at hmem
  set A : ℝ := (e.2.1 : ℝ) / D with hA
  set B : ℝ := (e.2.2 : ℝ) / D with hB
  have l' : A - (ε1 : ℝ) ≤ 2 * ((xLo kP a.1.toNat : ℚ) : ℝ) - 1 := by
    have : (((e.2.1 : ℚ) / D - ε1 : ℚ) : ℝ) ≤ ((2 * xLo kP a.1.toNat - 1 : ℚ) : ℝ) := by
      exact_mod_cast l
    push_cast at this
    exact this
  have u' : 2 * ((xHi kP a.1.toNat : ℚ) : ℝ) - 1 ≤ A + (ε1 : ℝ) := by
    have : ((2 * xHi kP a.1.toNat - 1 : ℚ) : ℝ) ≤ (((e.2.1 : ℚ) / D + ε1 : ℚ) : ℝ) := by
      exact_mod_cast u
    push_cast at this
    exact this
  have hzA : |z - A| ≤ (ε1 : ℝ) := by
    rw [abs_le]
    have : z = 2 * YCell.physX ((a.1 : ℝ) / 10 ^ 12) - 1 := rfl
    constructor <;> linarith
  have hε1 : (0 : ℝ) ≤ ε1 := (abs_nonneg _).trans hzA
  have B0 : 0 < B := by
    have : (0 : ℝ) < e.2.2 := by exact_mod_cast b0
    positivity
  have ba' : |A| ≤ 2 := by
    have : |(((e.2.1 : ℚ) / D : ℚ) : ℝ)| ≤ ((2 : ℚ) : ℝ) := by exact_mod_cast ba
    push_cast at this
    exact this
  have hs' : |1 - A ^ 2 - B ^ 2| + 3 * (ε1 : ℝ) ≤ (ε2 : ℝ) * B := by
    have : ((|1 - ((e.2.1 : ℚ) / D) ^ 2 - ((e.2.2 : ℚ) / D) ^ 2| + 3 * ε1 : ℚ) : ℝ) ≤
        ((ε2 * ((e.2.2 : ℚ) / D) : ℚ) : ℝ) := by exact_mod_cast hs
    push_cast at this
    exact this
  have hw' : |((a.2 : ℚ) : ℝ) - (e.1 : ℝ) / Dz| ≤ (δ : ℝ) := by
    have : ((|a.2 - (e.1 : ℚ) / Dz| : ℚ) : ℝ) ≤ ((δ : ℚ) : ℝ) := by exact_mod_cast hw
    push_cast at this
    exact this
  refine ⟨?_, hw'⟩
  set s := √(1 - z ^ 2) with hsd
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have ssq : s ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by nlinarith [hmem.1, hmem.2])
  have hzsq : |z ^ 2 - A ^ 2| ≤ 3 * (ε1 : ℝ) := by
    have f : z ^ 2 - A ^ 2 = (z - A) * (z + A) := by ring
    rw [f, abs_mul]
    have g : |z + A| ≤ 3 := by
      refine (abs_add_le _ _).trans ?_
      have : |z| ≤ 1 := abs_le.2 hmem
      linarith
    calc |z - A| * |z + A| ≤ (ε1 : ℝ) * 3 := mul_le_mul hzA g (abs_nonneg _) hε1
      _ = 3 * (ε1 : ℝ) := by ring
  have hsB : |s - B| ≤ (ε2 : ℝ) := by
    have f : (s - B) * (s + B) = (1 - A ^ 2 - B ^ 2) - (z ^ 2 - A ^ 2) := by
      have : (s - B) * (s + B) = s ^ 2 - B ^ 2 := by ring
      rw [this, ssq]
      ring
    have g : |s - B| * (s + B) ≤ (ε2 : ℝ) * B := by
      have : |s - B| * (s + B) = |(s - B) * (s + B)| := by
        rw [abs_mul, abs_of_pos (by linarith : 0 < s + B)]
      rw [this, f]
      refine (abs_sub _ _).trans ?_
      linarith
    by_contra hc
    push Not at hc
    have : (ε2 : ℝ) * B < |s - B| * (s + B) := by
      have hB' : B ≤ s + B := by linarith
      calc (ε2 : ℝ) * B < |s - B| * B := mul_lt_mul_of_pos_right hc B0
        _ ≤ |s - B| * (s + B) := mul_le_mul_of_nonneg_left hB' (abs_nonneg _)
    linarith
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [uOf, toC, Complex.sub_re, Complex.sub_im]
  rw [← hA, ← hB, ← hsd]
  linarith

/-- The spec list of direct atoms. -/
def specO : List Ev → List Ent → List Spec
  | a :: A, e :: E => (((a.2 : ℚ) : ℝ), uOf (zE ((a.1 : ℝ) / 10 ^ 12)), e) :: specO A E
  | _, _ => []

theorem specO_ents {kP : ℕ} {D Dz : ℤ} {ε1 ε2 δ : ℚ} : ∀ {A : List Ev} {E : List Ent},
    ownB kP D Dz ε1 ε2 δ A E = true → (specO A E).map (fun x => x.2.2) = E
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [ownB] at h
  | _ :: _, [], h => by simp [ownB] at h
  | a :: A, e :: E, h => by
    simp only [ownB, Bool.and_eq_true] at h
    simp only [specO, List.map_cons]
    rw [specO_ents h.2]

theorem specO_len {kP : ℕ} {D Dz : ℤ} {ε1 ε2 δ : ℚ} : ∀ {A : List Ev} {E : List Ent},
    ownB kP D Dz ε1 ε2 δ A E = true → (specO A E).length = A.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [ownB] at h
  | _ :: _, [], h => by simp [ownB] at h
  | a :: A, e :: E, h => by
    simp only [ownB, Bool.and_eq_true] at h
    simp only [specO, List.length_cons]
    rw [specO_len h.2]

theorem specO_ok {kP : ℕ} {D Dz : ℤ} {ε1 ε2 δ : ℚ} (hD : 0 < D) : ∀ {A : List Ev} {E : List Ent},
    ownB kP D Dz ε1 ε2 δ A E = true → ∀ x ∈ specO A E,
      ‖x.2.1‖ ≤ 1 ∧ ‖x.2.1 - toC D (x.2.2.2.1, x.2.2.2.2)‖ ≤ (ε1 : ℝ) + ε2 ∧
        |x.1 - (x.2.2.1 : ℝ) / Dz| ≤ (δ : ℝ)
  | [], [], _, x, hx => by simp [specO] at hx
  | [], _ :: _, h, _, _ => by simp [ownB] at h
  | _ :: _, [], h, _, _ => by simp [ownB] at h
  | a :: A, e :: E, h, x, hx => by
    simp only [ownB, Bool.and_eq_true] at h
    simp only [specO, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have c := oClose_spec hD h.1
      have h2 : 2000000000000 ≤ a.1 := by
        have := h.1
        simp only [oClose, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1.1.1.1.1.1.1
      exact ⟨norm_uOf (zE_mem (key_ge h2)), c.1, c.2⟩
    · exact specO_ok hD h.2 x hx

theorem specO_sum {kP : ℕ} {D Dz : ℤ} {ε1 ε2 δ : ℚ} (n : ℕ) : ∀ {A : List Ev} {E : List Ent},
    ownB kP D Dz ε1 ε2 δ A E = true →
    ((specO A E).map fun x => x.1 * (x.2.1 ^ n).re).sum = sT (A.map atomR) n
  | [], [], _ => by simp [specO, sT, evE]
  | [], _ :: _, h => by simp [ownB] at h
  | _ :: _, [], h => by simp [ownB] at h
  | a :: A, e :: E, h => by
    simp only [ownB, Bool.and_eq_true] at h
    have ih := specO_sum (kP := kP) n h.2
    have h2 : 2000000000000 ≤ a.1 := by
      have := h.1
      simp only [oClose, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1.1.1.1.1.1
    simp only [specO, List.map_cons, List.sum_cons, ih]
    rw [uOf_pow_re (zE_mem (key_ge h2))]
    simp [sT, evE, atomR]

/-- **The moments of the direct atoms.** -/
theorem own_mom {p : EPar} (h : p.OK) {kP : ℕ} {Dz : ℤ} (hDz : 0 < Dz) {ε1 ε2 δ : ℚ}
    {A : List Ev} {E : List Ent} (hc : ownB kP p.D Dz ε1 ε2 δ A E = true)
    (hb : (p.bs : ℝ) * (2 * ((ε1 : ℝ) + ε2) + 2 / p.D) ≤ 1)
    (hI : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * ((ε1 : ℝ) + ε2) + 2 / p.D)) + 2 / p.D) ≤ 1)
    (hη : etaOf p ((ε1 : ℝ) + ε2) ≤ 1) (hη0 : 0 ≤ etaOf p ((ε1 : ℝ) + ε2))
    (hg : ((E.map fun e => |e.1|).sum) * (2 * p.D ^ 2) < p.B / 2) {n : ℕ}
    (hn : n < p.I * p.bs) :
    |sT (A.map atomR) n - ((moments p E).getD n 0 : ℝ) / ((Dz * p.D ^ 2 : ℤ) : ℝ)| ≤
      (A.length : ℝ) * δ + (((E.map fun e => |e.1|).sum : ℤ) : ℝ) / Dz *
        etaOf p ((ε1 : ℝ) + ε2) := by
  have hk := specO_ents hc
  have hok := specO_ok h.D_pos hc
  have hsum : ((specO A E).map fun x => |x.2.2.1|).sum = (E.map fun e => |e.1|).sum := by
    conv_rhs => rw [← hk]
    rw [List.map_map]
    rfl
  have c := spec_close h (L := specO A E) (ε := (ε1 : ℝ) + ε2) (δ := δ) hDz
    (fun x hx => (hok x hx).1) (fun x hx => (hok x hx).2.1) (fun x hx => (hok x hx).2.2)
    hb hI hη hη0 (by rw [hsum]; exact hg) hn
  rw [specO_sum n hc, hk, specO_len hc, hsum] at c
  exact c

/-! ### Rational sums against atom sums -/

theorem evQ_close {F : ℝ → ℝ} {fh : Ev → ℚ} {δ : ℝ} (hδ : 0 ≤ δ) : ∀ (E : List Ev),
    (∀ e ∈ E, |F ((e.1 : ℝ) / 10 ^ 12) - (fh e : ℝ)| ≤ δ) →
    |evQ E F - (((E.map fun e => e.2 * fh e).sum : ℚ) : ℝ)| ≤
      (((E.map fun e => |e.2|).sum : ℚ) : ℝ) * δ
  | [], _ => by simp
  | e :: E, h => by
    have ih := evQ_close hδ E fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h0 := h e List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, evQ_cons]
    rw [Rat.cast_add, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
    set S := (((E.map fun e => e.2 * fh e).sum : ℚ) : ℝ)
    set W := (((E.map fun e => |e.2|).sum : ℚ) : ℝ)
    have ee : ((e.2 : ℚ) : ℝ) * F ((e.1 : ℝ) / 10 ^ 12) + evQ E F - (((e.2 : ℚ) : ℝ) * (fh e : ℝ) + S) =
        ((e.2 : ℚ) : ℝ) * (F ((e.1 : ℝ) / 10 ^ 12) - (fh e : ℝ)) + (evQ E F - S) := by ring
    rw [ee]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _)) ih

/-! ### The exact primitive of `log physX` -/

/-- A primitive of `log physX` on `[2, ∞)`. -/
def Hx (y : ℝ) : ℝ := y * Real.log (YCell.physX y) + √(y ^ 2 - 4)

theorem physX_form {y : ℝ} (hy : 2 ≤ y) : YCell.physX y = 2 / (y + √(y ^ 2 - 4)) := by
  unfold YCell.physX
  rw [if_pos (by linarith)]

theorem Hx_form {y : ℝ} (hy : 2 ≤ y) :
    Hx y = y * (Real.log 2 - Real.log (y + √(y ^ 2 - 4))) + √(y ^ 2 - 4) := by
  have : 0 < y + √(y ^ 2 - 4) := by have := Real.sqrt_nonneg (y ^ 2 - 4); linarith
  unfold Hx
  rw [physX_form hy, Real.log_div (by norm_num) this.ne']

theorem hasDeriv_Hx {y : ℝ} (hy : 2 < y) : HasDerivAt Hx (Real.log (YCell.physX y)) y := by
  have hp : 0 < y ^ 2 - 4 := by nlinarith
  set w := √(y ^ 2 - 4) with hw
  have w0 : 0 < w := Real.sqrt_pos.2 hp
  have hs : HasDerivAt (fun u => √(u ^ 2 - 4)) (y / w) y := by
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2 - 4) (2 * y) y := by
      simpa using ((hasDerivAt_id y).pow 2).sub_const 4
    have := h1.sqrt hp.ne'
    convert this using 1
    rw [← hw]
    field_simp
  have hyw : 0 < y + w := by linarith
  have hl : HasDerivAt (fun u => Real.log (u + √(u ^ 2 - 4))) (1 / w) y := by
    have h0 := (hasDerivAt_id' y).fun_add hs
    have := h0.log hyw.ne'
    refine this.congr_deriv ?_
    field_simp
    rw [← hw]
    ring
  have hm : HasDerivAt (fun u => u * (Real.log 2 - Real.log (u + √(u ^ 2 - 4))) + √(u ^ 2 - 4))
      (Real.log 2 - Real.log (y + w)) y := by
    have h0 := (hasDerivAt_const y (Real.log 2)).fun_sub hl
    have := ((hasDerivAt_id' y).fun_mul h0).fun_add hs
    refine this.congr_deriv ?_
    field_simp
    ring
  have e : Hx =ᶠ[nhds y] fun u => u * (Real.log 2 - Real.log (u + √(u ^ 2 - 4))) + √(u ^ 2 - 4) := by
    filter_upwards [lt_mem_nhds hy] with u hu
    exact Hx_form hu.le
  have := hm.congr_of_eventuallyEq e
  convert this using 1
  rw [physX_form hy.le, Real.log_div (by norm_num) hyw.ne']

theorem Hx_cont {lo hi : ℝ} (h2 : 2 ≤ lo) : ContinuousOn Hx (Icc lo hi) := by
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  unfold Hx
  refine (continuousOn_id.mul (hc.log fun y hy => ?_)).add (by fun_prop)
  exact (physX_mem (h2.trans hy.1)).1.ne'

theorem logX_int {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) :
    IntervalIntegrable (fun y => Real.log (YCell.physX y)) volume lo hi := by
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  refine ContinuousOn.intervalIntegrable_of_Icc hlt.le (hc.log fun y hy => ?_)
  exact (physX_mem (h2.trans hy.1)).1.ne'

theorem int_logX {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) :
    ∫ y in lo..hi, Real.log (YCell.physX y) = Hx hi - Hx lo :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le (Hx_cont h2)
    (fun _ hy => hasDeriv_Hx (lt_of_le_of_lt h2 hy.1)) (logX_int h2 hlt)

theorem pint_logX {P : List Seg} (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) :
    pint P (fun y => Real.log (YCell.physX y)) = evS P Hx := by
  induction P with
  | nil => simp [pint, evS]
  | cons g t ih =>
    rw [pint_cons, evS_cons, ih fun x hx => hP x (List.mem_cons_of_mem _ hx),
      int_logX (hP g List.mem_cons_self).1 (hP g List.mem_cons_self).2]

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CapFields

/-! ### Logarithms at keys -/

/-- Parameters of the logarithm at a key. -/
structure LPar where
  F : ℕ
  n : ℕ
  n2 : ℕ
  kP : ℕ
  mM : ℚ
  gp : ℚ

/-- `log physX` at a key, at scale `2^F`. -/
def lgX (q : LPar) (k : ℤ) : ℤ :=
  logFx q.F q.n q.n2 (pxLo q.kP k.toNat).1 (pxLo q.kP k.toNat).2

def lgOK (q : LPar) (k : ℤ) : Bool :=
  decide (2000000000000 ≤ k) && pxOK q.kP k.toNat &&
  lnormOK (pxLo q.kP k.toNat).1 (pxLo q.kP k.toNat).2 &&
  decide (|(((lnorm (pxLo q.kP k.toNat).1 (pxLo q.kP k.toNat).2).1 : ℤ) : ℚ)| ≤ q.mM) &&
  decide (xHi q.kP k.toNat / xLo q.kP k.toNat - 1 ≤ q.gp)

/-- The rational estimate of `log 2` at scale `2^F`. -/
def ln2Q (q : LPar) : ℚ := (atanhV q.F q.n2 1 3 : ℚ) / 2 ^ q.F

/-- The estimate of `log (2 physX)` at a key. -/
def l2X (q : LPar) (e : Ev) : ℚ := ln2Q q + (lgX q e.1 : ℚ) / 2 ^ q.F

/-- The estimate of `1 / (2 physX)` at a key. -/
def nuX (kP : ℕ) (e : Ev) : ℚ := 1 / (2 * xLo kP e.1.toNat)

def nuOK (kP : ℕ) (g : ℚ) (e : Ev) : Bool :=
  decide (1 / (2 * xLo kP e.1.toNat) - 1 / (2 * xHi kP e.1.toNat) ≤ g)

/-- The direct list. -/
def dirList (dP Sc : ℤ) (c0 : ℤ) (mom : List ℤ) (lam nu : ℚ) : List ℤ :=
  c0 :: dirLoop dP Sc 0 (mom.getD 1 0) ⌊lam * Sc⌋ ⌊lam * Sc⌋ ⌊-nu * Sc⌋ mom

/-- The root estimate at a key. -/
def rtX (kP : ℕ) (e : Ev) : ℚ :=
  (isqrtN (((e.1.toNat) ^ 2 - 4 * 10 ^ 24) * (2 ^ kP) ^ 2) : ℚ) / (2 ^ kP * 10 ^ 12)

/-- The estimate of `Hx` at a key. -/
def hxX (q : LPar) (e : Ev) : ℚ :=
  (e.1 : ℚ) / 10 ^ 12 * ((lgX q e.1 : ℚ) / 2 ^ q.F) + rtX q.kP e

noncomputable section

def lgErr (q : LPar) : ℝ :=
  (q.mM : ℝ) * (6 * q.n2 / 2 ^ q.F + 3 * (1 / 3 : ℝ) ^ (2 * q.n2 + 1)) +
    (6 * q.n / 2 ^ q.F + 5 / 2 * (1 / 5 : ℝ) ^ (2 * q.n + 1)) + q.gp

def ln2Err (q : LPar) : ℝ := 6 * q.n2 / 2 ^ q.F + 3 * (1 / 3 : ℝ) ^ (2 * q.n2 + 1)

theorem ln2Q_spec (q : LPar) : |Real.log 2 - ((ln2Q q : ℚ) : ℝ)| ≤ ln2Err q := by
  have := ln2_enc q.F q.n2
  unfold ln2Q ln2Err
  push_cast
  exact this

theorem pxLo_pos (kP A : ℕ) (hA : 2000000000000 ≤ A) :
    0 < (pxLo kP A).1 ∧ 0 < (pxLo kP A).2 := by
  unfold pxLo
  constructor
  · positivity
  · simp only
    omega

theorem pxHi_pos (kP A : ℕ) (hA : 2000000000000 ≤ A) :
    0 < (pxHi kP A).1 ∧ 0 < (pxHi kP A).2 := by
  unfold pxHi
  constructor
  · positivity
  · simp only
    have : 0 < A * 2 ^ kP := by positivity
    omega

theorem lgX_spec {q : LPar} {k : ℤ} (h : lgOK q k = true) :
    |Real.log (YCell.physX ((k : ℝ) / 10 ^ 12)) - (lgX q k : ℝ) / 2 ^ q.F| ≤ lgErr q := by
  simp only [lgOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h2, hx⟩, hn⟩, hm⟩, hg⟩ := h
  have hA : 2000000000000 ≤ k.toNat := by omega
  obtain ⟨p0, q0⟩ := pxLo_pos q.kP _ hA
  obtain ⟨p1, q1⟩ := pxHi_pos q.kP _ hA
  have sp := logFx_spec (F := q.F) (n := q.n) (n2 := q.n2) p0 q0 hn
  obtain ⟨xl, xh⟩ := x_enc h2 hx
  set X := YCell.physX ((k : ℝ) / 10 ^ 12)
  have l0 : (0 : ℝ) < ((xLo q.kP k.toNat : ℚ) : ℝ) := by
    unfold xLo
    push_cast
    have a : (0 : ℝ) < ((pxLo q.kP k.toNat).1 : ℝ) := by exact_mod_cast p0
    have b : (0 : ℝ) < ((pxLo q.kP k.toNat).2 : ℝ) := by exact_mod_cast q0
    positivity
  have hXpos : 0 < X := lt_of_lt_of_le l0 xl
  have hm' : |(((lnorm (pxLo q.kP k.toNat).1 (pxLo q.kP k.toNat).2).1 : ℤ) : ℝ)| ≤ (q.mM : ℝ) := by
    exact_mod_cast hm
  have hg' : ((xHi q.kP k.toNat : ℚ) : ℝ) / ((xLo q.kP k.toNat : ℚ) : ℝ) - 1 ≤ (q.gp : ℝ) := by
    exact_mod_cast hg
  have c1 : Real.log ((xLo q.kP k.toNat : ℚ) : ℝ) ≤ Real.log X := Real.log_le_log l0 xl
  have c2 : Real.log X ≤ Real.log ((xLo q.kP k.toNat : ℚ) : ℝ) + q.gp := by
    have a := Real.log_le_log hXpos xh
    have hr : (0 : ℝ) < ((xHi q.kP k.toNat : ℚ) : ℝ) / ((xLo q.kP k.toNat : ℚ) : ℝ) :=
      div_pos (lt_of_lt_of_le hXpos xh) l0
    have b := Real.log_le_sub_one_of_pos hr
    rw [Real.log_div (lt_of_lt_of_le hXpos xh).ne' l0.ne'] at b
    linarith
  have ex : ((xLo q.kP k.toNat : ℚ) : ℝ) =
      ((pxLo q.kP k.toNat).1 : ℝ) / ((pxLo q.kP k.toNat).2 : ℝ) := by
    unfold xLo
    push_cast
    rfl
  rw [← ex] at sp
  have hpos : (0 : ℝ) ≤ 6 * q.n2 / 2 ^ q.F + 3 * (1 / 3 : ℝ) ^ (2 * q.n2 + 1) := by positivity
  have sp2 := sp.trans (add_le_add_left (mul_le_mul_of_nonneg_right hm' hpos) _)
  have g0 : (0 : ℝ) ≤ q.gp := by
    have := c1.trans c2
    linarith
  unfold lgErr
  change |Real.log X - ((logFx q.F q.n q.n2 _ _ : ℤ) : ℝ) / 2 ^ q.F| ≤ _
  have a := abs_le.1 sp2
  rw [abs_le]
  constructor <;> linarith [a.1, a.2]

theorem floorSc {x : ℚ} {Sc : ℤ} (hS : 0 < Sc) :
    |(x : ℝ) - ((⌊x * Sc⌋ : ℤ) : ℝ) / Sc| ≤ 1 / Sc := by
  have hr : (0 : ℝ) < Sc := by exact_mod_cast hS
  have a : ((⌊x * Sc⌋ : ℤ) : ℚ) ≤ x * Sc := Int.floor_le _
  have b : x * Sc < ((⌊x * Sc⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  have a' : ((⌊x * Sc⌋ : ℤ) : ℝ) ≤ (x : ℝ) * Sc := by exact_mod_cast a
  have b' : (x : ℝ) * Sc < ((⌊x * Sc⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast b
  have e : (x : ℝ) - ((⌊x * Sc⌋ : ℤ) : ℝ) / Sc = ((x : ℝ) * Sc - ((⌊x * Sc⌋ : ℤ) : ℝ)) / Sc := by
    field_simp
  rw [e, abs_div, abs_of_pos hr, abs_of_nonneg (by linarith)]
  exact div_le_div_of_nonneg_right (by linarith) hr.le

theorem one_add_z {y : ℝ} : 1 + zE y = 2 * YCell.physX y := by unfold zE; ring

/-- `sI 0` is the atom sum of `log (2 physX)`. -/
theorem sI0 (E : List Ev) :
    sI (E.map atomR) 0 = evQ E fun y => Real.log (2 * YCell.physX y) := by
  unfold sI
  rw [evE_atomR]
  refine evQ_congr fun y => ?_
  simp only [iP, one_add_z]

theorem sJ0 (E : List Ev) :
    sJ (E.map atomR) 0 = -evQ E fun y => 1 / (2 * YCell.physX y) := by
  unfold sJ
  rw [evE_atomR, ← evQ_fun_neg]
  refine evQ_congr fun y => ?_
  simp only [jP, one_add_z]
  ring

theorem sG0 (E : List (ℝ × ℝ)) : sG E 0 = sI E 0 := by
  have : sJ E 1 + sJ E 0 = 1 * sJ E 1 + 1 * sJ E 0 := by ring
  unfold sG
  rw [show 0 + 1 = 1 from rfl, this]
  unfold sJ sI
  rw [← evE_lin]
  refine evE_congr fun y => ?_
  simp only [jP, iP]
  ring

theorem sH0 (E : List (ℝ × ℝ)) : sH E 0 = sT E 1 := by
  have : sI E 1 + sI E 0 = 1 * sI E 1 + 1 * sI E 0 := by ring
  unfold sH
  rw [show 0 + 1 = 1 from rfl, this]
  unfold sI sT
  rw [← evE_lin]
  refine evE_congr fun y => ?_
  simp only [iP, basis_one']
  ring

/-- Budget of the seeds. -/
structure SeedOK (q : LPar) (E : List Ev) (g : ℚ) : Prop where
  lg : ∀ e ∈ E, lgOK q e.1 = true
  nu : ∀ e ∈ E, nuOK q.kP g e = true

theorem lam_close {q : LPar} {E : List Ev} {g : ℚ} (h : SeedOK q E g) (hpos : 0 ≤ ln2Err q + lgErr q) :
    |evQ E (fun y => Real.log (2 * YCell.physX y)) -
        (((E.map fun e => e.2 * l2X q e).sum : ℚ) : ℝ)| ≤
      (((E.map fun e => |e.2|).sum : ℚ) : ℝ) * (ln2Err q + lgErr q) := by
  refine evQ_close hpos E fun e he => ?_
  have hg := h.lg e he
  have a := lgX_spec hg
  have b := ln2Q_spec q
  simp only [lgOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  have h2 := hg.1.1.1.1
  obtain ⟨x1, _⟩ := physX_mem (key_ge h2)
  rw [Real.log_mul (by norm_num) x1.ne']
  unfold l2X
  push_cast
  have e' : Real.log 2 + Real.log (YCell.physX ((e.1 : ℝ) / 10 ^ 12)) -
      (((ln2Q q : ℚ) : ℝ) + (lgX q e.1 : ℝ) / 2 ^ q.F) =
      (Real.log 2 - ((ln2Q q : ℚ) : ℝ)) +
        (Real.log (YCell.physX ((e.1 : ℝ) / 10 ^ 12)) - (lgX q e.1 : ℝ) / 2 ^ q.F) := by ring
  rw [e']
  exact (abs_add_le _ _).trans (add_le_add b a)

theorem nu_close {q : LPar} {E : List Ev} {g : ℚ} (h : SeedOK q E g) (hg0 : (0 : ℝ) ≤ g) :
    |evQ E (fun y => 1 / (2 * YCell.physX y)) -
        (((E.map fun e => e.2 * nuX q.kP e).sum : ℚ) : ℝ)| ≤
      (((E.map fun e => |e.2|).sum : ℚ) : ℝ) * (g : ℝ) := by
  refine evQ_close hg0 E fun e he => ?_
  have hl := h.lg e he
  have hn := h.nu e he
  simp only [lgOK, Bool.and_eq_true, decide_eq_true_eq] at hl
  have h2 := hl.1.1.1.1
  obtain ⟨xl, xh⟩ := x_enc h2 hl.1.1.1.2
  simp only [nuOK, decide_eq_true_eq] at hn
  have hn' : 1 / (2 * ((xLo q.kP e.1.toNat : ℚ) : ℝ)) - 1 / (2 * ((xHi q.kP e.1.toNat : ℚ) : ℝ)) ≤
      (g : ℝ) := by exact_mod_cast hn
  have hA : 2000000000000 ≤ e.1.toNat := by omega
  obtain ⟨p0, q0⟩ := pxLo_pos q.kP _ hA
  have l0 : (0 : ℝ) < ((xLo q.kP e.1.toNat : ℚ) : ℝ) := by
    unfold xLo
    push_cast
    have a : (0 : ℝ) < ((pxLo q.kP e.1.toNat).1 : ℝ) := by exact_mod_cast p0
    have b : (0 : ℝ) < ((pxLo q.kP e.1.toNat).2 : ℝ) := by exact_mod_cast q0
    positivity
  set X := YCell.physX ((e.1 : ℝ) / 10 ^ 12)
  have hX : 0 < X := lt_of_lt_of_le l0 xl
  have m1 : 1 / (2 * X) ≤ 1 / (2 * ((xLo q.kP e.1.toNat : ℚ) : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have m2 : 1 / (2 * ((xHi q.kP e.1.toNat : ℚ) : ℝ)) ≤ 1 / (2 * X) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold nuX
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-- **The direct stream from its checks.** -/
theorem own_stream {p : EPar} (h : p.OK) {N : ℕ} (hN : 1 ≤ N) (hIN : N + 2 = p.I * p.bs)
    {P : List Seg} {A : List Ev} (hA : Atoms P (A.map atomR))
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) {q : LPar} {Dz : ℤ} (hDz : 0 < Dz) {ε1 ε2 δ g : ℚ}
    {E : List Ent} (hc : ownB q.kP p.D Dz ε1 ε2 δ A E = true) (hs : SeedOK q A g)
    (hb : (p.bs : ℝ) * (2 * ((ε1 : ℝ) + ε2) + 2 / p.D) ≤ 1)
    (hI : (p.I : ℝ) * (2 * ((p.bs : ℝ) * (2 * ((ε1 : ℝ) + ε2) + 2 / p.D)) + 2 / p.D) ≤ 1)
    (hη : etaOf p ((ε1 : ℝ) + ε2) ≤ 1) (hη0 : 0 ≤ etaOf p ((ε1 : ℝ) + ε2))
    (hg : ((E.map fun e => |e.1|).sum) * (2 * p.D ^ 2) < p.B / 2)
    {dP : ℕ} (hdP : 0 < dP) {Em h0 : ℝ}
    (hEm : (A.length : ℝ) * δ + (((E.map fun e => |e.1|).sum : ℤ) : ℝ) / Dz *
        etaOf p ((ε1 : ℝ) + ε2) ≤ Em) (hEm0 : 0 ≤ Em) (hg0 : (0 : ℝ) ≤ g)
    (hlg0 : 0 ≤ ln2Err q + lgErr q) (hEh : Em ≤ h0)
    (hl : (((A.map fun e => |e.2|).sum : ℚ) : ℝ) * (ln2Err q + lgErr q) +
      1 / ((Dz * p.D ^ 2 : ℤ) : ℝ) ≤ h0)
    (hν : (((A.map fun e => |e.2|).sum : ℚ) : ℝ) * (g : ℝ) + 1 / ((Dz * p.D ^ 2 : ℤ) : ℝ) ≤ h0)
    {c0 : ℤ} {δ0 Mx : ℝ} (hc0 : |evS P (Adir 0) - (c0 : ℝ) / dP| ≤ δ0)
    (hV : ∀ t ∈ Ioc (0 : ℝ) 1, dirV N P (A.map atomR) t ≤ Mx) :
    Close dP (fun t => pint P fun y => Real.log |t - YCell.physX y|)
      (dirList (dP : ℤ) (Dz * p.D ^ 2) c0 (moments p E) ((A.map fun e => e.2 * l2X q e).sum)
        ((A.map fun e => e.2 * nuX q.kP e).sum))
      (2 / N * Mx + δ0 + (N : ℝ) * (1 / dP + (4 * (Bud.eJ ⟨h0, Em + 2 / ((Dz * p.D ^ 2 : ℤ) : ℝ), N⟩) +
        (Em + 2 / ((Dz * p.D ^ 2 : ℤ) : ℝ))))) := by
  have hS : 0 < Dz * p.D ^ 2 := by have := h.D_pos; positivity
  have hkeys : ∀ e ∈ A.map atomR, 2 ≤ e.1 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
    have := hs.lg a ha
    simp only [lgOK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact key_ge this.1.1.1.1
  have hm : ∀ n ≤ N + 1, |sT (A.map atomR) n - ((moments p E).getD n 0 : ℝ) /
      ((Dz * p.D ^ 2 : ℤ) : ℝ)| ≤ Em := fun n hn =>
    (own_mom h hDz hc hb hI hη hη0 hg (by omega)).trans hEm
  set Sc := Dz * p.D ^ 2 with hSc
  set lam := (A.map fun e => e.2 * l2X q e).sum
  set nu := (A.map fun e => e.2 * nuX q.kP e).sum
  have e2 : |sI (A.map atomR) 0 - ((⌊lam * Sc⌋ : ℤ) : ℝ) / Sc| ≤ h0 := by
    rw [sI0]
    have a := lam_close hs hlg0
    have b := floorSc (x := lam) hS
    refine le_trans ?_ hl
    have := abs_sub_le (evQ A fun y => Real.log (2 * YCell.physX y)) (lam : ℝ)
      (((⌊lam * Sc⌋ : ℤ) : ℝ) / Sc)
    linarith
  have e4 : |sJ (A.map atomR) 0 - ((⌊-nu * Sc⌋ : ℤ) : ℝ) / Sc| ≤ h0 := by
    rw [sJ0]
    have a := nu_close hs hg0
    have b := floorSc (x := -nu) hS
    refine le_trans ?_ hν
    have e : -(evQ A fun y => 1 / (2 * YCell.physX y)) - ((⌊-nu * Sc⌋ : ℤ) : ℝ) / Sc =
        -((evQ A fun y => 1 / (2 * YCell.physX y)) - (nu : ℝ)) +
          (((-nu : ℚ) : ℝ) - ((⌊-nu * Sc⌋ : ℤ) : ℝ) / Sc) := by
      push_cast
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith
  have e1 : |sH (A.map atomR) 0 - ((moments p E).getD 1 0 : ℝ) / Sc| ≤ h0 := by
    rw [sH0]
    exact (hm 1 (by omega)).trans hEh
  have e3 : |sG (A.map atomR) 0 - ((⌊lam * Sc⌋ : ℤ) : ℝ) / Sc| ≤ h0 := by
    rw [sG0]
    exact e2
  have hlen : (moments p E).length = N + 2 := by rw [len_moments, hIN]
  have hh0 : 0 ≤ h0 := hEm0.trans hEh
  exact dir_close hN hA hP hkeys hdP hS hlen hEm0 hm hh0 e1 e2 e3 e4 hc0 hV

/-- **The bounded-variation tail from its checks.** -/
theorem hV_of (p : BinPar) (N w M : ℕ) (hB : 1 ≤ p.B) (hN : 1 ≤ N) {E : List Ev} {G : List GS}
    (hgrid : gridOK p = true) (hat : E.all (atomOK p) = true) (hseg : G.all (segOK p) = true)
    (hv : hvCheck p N w M (pairsAll p E G) = true)
    (hG : ∀ g ∈ G, 2000000000000 ≤ g.1 ∧ g.1 < g.2.1)
    (hP : ∀ g ∈ G.map segR, 2 ≤ g.lo ∧ g.lo < g.hi) (hE : ∀ e ∈ E.map atomR, 2 ≤ e.1) :
    ∀ t ∈ Ioc (0 : ℝ) 1, dirV N (G.map segR) (E.map atomR) t ≤
      (M : ℝ) / (2 ^ 64 * 2 ^ (p.kb + p.h)) := by
  obtain ⟨_, hconv⟩ := pilot_conv p N w M _ hB hv
  simp only [List.all_eq_true] at hat hseg
  have hbin : ∀ j < p.B, binUp p.B (G.map segR) (E.map atomR) j ≤
      (pv (pairsAll p E G) j : ℝ) / 2 ^ (p.kb + p.h) := fun j hj =>
    binUp_pilot p hB E G hat (fun g hg => ⟨(hG g hg).1, (hG g hg).2, hseg g hg⟩)
      (gridOK_spec hgrid) j hj
  exact dirV_le_of_packed (N := N) (B := p.B) hB hP hE (Kn := Kn N p.B)
    (mn := pv (pairsAll p E G)) (dK := 2 ^ 64) (dm := 2 ^ (p.kb + p.h))
    (by positivity) (by positivity) (fun d _ => kk_le_Kn hN hB d) hbin hconv

theorem sqrt_enc {r t M : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (hM : 0 ≤ M) (h1 : r * r ≤ M * t ^ 2)
    (h2 : M * t ^ 2 ≤ (r + 1) * (r + 1)) : r / t ≤ √M ∧ √M ≤ (r + 1) / t := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith

/-- The opposite constant. -/
theorem opp_const {P : List Seg} {A : List Ev} (hA : Atoms P (A.map atomR))
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) {q : LPar} (hl : ∀ e ∈ A, lgOK q e.1 = true)
    {K : ℚ} (hK : ∀ e ∈ A, (e.1 : ℚ) / 10 ^ 12 ≤ K)
    (hlg : 0 ≤ lgErr q) (hK0 : (0 : ℝ) ≤ K) :
    pint P (fun y => Real.log (YCell.physX y)) ≤
      -(((A.map fun e => e.2 * hxX q e).sum : ℚ) : ℝ) +
        (((A.map fun e => |e.2|).sum : ℚ) : ℝ) * ((K : ℝ) * lgErr q + 1 / (2 ^ q.kP * 10 ^ 12)) := by
  rw [pint_logX hP, hA Hx, evE_atomR]
  have c := evQ_close (F := Hx) (fh := hxX q)
    (δ := (K : ℝ) * lgErr q + 1 / (2 ^ q.kP * 10 ^ 12)) (by positivity) A fun e he => ?_
  · have := abs_le.1 c
    linarith [this.1]
  have hg := hl e he
  have sp := lgX_spec hg
  simp only [lgOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  have h2 := hg.1.1.1.1
  have hx := hg.1.1.1.2
  have hy := key_ge h2
  set y := (e.1 : ℝ) / 10 ^ 12 with hyd
  have hKy : y ≤ K := by
    have : ((e.1 : ℚ) / 10 ^ 12 : ℚ) ≤ K := hK e he
    have r : (((e.1 : ℚ) / 10 ^ 12 : ℚ) : ℝ) ≤ K := by exact_mod_cast this
    push_cast at r
    exact r
  -- the root
  have hAn : 2000000000000 ≤ e.1.toNat := by omega
  obtain ⟨r1, r2⟩ := sqOK_spec hx
  set t : ℕ := 2 ^ q.kP with ht
  have hsq : 4 * 10 ^ 24 ≤ e.1.toNat ^ 2 :=
    calc 4 * 10 ^ 24 = 2000000000000 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hAn 2
  set M : ℕ := e.1.toNat ^ 2 - 4 * 10 ^ 24 with hM
  set r : ℕ := isqrtN (M * t ^ 2) with hr
  have hMr : (M : ℝ) = (e.1.toNat : ℝ) ^ 2 - 4 * 10 ^ 24 := by
    rw [hM, Nat.cast_sub hsq]
    push_cast
    ring
  have hyA : y = (e.1.toNat : ℝ) / 10 ^ 12 := (key_cast h2).symm
  have hroot : √(y ^ 2 - 4) = √(M : ℝ) / 10 ^ 12 := by
    rw [show y ^ 2 - 4 = (M : ℝ) / (10 ^ 12) ^ 2 by rw [hMr, hyA]; field_simp,
      Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq (by norm_num)]
  have tr : (0 : ℝ) < t := by rw [ht]; positivity
  obtain ⟨b1, b2⟩ := sqrt_enc tr (Nat.cast_nonneg r) (Nat.cast_nonneg M)
    (by exact_mod_cast r1) (by exact_mod_cast r2.le)
  have hrt : |√(y ^ 2 - 4) - ((rtX q.kP e : ℚ) : ℝ)| ≤ 1 / (2 ^ q.kP * 10 ^ 12) := by
    have er : ((rtX q.kP e : ℚ) : ℝ) = (r : ℝ) / t / 10 ^ 12 := by
      unfold rtX
      push_cast
      rw [ht, hr, hM]
      push_cast
      rw [div_div]
    rw [hroot, er]
    have tq : (t : ℝ) = 2 ^ q.kP := by rw [ht]; push_cast; rfl
    rw [← tq, abs_le]
    have s1 : (r : ℝ) / t / 10 ^ 12 ≤ √(M : ℝ) / 10 ^ 12 := by gcongr
    have s2 : √(M : ℝ) / 10 ^ 12 ≤ ((r : ℝ) + 1) / t / 10 ^ 12 := by gcongr
    have s3 : ((r : ℝ) + 1) / t / 10 ^ 12 = (r : ℝ) / t / 10 ^ 12 + 1 / (t * 10 ^ 12) := by
      field_simp
    have s4 : (0 : ℝ) < 1 / (t * 10 ^ 12) := by positivity
    constructor <;> linarith
  unfold Hx hxX
  push_cast
  rw [← hyd]
  have e' : y * Real.log (YCell.physX y) + √(y ^ 2 - 4) -
      (y * ((lgX q e.1 : ℝ) / 2 ^ q.F) + ((rtX q.kP e : ℚ) : ℝ)) =
      y * (Real.log (YCell.physX y) - (lgX q e.1 : ℝ) / 2 ^ q.F) +
        (√(y ^ 2 - 4) - ((rtX q.kP e : ℚ) : ℝ)) := by ring
  rw [e']
  refine (abs_add_le _ _).trans (add_le_add ?_ hrt)
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ y)]
  exact mul_le_mul hKy sp (abs_nonneg _) hK0

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.KronSquare
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

/-! ### The square certificate as one packed integer identity

No product list is formed and nothing is decoded: the symmetric Laurent values of the lists are
tree-packed and the identity is checked on the packed integers. -/

/-- Packed symmetric Laurent value of a list of length `n + 1`. -/
def liftK (lg K n : ℕ) (c : List ℤ) : ℤ :=
  pow2 (K * n) * packT lg (pow2 K) c + packT lg (pow2 K) c.reverse

/-- `2 d s + q ⋆ q = 2 d c` on the packed values. -/
def kronEq (K m lgs lgq : ℕ) (d c : ℤ) (s q : List ℤ) : Bool :=
  decide (2 * d * liftK lgs K (2 * m) s + liftK lgq K m q * liftK lgq K m q =
    2 * (2 * d * c) * pow2 (K * (2 * m)))

theorem pk_eq_horner (B : ℤ) : ∀ c : List ℤ, pk B c = hornerZ B c
  | [] => rfl
  | a :: t => by simp [pk, hornerZ, pk_eq_horner B t]

theorem liftK_eq {lg K n : ℕ} {c : List ℤ} (hl : c.length = n + 1) (hg : n + 1 ≤ 2 ^ lg) :
    liftK lg K n c = vz (pow2 K) n c 0 := by
  have h1 : packT lg (pow2 K) c = hornerZ (pow2 K) c := by
    rw [packT_eq lg _ _ (by omega), pk_eq_horner]
  have h2 : packT lg (pow2 K) c.reverse = hornerZ (pow2 K) c.reverse := by
    rw [packT_eq lg _ _ (by simp; omega), pk_eq_horner]
  have := vz_eq (pow2 K) n 0 c 0 (by omega)
  unfold liftK
  rw [h1, h2, this, ← pow2_mul_pow]
  simp

theorem vz_smulZ (B : ℤ) (n : ℕ) (a : ℤ) : ∀ (c : List ℤ) (k : ℕ),
    vz B n (smulZ a c) k = a * vz B n c k
  | [], _ => by simp [smulZ, vz]
  | b :: t, k => by
    have := vz_smulZ B n a t (k + 1)
    simp only [smulZ, List.map_cons, vz] at this ⊢
    rw [this]
    ring

theorem vz_zeros (B : ℤ) (n : ℕ) : ∀ (e k : ℕ), vz B n (List.replicate e 0) k = 0
  | 0, _ => by simp [vz]
  | e + 1, k => by simp [List.replicate_succ, vz, vz_zeros B n e (k + 1)]

theorem l1_smulZ (a : ℤ) : ∀ c : List ℤ, l1 (smulZ a c) = |a| * l1 c
  | [] => by simp [smulZ, l1]
  | b :: t => by
    have := l1_smulZ a t
    simp only [smulZ, List.map_cons, l1] at this ⊢
    rw [this, abs_mul]
    ring

theorem len_addZ_eq {u v : List ℤ} {n : ℕ} (hu : u.length = n) (hv : v.length = n) :
    (addZ u v).length = n := by
  rw [len_addZ, hu, hv]
  simp

noncomputable section

/-- **Packed square certificate.** -/
theorem kron_le {K m lgs lgq : ℕ} {d c : ℤ} {s q : List ℤ} (hd : 0 < d)
    (hs : s.length = 2 * m + 1) (hq : q.length = m + 1) (hgs : 2 * m + 1 ≤ 2 ^ lgs)
    (hgq : m + 1 ≤ 2 ^ lgq) (hE : kronEq K m lgs lgq d c s q = true)
    (hb : 4 * (2 * d * l1 s + 2 * l1 q * l1 q) < pow2 K) (hc : 8 * (2 * d * |c|) < pow2 K)
    (x : ℝ) : rawSum s 0 x ≤ c := by
  have hB : 0 < pow2 K := by unfold pow2; positivity
  set B := pow2 K with hBd
  have hqn : q ≠ [] := by
    intro h
    rw [h] at hq
    simp at hq
  have hX := len_mulZ q 0 q hqn hqn
  have hXl : (mulZ q 0 q).length = 2 * m + 1 := by
    rw [hX, hq]
    omega
  set X := mulZ q 0 q with hXd
  set w := addZ (smulZ (2 * d) s) X with hw
  have hwl : w.length = 2 * m + 1 := len_addZ_eq (by simp [smulZ, hs]) hXl
  set T : List ℤ := (2 * d * c) :: List.replicate (2 * m) 0 with hT
  have hTl : T.length = 2 * m + 1 := by simp [hT]
  -- packed values
  have hE' : 2 * d * vz B (2 * m) s 0 + vz B m q 0 * vz B m q 0 =
      2 * (2 * d * c) * pow2 (K * (2 * m)) := by
    have := of_decide_eq_true hE
    rw [liftK_eq hs hgs, liftK_eq hq hgq] at this
    exact this
  have hvX : vz B (2 * m) X 0 = vz B m q 0 * vz B m q 0 := by
    have := vz_mulZ B (n := m) (m := m) q 0 q (by omega) (by omega)
    rw [show m + m = 2 * m by omega] at this
    exact this
  have hvw : vz B (2 * m) w 0 = vz B (2 * m) T 0 := by
    rw [hw, vz_addZ, vz_smulZ, hvX, hE', hT]
    simp only [vz, vz_zeros, tau]
    rw [← pow2_mul_pow]
    simp only [add_zero, Nat.sub_zero]
    ring
  obtain ⟨x0, xt, hwc⟩ : ∃ x0 xt, w = x0 :: xt := by
    rcases h : w with _ | ⟨x0, xt⟩
    · rw [h] at hwl
      simp at hwl
    · exact ⟨x0, xt, rfl⟩
  have hxt : xt.length = 2 * m := by
    rw [hwc] at hwl
    simpa using hwl
  have hnz : w ≠ [] := by rw [hwc]; simp
  have hTz : T ≠ [] := by simp [hT]
  have l1 : liftV B w = liftV B T := by
    rw [← vz_liftV B hnz, ← vz_liftV B hTz, hwl, hTl]
    exact hvw
  rw [hwc, hT, liftV_cons, liftV_cons] at l1
  -- digits
  have hl1w : CatalanMeasure.Signed.ChebSquare.l1 (x0 :: xt) ≤
      2 * d * CatalanMeasure.Signed.ChebSquare.l1 s +
        2 * CatalanMeasure.Signed.ChebSquare.l1 q * CatalanMeasure.Signed.ChebSquare.l1 q := by
    rw [← hwc, hw]
    refine (l1_addZ_le _ _).trans ?_
    rw [l1_smulZ, abs_of_pos (by positivity : 0 < 2 * d)]
    have := l1_mulZ_le q 0 q
    linarith
  have hsym : ∀ {a : ℤ} {t : List ℤ}, ∀ e ∈ symZ (2 * a) t,
      |e| ≤ 2 * CatalanMeasure.Signed.ChebSquare.l1 (a :: t) := by
    intro a t e he
    have hXe : ∀ y ∈ (a :: t), |y| ≤ CatalanMeasure.Signed.ChebSquare.l1 (a :: t) :=
      fun y hy => abs_le_l1 _ y hy
    have h0 := CatalanMeasure.GenD.Signed.RouteI.KronSquare.l1_nonneg (a :: t)
    simp only [symZ, List.mem_append, List.mem_reverse, List.mem_cons] at he
    rcases he with he | rfl | he
    · have := hXe e (by simp [he])
      linarith
    · rw [abs_mul]
      have := hXe a (by simp)
      simp
      linarith
    · have := hXe e (by simp [he])
      linarith
  have hlen : (symZ (2 * x0) xt).length =
      (symZ (2 * (2 * d * c)) (List.replicate (2 * m) 0)).length := by
    simp [symZ, hxt]
  have heq := hornerZ_inj hB _ _ hlen
    (fun e he => by
      have := hsym e he
      nlinarith [hl1w, hb, this])
    (fun e he => by
      have := hsym e he
      have l : CatalanMeasure.Signed.ChebSquare.l1 ((2 * d * c) :: List.replicate (2 * m) 0) =
          |2 * d * c| := by
        have z : ∀ n : ℕ, CatalanMeasure.Signed.ChebSquare.l1 (List.replicate n (0 : ℤ)) = 0 := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih => simp [List.replicate_succ, CatalanMeasure.Signed.ChebSquare.l1, ih]
        simp [CatalanMeasure.Signed.ChebSquare.l1, z]
      rw [l, abs_mul, abs_of_pos (by positivity : 0 < 2 * d)] at this
      nlinarith [hc, this])
    l1
  have hdrop := congrArg (List.drop (2 * m)) heq
  have d1 : (symZ (2 * x0) xt).drop (2 * m) = (2 * x0) :: xt := by
    rw [symZ, List.drop_left' (by simp [hxt])]
  have d2 : (symZ (2 * (2 * d * c)) (List.replicate (2 * m) 0)).drop (2 * m) =
      (2 * (2 * d * c)) :: List.replicate (2 * m) 0 := by
    rw [symZ, List.drop_left' (by simp)]
  rw [d1, d2] at hdrop
  have hx0 : x0 = 2 * d * c := by
    have := (List.cons.inj hdrop).1
    omega
  have hxt' : xt = List.replicate (2 * m) 0 := (List.cons.inj hdrop).2
  have hwT : w = T := by rw [hwc, hT, hx0, hxt']
  -- evaluate
  have ev := congrArg (fun l => rawSum l 0 x) hwT
  simp only [hw, rawSum_addZ, rawSum_smulZ, hXd, rawSum_mulZ] at ev
  have z : ∀ (n k : ℕ), rawSum (List.replicate n (0 : ℤ)) k x = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro k
      simp [List.replicate_succ, rawSum_cons, ih]
  rw [hT, rawSum_cons, z, basis_zero] at ev
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  push_cast at ev
  have hsq := mul_self_nonneg (rawSum q 0 x)
  nlinarith

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory intervalIntegral
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### The physical pieces of a free row -/

theorem pint_append (A B : List Seg) (f : ℝ → ℝ) : pint (A ++ B) f = pint A f + pint B f := by
  simp [pint]

theorem pint_dir_nonpos {P : List Seg} (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi)
    (hρ : ∀ g ∈ P, 0 ≤ g.rho) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    pint P (fun y => Real.log |t - YCell.physX y|) ≤ 0 := by
  induction P with
  | nil => simp [pint]
  | cons g l ih =>
    have i1 := ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))
      (fun x hx => hρ x (List.mem_cons_of_mem _ hx))
    obtain ⟨a, b⟩ := hP g List.mem_cons_self
    have r := hρ g List.mem_cons_self
    rw [pint_cons]
    have hi : ∫ y in g.lo..g.hi, Real.log |t - YCell.physX y| ≤ 0 := by
      have : 0 ≤ ∫ y in g.lo..g.hi, -Real.log |t - YCell.physX y| := by
        refine intervalIntegral.integral_nonneg b.le fun y hy => ?_
        obtain ⟨x0, x1⟩ := physX_mem (a.trans hy.1)
        have : |t - YCell.physX y| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        have := Real.log_nonpos (abs_nonneg (t - YCell.physX y)) this
        linarith
      rw [intervalIntegral.integral_neg] at this
      linarith
    have := mul_nonpos_of_nonneg_of_nonpos r hi
    linarith

theorem own_part {l : List YCell} {P1 P2 : List Seg} {sg t : ℝ} (hsg : sg = 1 ∨ sg = -1)
    (hl : ∀ c ∈ l, 2 ≤ c.lo ∨ c.hi ≤ -2)
    (hb : ∀ F : ℝ → ℝ, evC l F = evS (P1 ++ P2) (fun y => sg * F (sg * y)))
    (hP : ∀ g ∈ P1 ++ P2, 2 ≤ g.lo ∧ g.lo < g.hi) (hρ : ∀ g ∈ P2, 0 ≤ g.rho)
    (h0 : 0 < t) (h1 : t ≤ 1) :
    avgL l (rowK (sg * t)) ≤ pint P1 (fun y => Real.log |t - YCell.physX y|) +
      pint (P1 ++ P2) (fun y => Real.log |1 - YCell.physX y * t|) := by
  rw [avg_row_same hsg hl hb hP h0]
  rw [pint_split (a := fun y => Real.log |t - YCell.physX y|)
    (b := fun y => Real.log |1 - YCell.physX y * t|)
    (fun g hg => (hP g hg).2.le) (fun g hg => rowlog2_int (hP g hg).1 (hP g hg).2 h0 h1)
    (fun g hg => rowlog_int (hP g hg).1 (hP g hg).2 h0 h1)
    (fun g _ y _ => by unfold rowK; rw [mul_comm t])]
  rw [pint_append]
  have := pint_dir_nonpos (fun g hg => hP g (List.mem_append_right _ hg)) hρ h0 h1
  linarith

theorem opp_part {l : List YCell} {P : List Seg} {sg t : ℝ} (hsg : sg = 1 ∨ sg = -1)
    (hl : ∀ c ∈ l, 2 ≤ c.lo ∨ c.hi ≤ -2)
    (hb : ∀ F : ℝ → ℝ, evC l F = evS P (fun y => -sg * F (-sg * y)))
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (h0 : 0 < t) :
    avgL l (rowK (sg * t)) = pint P (fun y => Real.log (YCell.physX y)) +
      pint P (fun y => Real.log (1 + y * t + t ^ 2)) := by
  rw [avg_row_opp hsg hl hb hP h0]
  refine pint_split (fun g hg => (hP g hg).2.le) (fun g hg => logX_int (hP g hg).1 (hP g hg).2)
    (fun g hg => ?_) (fun g hg y hy => rowK_opp ((hP g hg).1.trans hy.1) h0)
  refine ContinuousOn.intervalIntegrable_of_Icc (hP g hg).2.le ?_
  refine ContinuousOn.log (by fun_prop) fun y hy => ?_
  have hy2 : 2 ≤ y := (hP g hg).1.trans (by simpa [uIcc_of_le (hP g hg).2.le] using hy.1)
  have : 0 < 1 + y * t + t ^ 2 := by nlinarith
  exact this.ne'

theorem avQ_filter (s : Bool) (f : QA → Bool) (t : ℝ) : ∀ L : List QA,
    avQ s L t = avQ s (L.filter f) t + avQ s (L.filter fun x => !f x) t
  | [] => by simp [avQ_nil]
  | x :: l => by
    have ih := avQ_filter s f t l
    cases hf : f x
    · simp only [List.filter_cons, hf, avQ_cons, Bool.not_false, if_true, Bool.false_eq_true,
        if_false, ite_false, ite_true]
      rw [ih]
      ring
    · simp only [List.filter_cons, hf, avQ_cons, Bool.not_true, if_true, Bool.false_eq_true,
        if_false, ite_false, ite_true]
      rw [ih]
      ring

theorem close_split (s : Bool) {dP : ℕ} (f : QA → Bool) {L : List QA} {a b : List ℤ} {e1 e2 : ℝ}
    (h1 : Close dP (avQ s (L.filter f)) a e1)
    (h2 : Close dP (avQ s (L.filter fun x => !f x)) b e2) :
    Close dP (avQ s L) (addZ a b) (e1 + e2) := by
  intro t ht
  have := (h1.add h2) t ht
  rw [avQ_filter s f t L]
  exact this

/-- **The free row at one sign from its streams.** -/
theorem row_cap {S : CapSource} (hS : S.Admissible) (σ : Sign) {dP : ℕ} (hdP : 0 < dP)
    {D R O C : ℝ → ℝ} {Lq cr wl eD eF eT eR eA eE : ℝ} {AF AT : List QA} {cD cF cT cl r q : List ℤ}
    {K m lgs lgq : ℕ} {c : ℤ} {cap : ℝ} {dom : Set ℝ} (hdom : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1)
    (hdom2 : ∀ t ∈ dom, sgOf σ * t ≠ 0)
    (hOwn : ∀ t ∈ dom, avgL (S.gas σ) (rowK (sgOf σ * t)) ≤ D t + R t)
    (hOpp : ∀ t ∈ dom, avgL (S.gas (opp σ)) (rowK (sgOf σ * t)) ≤ Lq + O t)
    (hCol : ∀ t ∈ dom, -avgL (S.refCol 0) (colK (sgOf σ * t)) ≤ C t)
    (hRf : ∀ t ∈ dom, (2 - cr) * R t +
      (if σ = Sign.pos then S.reflPoly (sgOf σ * t) else 0) ≤ 0)
    (hAt : ∀ t ∈ dom, cr * R t + O t + C t + (11 / 29 - wl) * Real.log t +
      3 / 29 * Real.log (1 - sgOf σ * t) ≤ avQ false AF t + avQ true AT t)
    (hRad : ∀ t ∈ dom, S.radialA (Trunc.finite 384) σ (sgOf σ * t) -
      39 / 29 * Real.log (1 + t ^ 2) + wl * Real.log t ≤ rawSum cl 0 (2 * t - 1) / dP + eR)
    (hDir : Close dP D cD eD) (hF : Close dP (avQ false AF) cF eF)
    (hT : Close dP (avQ true AT) cT eT)
    (hAux : S.auxTail (Trunc.finite 384) σ ≤ eA)
    (hE : (if σ = Sign.pos then S.reflTail else 0) ≤ eE)
    (hs : (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) r).length = 2 * m + 1)
    (hq : q.length = m + 1) (hgs : 2 * m + 1 ≤ 2 ^ lgs) (hgq : m + 1 ≤ 2 ^ lgq)
    (hK : kronEq K m lgs lgq (dP : ℤ) c (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) r) q = true)
    (hb : 4 * (2 * (dP : ℤ) * l1 (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) r) +
      2 * l1 q * l1 q) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K)
    (hc : 8 * (2 * (dP : ℤ) * |c|) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K)
    (hfin : ((c : ℝ) - (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ))) / dP + (eD + eD) + eF + eT +
      eR + eA + eE + Lq - kappa σ ≤ cap) :
    ∀ t ∈ dom, S.rowField (Trunc.finite 384) σ Flavor.free (some 0) (sgOf σ * t) ≤ cap := by
  intro t ht
  have ht' := hdom t ht
  have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
  have hdZ : (0 : ℤ) < (dP : ℤ) := by exact_mod_cast hdP
  have hz : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have e0 := rowField_phys hS (Trunc.finite 384) σ (hdom2 t ht)
  have hAbs : |sgOf σ * t| = t := by
    rcases sgOf_cases σ with h | h <;> rw [h] <;> simp [abs_of_pos ht'.1]
  have hSq : (sgOf σ * t) ^ 2 = t ^ 2 := by
    rcases sgOf_cases σ with h | h <;> rw [h] <;> ring
  have hC := (((hDir.add hDir).add hF).add hT) t ht'
  set Pf := addZ (addZ (addZ (addZ cD cD) cF) cT) cl with hPf
  have hk := kron_le hdZ hs hq hgs hgq hK hb hc (2 * t - 1)
  rw [rawSum_addZ, hPf, rawSum_addZ] at hk
  have hrg := CatalanMeasure.GenD.Signed.RouteI.CompactCap.rawSum_ge r hz
  have a1 := abs_le.1 hC
  have o1 := hOwn t ht
  have o2 := hOpp t ht
  have o3 := hCol t ht
  have o4 := hRf t ht
  have o5 := hAt t ht
  have o6 := hRad t ht
  rw [e0]
  unfold rest
  rw [hAbs, hSq]
  have hk' : (rawSum (addZ (addZ (addZ cD cD) cF) cT) 0 (2 * t - 1) + rawSum cl 0 (2 * t - 1)) / dP +
      (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ)) / dP ≤ (c : ℝ) / dP := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hdr.le
  have hfin' := hfin
  rw [sub_div] at hfin'
  rw [add_div] at hk'
  have hsplit : (if σ = Sign.pos then S.reflPoly (sgOf σ * t) + S.reflTail else 0) =
      (if σ = Sign.pos then S.reflPoly (sgOf σ * t) else 0) + (if σ = Sign.pos then S.reflTail else 0) := by
    split_ifs <;> simp
  rw [hsplit]
  set W := (if σ = Sign.pos then S.reflPoly (sgOf σ * t) else 0)
  set Er := (if σ = Sign.pos then S.reflTail else 0)
  have hlt : 11 / 29 * Real.log t = (11 / 29 - wl) * Real.log t + wl * Real.log t := by ring
  rw [hlt]
  have ev : avQ false AF t + avQ true AT t + (D t + D t) ≤
      rawSum (addZ (addZ (addZ cD cD) cF) cT) 0 (2 * t - 1) / dP + (eD + eD + eF + eT) := by
    have := a1.2
    linarith
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory intervalIntegral
open scoped Interval
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.OrdHf (Cov Blk blkF sumF polK psiR bot mBlk sumEQ mc4)
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### Reflection against the reflection series -/

theorem phys_pint {l : List YCell} {P : List Seg} {f : ℝ → ℝ} (hl : ∀ c ∈ l, 2 ≤ c.lo)
    (hb : ∀ F : ℝ → ℝ, evC l F = evS P F) (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi)
    (hI : ∀ a b : ℝ, 2 ≤ a → a < b →
      IntervalIntegrable (fun y => f (YCell.physX y)) volume a b) :
    physL l f = pint P (fun y => f (YCell.physX y)) := by
  set h : ℝ → ℝ := fun y => f (YCell.physX y) with hh
  have h2 : ∀ b : ℝ, 2 ≤ b → IntervalIntegrable h volume 2 b := by
    intro b hb2
    rcases hb2.lt_or_eq with hlt | rfl
    · exact hI 2 b le_rfl hlt
    · exact IntervalIntegrable.refl
  have hd : ∀ a b : ℝ, 2 ≤ a → 2 ≤ b →
      (∫ u in (2 : ℝ)..b, h u) - (∫ u in (2 : ℝ)..a, h u) = ∫ u in a..b, h u :=
    fun a b ha hb' => intervalIntegral.integral_interval_sub_left (h2 b hb') (h2 a ha)
  have e1 : physL l f = evC l (fun y => ∫ u in (2 : ℝ)..y, h u) := by
    unfold physL evC
    congr 1
    refine List.map_congr_left fun c hc => ?_
    have hlo := hl c hc
    have := c.lo_lt
    rw [hd c.lo c.hi hlo (by linarith)]
    rfl
  rw [e1, hb]
  refine evS_congr fun g hg => ?_
  obtain ⟨a, b⟩ := hP g hg
  exact hd g.lo g.hi a (by linarith)

theorem refl_series (S : CapSource) {P : List Seg} (hl : ∀ c ∈ S.gas Sign.pos, 2 ≤ c.lo)
    (hb : ∀ F : ℝ → ℝ, evC (S.gas Sign.pos) F = evS P F)
    (hP : ∀ g ∈ P, 2 ≤ g.lo ∧ g.lo < g.hi) (hr : S.reflDeg = 899) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    pint P (fun y => Real.log |1 - YCell.physX y * t|) + S.reflPoly t ≤ 0 := by
  have e := phys_pint (f := fun s => Real.log |1 - s * t|) hl hb hP
    fun a b ha hab => rowlog_int ha hab h0 h1
  have b := OrdHf.physL_refl_le hl h0 h1 900
  have c : S.reflPoly t = ∑ k ∈ Finset.range 900, t ^ (k + 1) / ((k : ℝ) + 1) *
      physL (S.gas Sign.pos) (fun s => s ^ (k + 1)) := OrdHf.reflPoly_eq S hr t
  rw [← c, e] at b
  linarith

/-! ### The radial stream -/

theorem rawQ_scaled (dP : ℕ) : ∀ (L : List ℤ) (k : ℕ) (x : ℝ),
    rawQ (L.map fun d : ℤ => (d : ℚ) / dP) k x = rawSum L k x / dP
  | [], _, _ => by simp [rawQ]
  | a :: t, k, x => by
    simp only [List.map_cons, rawQ, rawSum_cons, rawQ_scaled dP t (k + 1) x]
    push_cast
    ring

theorem polK_abs_le (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) : ∀ (D : List ℤ) (k : ℕ),
    polK D k y ≤ ((l1 D : ℤ) : ℝ)
  | [], _ => by simp [polK, l1]
  | d :: t, k => by
    have ih := polK_abs_le y h0 h1 t (k + 1)
    simp only [polK, l1]
    push_cast
    have hp : y ^ (k + 1) ≤ 1 := pow_le_one₀ h0 h1
    have hp0 : 0 ≤ y ^ (k + 1) := pow_nonneg h0 _
    have : (d : ℝ) * y ^ (k + 1) ≤ |(d : ℝ)| := by
      calc (d : ℝ) * y ^ (k + 1) ≤ |(d : ℝ)| * y ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hp0
        _ ≤ |(d : ℝ)| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = _ := mul_one _
    linarith

/-- The constant bound of the blocks below all radii. -/
def smallQ (W : ℕ) : List Blk → ℚ
  | [] => 0
  | B :: t => (B.M * B.sg + (l1 B.D : ℚ) / 2 ^ W) + smallQ W t

theorem sumF_small (W : ℕ) {t : ℝ} (h0 : 0 < t) : ∀ Bs : List Blk,
    (∀ B ∈ Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg) → (∀ B ∈ Bs, t ≤ B.rho) →
    sumF W Bs t ≤ ((smallQ W Bs : ℚ) : ℝ)
  | [], _, _ => by simp [sumF, smallQ]
  | B :: Bs, h, h' => by
    have ih := sumF_small W h0 Bs (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (fun x hx => h' x (List.mem_cons_of_mem _ hx))
    obtain ⟨r0, m0, sl⟩ := h B List.mem_cons_self
    have ht := h' B List.mem_cons_self
    have r0' : (0 : ℝ) < B.rho := by exact_mod_cast r0
    have m0' : (0 : ℝ) ≤ B.M := by exact_mod_cast m0
    have e : sumF W (B :: Bs) t = blkF W B t + sumF W Bs t := by simp [sumF]
    rw [e]
    simp only [smallQ]
    push_cast
    have hb : blkF W B t ≤ (B.M : ℝ) * B.sg + ((l1 B.D : ℤ) : ℝ) / 2 ^ W := by
      unfold blkF psiR
      rw [max_eq_right ht, if_neg (not_lt.2 ht)]
      have p := polK_abs_le (t / B.rho) (by positivity) ((div_le_one r0').2 ht) B.D 0
      have q := mul_le_mul_of_nonneg_left sl m0'
      have : polK B.D 0 (t / B.rho) / 2 ^ W ≤ ((l1 B.D : ℤ) : ℝ) / 2 ^ W :=
        div_le_div_of_nonneg_right p (by positivity)
      linarith
    linarith

/-- **The radial bound from a chord cover.** The block `(x₀, sg, wl, [])` carries `wl log t`. -/
theorem rad_of_cov (C : Cov) {dP : ℕ} (hdP : 0 < dP) {cl : List ℤ} {B0 : List Blk} {x0 sgw wl : ℚ}
    (hBs : C.Bs = B0 ++ [⟨x0, sgw, wl, []⟩]) (hCs : C.s = 39 / 29) (hα : C.α = 2) (hβ : C.β = -1)
    (hCl : C.Cl = cl.map fun d : ℤ => (d : ℚ) / dP) {E K Bud : ℚ} (n : ℚ × ℚ) (ns : List (ℚ × ℚ))
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumEQ C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) (h0 : 0 < n.1)
    (hc : C.chain E K Bud n ns = true) (hn : (n :: ns).all C.nodeOK = true) (hlo : bot n ns = x0)
    (h1 : n.1 = 1) (hx : ∀ B ∈ C.Bs, x0 ≤ B.rho)
    (hsm : smallQ C.W C.Bs + (l1 cl : ℚ) / dP ≤ Bud) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    sumF C.W B0 t - 39 / 29 * Real.log (1 + t ^ 2) + (wl : ℝ) * Real.log t ≤
      rawSum cl 0 (2 * t - 1) / dP + (Bud : ℝ) := by
  have hdr : (0 : ℝ) < dP := by exact_mod_cast hdP
  have hz : 2 * t - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hPhi : C.Phi t ≤ Bud := by
    rcases le_total t (x0 : ℝ) with hs | hs
    · have a := sumF_small C.W ht0 C.Bs hB fun B hB' => hs.trans (by exact_mod_cast hx B hB')
      have b := abs_rawSum_le cl 0 hz
      have c : (0 : ℝ) ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
      have d : ((smallQ C.W C.Bs : ℚ) : ℝ) + ((l1 cl : ℤ) : ℝ) / dP ≤ Bud := by
        exact_mod_cast hsm
      unfold Cov.Phi
      rw [hCs, hα, hβ, hCl, rawQ_scaled]
      push_cast
      have e : (2 : ℝ) * t + -1 = 2 * t - 1 := by ring
      rw [e]
      have f : -(rawSum cl 0 (2 * t - 1) / dP) ≤ ((l1 cl : ℤ) : ℝ) / dP := by
        rw [← neg_div]
        exact div_le_div_of_nonneg_right (by linarith [(abs_le.1 b).1]) hdr.le
      nlinarith
    · exact OrdHf.Phi_of C n ns (by rw [hCs]; norm_num) (by rw [hα]; norm_num) hB hE hK h0 hc hn hlo
        h1 ⟨hs, ht1⟩
  have hx0 : (0 : ℝ) ≤ wl := by
    have := (hB ⟨x0, sgw, wl, []⟩ (by rw [hBs]; simp)).2.1
    exact_mod_cast this
  unfold Cov.Phi at hPhi
  rw [hBs, OrdHf.sumF_snoc, hCs, hα, hβ, hCl, rawQ_scaled] at hPhi
  push_cast at hPhi
  have e : (2 : ℝ) * t + -1 = 2 * t - 1 := by ring
  rw [e] at hPhi
  have hw : (wl : ℝ) * Real.log t ≤ blkF C.W ⟨x0, sgw, wl, []⟩ t := by
    unfold blkF
    simp only [polK, zero_div, add_zero]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log ht0 (le_max_left _ _)) hx0
  linarith

theorem radP_le {R : OrdHf.RadLit}
    (hR : OrdHf.RadOK R capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16)
    (hs : R.s = 1) {u : ℝ} (hu : 0 < u) :
    capSource.radialA (Trunc.finite 384) Sign.pos u ≤
      sumF R.W R.Bs u + ((OrdHf.errS R 16 : ℚ) : ℝ) :=
  OrdHf.radial_pos hR hs (OrdHf.capAux Sign.pos) (fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show e ∈ (auxT Sign.pos).map _ from he)
    exact mkAux_rad_lt _ _ t (pa_ok t ht).2) hu

/-- The rational error of the negative radial field. -/
def errN (R : OrdHf.RadLit) (Tm : ℤ) : ℚ :=
  OrdHf.errS R 16 + ((Tm : ℚ) / 2 ^ 160 + 384 * (OrdHf.mirE R 1 16 + 1 / 2 ^ R.W))

theorem radN_le {R : OrdHf.RadLit}
    (hR : OrdHf.RadOK R capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16)
    (hs : R.s = -1) {rns : List ℕ} {rb nm : ℕ} (hn : OrdHf.rnOK R rns rb = true)
    (hf : OrdHf.fbOK R = true) {Dm : List ℤ} (hDm : Dm = OrdHf.truncD R.sh nm (OrdHf.mirF R rns rb 16))
    {Tm : ℤ} (hTm : OrdHf.abs1 ((OrdHf.mirF R rns rb 16).drop nm) = Tm) {u : ℝ} (hu : 0 < u)
    (hu1 : u ≤ 1) :
    capSource.radialA (Trunc.finite 384) Sign.neg (-u) ≤
      sumF R.W (R.Bs ++ [mBlk Dm]) u + ((errN R Tm : ℚ) : ℝ) := by
  have hrn : ∀ i < 16, ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧
      (R.B i).rho ≤ 1 := fun i hi => OrdHf.hrn_of hn hi
  have rd := OrdHf.radial_neg hR hs (OrdHf.capAux Sign.neg) (fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show e ∈ (auxT Sign.neg).map _ from he)
    exact mkAux_rad_lt _ _ t (na_ok t ht).2) rns rb nm (Fb := 1) zero_le_one hrn
    (fun i hi => (hR.hrad i hi).2.1.trans (by exact_mod_cast (hrn i hi).2))
    (fun i hi d hd => OrdHf.hb_of hf hi hd) hu hu1
  rw [← hDm, hTm] at rd
  rw [OrdHf.sumF_snoc, OrdHf.blkF_mBlk _ _ hu1]
  unfold errN
  push_cast at rd ⊢
  linarith

theorem auxP_le : capSource.auxTail (Trunc.finite 384) Sign.pos ≤
    ((OrdHf.Enc.tail (1 - OrdHf.massQ OrdHf.gP.T OrdHf.gP.L) 1 : ℚ) : ℝ) :=
  OrdHf.auxTail_le OrdHf.enc_valid OrdHf.enc_q1 Sign.pos (by rw [auxMass_eq, OrdHf.tgtP])
    (by rw [auxMass_eq]; exact tgt_nonneg _) (by simp)

theorem auxN_le : capSource.auxTail (Trunc.finite 384) Sign.neg ≤
    ((OrdHf.Enc.tail (53 / 58 - OrdHf.massQ OrdHf.gN.T OrdHf.gN.L) 2 : ℚ) : ℝ) :=
  OrdHf.auxTail_le OrdHf.enc_valid OrdHf.enc_q1 Sign.neg (by rw [auxMass_eq, OrdHf.tgtN])
    (by rw [auxMass_eq]; exact tgt_nonneg _) (by simp)

theorem eref_cap : capSource.reflTail ≤ (1 / 900 + 1 / 901) / 901 * ((OrdHf.EvP : ℝ) / 2 ^ 64) := by
  have hF := OrdHf.relP_spec OrdHf.pTg gasPosT OrdHf.gP.L OrdHf.pRel
  have := OrdHf.eref_le OrdHf.pP64 OrdHf.pT0 hF
  rw [OrdHf.pE] at this
  rw [OrdHf.reflTail_eq capSource rfl]
  exact this

/-! ### Bindings -/

/-- All weights cancel between two atom lists. -/
def cancelB (n : ℕ) (A B : List Ev) : Bool :=
  (mergeA n A (negEv B)).all fun e => decide (e.2 = 0)

theorem evQ_zero : ∀ E : List Ev, (E.all fun e => decide (e.2 = 0)) = true → ∀ F : ℝ → ℝ,
    evQ E F = 0
  | [], _, _ => by simp
  | e :: E, h, F => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [evQ_cons, evQ_zero E h.2 F, h.1]
    simp

theorem cancelB_eq {n : ℕ} {A B : List Ev} (h : cancelB n A B = true) (F : ℝ → ℝ) :
    evQ A F = evQ B F := by
  have := evQ_zero _ h F
  rw [evQ_mergeA, evQ_negEv] at this
  linarith

/-- The atoms of a list of segments. -/
def segEv : List GS → List Ev
  | [] => []
  | g :: G => (g.1, g.2.2) :: (g.2.1, -g.2.2) :: segEv G

theorem evS_segEv : ∀ (G : List GS) (F : ℝ → ℝ), evS (G.map segR) F = -evQ (segEv G) F
  | [], F => by simp [evS, segEv]
  | g :: G, F => by
    rw [List.map_cons, evS_cons, evS_segEv G F]
    simp only [segEv, evQ_cons, segR]
    push_cast
    ring

theorem evC_cellEv (m : ℚ) (T : ℤ) (hm : 0 ≤ m) (hT : 0 < T) {L : List Tr}
    (hv : ∀ t ∈ L, t.1 < t.2.1 ∧ 0 ≤ t.2.2) (F : ℝ → ℝ) :
    evC (L.map (mkCell (m : ℝ) T)) F = -evQ (cellEv m T L) F := by
  unfold cellEv
  rw [evQ_mergeA, evC_cells m T hm hT L hv]

/-- Positive side: a cell list against the segments `G`. -/
theorem bind_pos {l : List YCell} {A : List Ev} {G : List GS} {n : ℕ}
    (hl : ∀ F : ℝ → ℝ, evC l F = -evQ A F) (hc : cancelB n A (segEv G) = true) (F : ℝ → ℝ) :
    evC l F = evS (G.map segR) (fun y => 1 * F (1 * y)) := by
  rw [hl, evS_segEv, cancelB_eq hc]
  simp only [one_mul]

/-- Negative side: a cell list against the mirror of the segments `G`. -/
theorem bind_neg {l : List YCell} {A : List Ev} {G : List GS} {n : ℕ}
    (hl : ∀ F : ℝ → ℝ, evC l F = -evQ A F) (hc : cancelB n A (mirror (segEv G)) = true) (F : ℝ → ℝ) :
    evC l F = evS (G.map segR) (fun y => -1 * F (-1 * y)) := by
  rw [hl, evS_segEv, cancelB_eq hc, evQ_mirror]
  have : evQ (segEv G) (fun y => -1 * F (-1 * y)) = -evQ (segEv G) (fun y => F (-y)) := by
    rw [← evQ_fun_neg]
    exact evQ_congr fun y => by simp
  rw [this]

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set MeasureTheory intervalIntegral
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.OrdHf (Cov Blk blkF sumF polK psiR bot mBlk sumEQ mc4)
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### The logarithm atoms -/

theorem log_t_atom {c q : ℚ} (hc : 0 ≤ c) (h0r : 0 ≤ rQ q) (h1r : rQ q ≤ 1) {t : ℝ} (h0 : 0 < t)
    (h1 : t ≤ 1) : (c : ℝ) * Real.log t ≤ avQ true [(c, -q, 0)] t := by
  rw [avQ_cons, avQ_nil]
  simp only [av, if_true]
  have e : -qOf (-q, 0) = ((q : ℝ) : ℂ) := by
    rw [qOf_real]
    push_cast
    simp
  rw [e, add_zero]
  have r0 : (0 : ℝ) ≤ ((rQ q : ℚ) : ℝ) := by exact_mod_cast h0r
  have r1 : ((rQ q : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1r
  exact mul_le_mul_of_nonneg_left (log_le_flip h0 h1 (rQ_real q) r0 r1) (by exact_mod_cast hc)

theorem log_sub_atom {c q : ℚ} (hc : 0 ≤ c) (h0r : 0 ≤ rQ q) (h1r : rQ q ≤ 1) {t : ℝ} (h0 : 0 < t)
    (h1 : t < 1) : (c : ℝ) * Real.log (1 - t) ≤ avQ false [(c, q, 0)] t := by
  rw [avQ_cons, avQ_nil]
  simp only [av, Bool.false_eq_true, ite_false]
  rw [qOf_real, add_zero]
  have r0 : (0 : ℝ) ≤ ((rQ q : ℚ) : ℝ) := by exact_mod_cast h0r
  have r1 : ((rQ q : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1r
  exact mul_le_mul_of_nonneg_left (log_one_sub_le h0 h1 (rQ_real q) r0 r1) (by exact_mod_cast hc)

theorem log_add_atom {c q : ℚ} (hc : 0 ≤ c) (h1r : rQ q ≤ -1) {t : ℝ} (h0 : 0 < t) :
    (c : ℝ) * Real.log (1 + t) ≤ avQ false [(c, q, 0)] t := by
  rw [avQ_cons, avQ_nil]
  simp only [av, Bool.false_eq_true, ite_false]
  rw [qOf_real, add_zero]
  have r1 : ((rQ q : ℚ) : ℝ) ≤ -1 := by exact_mod_cast h1r
  exact mul_le_mul_of_nonneg_left (log_one_add_le h0 (rQ_real q) r1) (by exact_mod_cast hc)

/-! ### Bindings of `capSource` -/

theorem gasPos_ev (F : ℝ → ℝ) :
    evC (capSource.gas Sign.pos) F = -evQ (cellEv 1 (sumP row0) gasPosT) F := by
  have := evC_cellEv 1 (sumP row0) zero_le_one row0_tot (L := gasPosT)
    (fun t ht => row0_ok t (List.mem_filter.1 ht).1) F
  rw [Rat.cast_one] at this
  exact this

theorem gasNeg_ev (F : ℝ → ℝ) :
    evC (capSource.gas Sign.neg) F = -evQ (cellEv 1 (sumP row0) gasNegT) F := by
  have := evC_cellEv 1 (sumP row0) zero_le_one row0_tot (L := gasNegT)
    (fun t ht => row0_ok t (List.mem_filter.1 ht).1) F
  rw [Rat.cast_one] at this
  exact this

theorem col_ev (F : ℝ → ℝ) :
    evC (capSource.refCol 0) F = -evQ (cellEv 1 (sumP col0) col0) F := by
  rw [refCol_zero]
  exact evC_cellEv 1 (sumP col0) zero_le_one col0_tot col0_ok F

theorem gas_sides (σ : Sign) : ∀ c ∈ capSource.gas σ, 2 ≤ c.lo ∨ c.hi ≤ -2 := by
  intro c hc
  cases σ
  · exact Or.inr (gas_neg_hi c hc)
  · exact Or.inl (gas_pos_lo c hc)

/-! ### The certificate of one sign -/

/-- The finite data of a free row at one sign, on the domain `dom` of `t = |x|`. The own gas is
`Go ++ Gs` with `Gs` of nonnegative density; the direct potential is taken on `Go` alone. -/
structure RowCert (σ : Sign) (dom : Set ℝ) (cap : ℝ) where
  dP : ℕ
  hdP : 0 < dP
  hdom : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1
  cr : ℚ
  hcr : 0 ≤ cr
  wl : ℚ
  Go : List GS
  Gs : List GS
  Gq : List GS
  Gc : List GS
  qR : List ℚ
  qO : List (ℚ × ℚ)
  q0 : ℚ × ℚ
  qC : List (ℚ × ℚ)
  LF : List QA
  LT : List QA
  cD : List ℤ
  cF : List ℤ
  cT : List ℤ
  cl : List ℤ
  r : List ℤ
  q : List ℤ
  K : ℕ
  m : ℕ
  lgs : ℕ
  lgq : ℕ
  c : ℤ
  Lq : ℝ
  eD : ℝ
  eF : ℝ
  eT : ℝ
  eR : ℝ
  eA : ℝ
  eE : ℝ
  bindO : ∀ F : ℝ → ℝ, evC (capSource.gas σ) F =
    evS ((Go ++ Gs).map segR) (fun y => sgOf σ * F (sgOf σ * y))
  bindQ : ∀ F : ℝ → ℝ, evC (capSource.gas (opp σ)) F =
    evS (Gq.map segR) (fun y => -sgOf σ * F (-sgOf σ * y))
  bindC : ∀ F : ℝ → ℝ, evC (capSource.refCol 0) F =
    evS (Gc.map segR) (fun y => sgOf σ * F (sgOf σ * y))
  keyO : ∀ g ∈ (Go ++ Gs).map segR, 2 ≤ g.lo ∧ g.lo < g.hi
  keyQ : ∀ g ∈ Gq.map segR, 2 ≤ g.lo ∧ g.lo < g.hi
  posS : ∀ g ∈ Gs.map segR, 0 ≤ g.rho
  chkR : reflB (Go ++ Gs) qR = true
  chkO : oppB Gq qO = true
  chkC : colB Gc (q0 :: qC) = true
  hLq : pint (Gq.map segR) (fun y => Real.log (YCell.physX y)) ≤ Lq
  hRf : ∀ t ∈ dom, (2 - (cr : ℝ)) * pint ((Go ++ Gs).map segR)
      (fun y => Real.log |1 - YCell.physX y * t|) +
    (if σ = Sign.pos then capSource.reflPoly (sgOf σ * t) else 0) ≤ 0
  hLog : ∀ t ∈ dom, (11 / 29 - (wl : ℝ)) * Real.log t + 3 / 29 * Real.log (1 - sgOf σ * t) ≤
    avQ false LF t + avQ true LT t
  hRad : ∀ t ∈ dom, capSource.radialA (Trunc.finite 384) σ (sgOf σ * t) -
      39 / 29 * Real.log (1 + t ^ 2) + (wl : ℝ) * Real.log t ≤
    rawSum cl 0 (2 * t - 1) / dP + eR
  hDir : Close dP (fun t => pint (Go.map segR) fun y => Real.log |t - YCell.physX y|) cD eD
  hF : Close dP (avQ false (reflL cr (Go ++ Gs) qR ++ oppL Gq qO ++ colL 0 Gc (q0 :: qC) ++ LF))
    cF eF
  hT : Close dP (avQ true LT) cT eT
  hAux : capSource.auxTail (Trunc.finite 384) σ ≤ eA
  hE : (if σ = Sign.pos then capSource.reflTail else 0) ≤ eE
  hs : (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) r).length = 2 * m + 1
  hq : q.length = m + 1
  hgs : 2 * m + 1 ≤ 2 ^ lgs
  hgq : m + 1 ≤ 2 ^ lgq
  hK : kronEq K m lgs lgq (dP : ℤ) c (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) r) q = true
  hb : 4 * (2 * (dP : ℤ) * l1 (addZ (addZ (addZ (addZ (addZ cD cD) cF) cT) cl) r) +
    2 * l1 q * l1 q) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K
  hc : 8 * (2 * (dP : ℤ) * |c|) < CatalanMeasure.GenD.Signed.Davis.CircleCheb.pow2 K
  hfin : ((c : ℝ) - (((r.headD 0 : ℤ) : ℝ) - ((l1 r.tail : ℤ) : ℝ))) / dP + (eD + eD) + eF + eT +
    eR + eA + eE + Lq - kappa σ ≤ cap

/-- A row certificate bounds the finite row field at that sign. -/
theorem RowCert.le {σ : Sign} {dom : Set ℝ} {cap : ℝ} (R : RowCert σ dom cap) :
    ∀ t ∈ dom, capSource.rowField (Trunc.finite 384) σ Flavor.free (some 0) (sgOf σ * t) ≤ cap := by
  have hsg := sgOf_cases σ
  have hneg : ∀ t ∈ dom, sgOf σ * t ≠ 0 := by
    intro t ht
    have := (R.hdom t ht).1
    rcases hsg with h | h <;> rw [h] <;> simp [this.ne']
  have hbO := R.bindO
  rw [List.map_append] at hbO
  have hkO := R.keyO
  rw [List.map_append] at hkO
  refine row_cap capSource_admissible σ R.hdP R.hdom hneg
    (D := fun t => pint (R.Go.map segR) fun y => Real.log |t - YCell.physX y|)
    (R := fun t => pint ((R.Go ++ R.Gs).map segR) fun y => Real.log |1 - YCell.physX y * t|)
    (O := fun t => pint (R.Gq.map segR) fun y => Real.log (1 + y * t + t ^ 2))
    (C := fun t => -pint (R.Gc.map segR) (colK t)) (Lq := R.Lq) (cr := R.cr) (wl := R.wl)
    (AF := reflL R.cr (R.Go ++ R.Gs) R.qR ++ oppL R.Gq R.qO ++ colL 0 R.Gc (R.q0 :: R.qC) ++ R.LF)
    (AT := R.LT) ?_ ?_ ?_ R.hRf ?_ R.hRad R.hDir R.hF R.hT R.hAux R.hE R.hs R.hq R.hgs R.hgq R.hK
    R.hb R.hc R.hfin
  · intro t ht
    obtain ⟨h0, h1⟩ := R.hdom t ht
    have := own_part hsg (gas_sides σ) hbO hkO R.posS h0 h1
    rw [← List.map_append] at this
    exact this
  · intro t ht
    obtain ⟨h0, _⟩ := R.hdom t ht
    have hl : ∀ c ∈ capSource.gas (opp σ), 2 ≤ c.lo ∨ c.hi ≤ -2 := gas_sides _
    rw [opp_part hsg hl R.bindQ R.keyQ h0]
    linarith [R.hLq]
  · intro t ht
    obtain ⟨h0, _⟩ := R.hdom t ht
    rw [avg_col hsg R.bindC h0]
  · intro t ht
    obtain ⟨h0, h1⟩ := R.hdom t ht
    have a := refl_bound R.cr R.hcr h0 h1 _ _ R.chkR
    have b := opp_bound h0 h1 _ _ R.chkO
    have c := col_bound h0 h1 _ _ _ 0 R.chkC
    have d := R.hLog t ht
    simp only [avQ_append]
    simp only [Rat.cast_zero, mul_zero, zero_mul, add_zero] at c
    linarith

/-- **The free row from the two certificates.** -/
theorem freeRowCap0_of_checks
    (P : RowCert Sign.pos (Ioo (0 : ℝ) 1) (-2579777 / 1000000))
    (N : RowCert Sign.neg (Ioc (0 : ℝ) 1) (-2579777 / 1000000)) :
    capSource.FreeRowCap Trunc.exact 0 (-2579777 / 1000000) := by
  intro x hx
  obtain ⟨he, h0, h1⟩ := x_eq_sg_abs (σ := signOf x) hx rfl
  have hle := CompactSource.rowField_exact_le capSource capSource_admissible 384 (signOf x) Flavor.free
    (some 0) h1
  show capSource.rowField Trunc.exact (signOf x) Flavor.free (some 0) x ≤ _
  refine hle.trans ?_
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · have hs : signOf x = Sign.neg := by simp [signOf, b]
    rw [hs] at he ⊢
    have := N.le |x| ⟨h0, h1⟩
    rwa [← he] at this
  · have hs : signOf x = Sign.pos := by simp [signOf, not_lt.2 a.le]
    rw [hs] at he ⊢
    have := P.le |x| ⟨h0, by rw [abs_of_pos a]; exact b⟩
    rwa [← he] at this

/-- The reflection hypothesis of the positive sign with factor one. -/
theorem hRf_pos {Go Gs : List GS} (hb : ∀ F : ℝ → ℝ, evC (capSource.gas Sign.pos) F =
      evS ((Go ++ Gs).map segR) (fun y => sgOf Sign.pos * F (sgOf Sign.pos * y)))
    (hk : ∀ g ∈ (Go ++ Gs).map segR, 2 ≤ g.lo ∧ g.lo < g.hi) :
    ∀ t ∈ Ioo (0 : ℝ) 1, (2 - ((1 : ℚ) : ℝ)) * pint ((Go ++ Gs).map segR)
      (fun y => Real.log |1 - YCell.physX y * t|) +
      (if Sign.pos = Sign.pos then capSource.reflPoly (sgOf Sign.pos * t) else 0) ≤ 0 := by
  intro t ht
  have := refl_series capSource gas_pos_lo (P := (Go ++ Gs).map segR)
    (fun F => by simpa [sgOf] using hb F) hk rfl ht.1 ht.2.le
  simp only [ite_true, sgOf, one_mul, Rat.cast_one]
  linarith

/-- The reflection hypothesis of the negative sign is empty at factor two. -/
theorem hRf_neg (G : List GS) : ∀ t ∈ Ioc (0 : ℝ) 1, (2 - ((2 : ℚ) : ℝ)) * pint (G.map segR)
      (fun y => Real.log |1 - YCell.physX y * t|) +
      (if Sign.neg = Sign.pos then capSource.reflPoly (sgOf Sign.neg * t) else 0) ≤ 0 := by
  intro t _
  simp

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.OrdHf (Cov Blk blkF sumF polK psiR bot mBlk sumEQ mc4)
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### Leaves: chains, tails, radial and constants -/

/-- Atoms of nonzero weight. -/
def nzF (e : Ev) : Bool := !decide (e.2 = 0)

/-- Dropping zero-weight atoms keeps a profile identity. -/
theorem evQ_filter_nz (F : ℝ → ℝ) : ∀ E : List Ev, evQ (E.filter nzF) F = evQ E F
  | [] => by simp
  | e :: E => by
    have ih := evQ_filter_nz F E
    by_cases h : e.2 = 0
    · have : nzF e = false := by simp [nzF, h]
      rw [List.filter_cons_of_neg (by simp [this]), ih, evQ_cons, h]
      simp
    · have : nzF e = true := by simp [nzF, h]
      rw [List.filter_cons_of_pos this, evQ_cons, evQ_cons, ih]

theorem atoms_nz {P : List Seg} {E : List Ev} (h : Atoms P (E.map atomR)) :
    Atoms P ((E.filter nzF).map atomR) := by
  intro F
  rw [h F, evE_atomR, evE_atomR, evQ_filter_nz]

/-- Binding of a cell list to a chain, positive side. -/
theorem bind_chain_pos {l : List YCell} {A E : List Ev} {n : ℕ}
    (hl : ∀ F : ℝ → ℝ, evC l F = -evQ A F) (hs : sumW E = 0) (hc : cancelB n A E = true)
    (F : ℝ → ℝ) : evC l F = evS ((chainQ 0 E).map segR) (fun y => 1 * F (1 * y)) := by
  have := atoms_of_chain E hs (fun y => 1 * F (1 * y))
  rw [evE_atomR] at this
  rw [hl, this, cancelB_eq hc]
  simp only [one_mul]

/-- Binding of a cell list to a chain, negative side. -/
theorem bind_chain_neg {l : List YCell} {A E : List Ev} {n : ℕ}
    (hl : ∀ F : ℝ → ℝ, evC l F = -evQ A F) (hs : sumW E = 0)
    (hc : cancelB n A (mirror E) = true) (F : ℝ → ℝ) :
    evC l F = evS ((chainQ 0 E).map segR) (fun y => -1 * F (-1 * y)) := by
  have := atoms_of_chain E hs (fun y => -1 * F (-1 * y))
  rw [evE_atomR] at this
  rw [hl, this, cancelB_eq hc, evQ_mirror]
  have e : evQ E (fun y => -1 * F (-1 * y)) = -evQ E (fun y => F (-y)) := by
    rw [← evQ_fun_neg]
    exact evQ_congr fun y => by simp
  rw [e]

/-- The packed sum of a split entry list. -/
theorem run_append (p : EPar) (A B : List Ent) (acc : ℤ) :
    run p (A ++ B) acc = run p B (run p A acc) := by
  induction A generalizing acc with
  | nil => rfl
  | cons e A ih => simp only [List.cons_append, run, forceI_eq, ih]

theorem Close.mono {dP : ℕ} {f : ℝ → ℝ} {c : List ℤ} {e e' : ℝ} (h : Close dP f c e) (he : e ≤ e') :
    Close dP f c e' := fun t ht => (h t ht).trans he

/-- Chunks of an atom list add. -/
theorem Close.append (s : Bool) {dP : ℕ} {A B : List QA} {a b : List ℤ} {e1 e2 : ℝ}
    (h1 : Close dP (avQ s A) a e1) (h2 : Close dP (avQ s B) b e2) :
    Close dP (avQ s (A ++ B)) (addZ a b) (e1 + e2) := by
  intro t ht
  have := (h1.add h2) t ht
  rw [avQ_append]
  exact this

/-- The tail of an atom list below a common modulus. -/
theorem atail_le {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (M : ℕ) : ∀ A : List QA,
    (∀ a ∈ A, a.2.1 ^ 2 + a.2.2 ^ 2 ≤ ρ ^ 2) →
    atail (A.map aR) M ≤ (((A.map fun a => |a.1|).sum : ℚ) : ℝ) *
      (4 * ((ρ : ℝ) ^ (M + 1) * (1 - (ρ : ℝ))⁻¹ / ((M : ℝ) + 1)))
  | [], _ => by simp [atail]
  | a :: A, h => by
    have ih := atail_le h0 h1 M A fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hq := h a List.mem_cons_self
    have r0 : (0 : ℝ) ≤ ρ := by exact_mod_cast h0
    have r1 : (ρ : ℝ) < 1 := by exact_mod_cast h1
    have hn : ‖qOf a.2‖ ≤ ρ := by
      have e : ‖qOf a.2‖ ^ 2 = (a.2.1 : ℝ) ^ 2 + (a.2.2 : ℝ) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [qOf]
        ring
      have hq' : (a.2.1 : ℝ) ^ 2 + (a.2.2 : ℝ) ^ 2 ≤ (ρ : ℝ) ^ 2 := by exact_mod_cast hq
      exact abs_le_of_sq_le_sq' (by rw [e]; exact hq') r0 |>.2 |> fun h => by
        simpa [abs_of_nonneg (norm_nonneg _)] using h
    have hg : 0 < 1 - (ρ : ℝ) := by linarith
    have hg' : 0 < 1 - ‖qOf a.2‖ := by linarith
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have t1 : ‖qOf a.2‖ ^ (M + 1) * (1 - ‖qOf a.2‖)⁻¹ / ((M : ℝ) + 1) ≤
        (ρ : ℝ) ^ (M + 1) * (1 - (ρ : ℝ))⁻¹ / ((M : ℝ) + 1) := by
      refine div_le_div_of_nonneg_right ?_ hM.le
      refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn _) ?_ (by positivity) (by positivity)
      exact inv_anti₀ hg (by linarith)
    have t2 : |(a.1 : ℝ)| * (4 * (‖qOf a.2‖ ^ (M + 1) * (1 - ‖qOf a.2‖)⁻¹ / ((M : ℝ) + 1))) ≤
        |(a.1 : ℝ)| * (4 * ((ρ : ℝ) ^ (M + 1) * (1 - (ρ : ℝ))⁻¹ / ((M : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    simp only [atail, List.map_cons, List.sum_cons, aR] at ih ⊢
    rw [Rat.cast_add, Rat.cast_abs, add_mul]
    linarith

/-- The radial field of the positive sign through a cover. -/
theorem hRad_pos {R : OrdHf.RadLit}
    (hR : OrdHf.RadOK R capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16)
    (hRs : R.s = 1) (C : Cov) {dP : ℕ} (hdP : 0 < dP) {cl : List ℤ} {x0 sgw wl : ℚ}
    (hW : C.W = R.W) (hBs : C.Bs = R.Bs ++ [⟨x0, sgw, wl, []⟩])
    (hCs : C.s = 39 / 29) (hα : C.α = 2) (hβ : C.β = -1)
    (hCl : C.Cl = cl.map fun d : ℤ => (d : ℚ) / dP) {E K Bud : ℚ} (n : ℚ × ℚ) (ns : List (ℚ × ℚ))
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumEQ C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) (h0 : 0 < n.1)
    (hc : C.chain E K Bud n ns = true) (hn : (n :: ns).all C.nodeOK = true) (hlo : bot n ns = x0)
    (h1 : n.1 = 1) (hx : ∀ B ∈ C.Bs, x0 ≤ B.rho)
    (hsm : smallQ C.W C.Bs + (l1 cl : ℚ) / dP ≤ Bud) {dom : Set ℝ}
    (hd : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1) :
    ∀ t ∈ dom, capSource.radialA (Trunc.finite 384) Sign.pos (sgOf Sign.pos * t) -
        39 / 29 * Real.log (1 + t ^ 2) + (wl : ℝ) * Real.log t ≤
      rawSum cl 0 (2 * t - 1) / dP + ((Bud : ℝ) + ((OrdHf.errS R 16 : ℚ) : ℝ)) := by
  intro t ht
  obtain ⟨t0, t1⟩ := hd t ht
  have a := rad_of_cov C hdP hBs hCs hα hβ hCl n ns hB hE hK h0 hc hn hlo h1 hx hsm t0 t1
  have b := radP_le hR hRs t0
  rw [hW] at a
  simp only [sgOf, one_mul]
  linarith

/-- The radial field of the negative sign through a cover. -/
theorem hRad_neg {R : OrdHf.RadLit}
    (hR : OrdHf.RadOK R capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16)
    (hRs : R.s = -1) {rns : List ℕ} {rb nm : ℕ} (hrn : OrdHf.rnOK R rns rb = true)
    (hf : OrdHf.fbOK R = true) {Dm : List ℤ} (hDm : Dm = OrdHf.truncD R.sh nm (OrdHf.mirF R rns rb 16))
    {Tm : ℤ} (hTm : OrdHf.abs1 ((OrdHf.mirF R rns rb 16).drop nm) = Tm)
    (C : Cov) {dP : ℕ} (hdP : 0 < dP) {cl : List ℤ} {x0 sgw wl : ℚ}
    (hW : C.W = R.W) (hBs : C.Bs = (R.Bs ++ [mBlk Dm]) ++ [⟨x0, sgw, wl, []⟩])
    (hCs : C.s = 39 / 29) (hα : C.α = 2) (hβ : C.β = -1)
    (hCl : C.Cl = cl.map fun d : ℤ => (d : ℚ) / dP) {E K Bud : ℚ} (n : ℚ × ℚ) (ns : List (ℚ × ℚ))
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumEQ C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) (h0 : 0 < n.1)
    (hc : C.chain E K Bud n ns = true) (hn : (n :: ns).all C.nodeOK = true) (hlo : bot n ns = x0)
    (h1 : n.1 = 1) (hx : ∀ B ∈ C.Bs, x0 ≤ B.rho)
    (hsm : smallQ C.W C.Bs + (l1 cl : ℚ) / dP ≤ Bud) {dom : Set ℝ}
    (hd : ∀ t ∈ dom, t ∈ Ioc (0 : ℝ) 1) :
    ∀ t ∈ dom, capSource.radialA (Trunc.finite 384) Sign.neg (sgOf Sign.neg * t) -
        39 / 29 * Real.log (1 + t ^ 2) + (wl : ℝ) * Real.log t ≤
      rawSum cl 0 (2 * t - 1) / dP + ((Bud : ℝ) + ((errN R Tm : ℚ) : ℝ)) := by
  intro t ht
  obtain ⟨t0, t1⟩ := hd t ht
  have a := rad_of_cov C hdP hBs hCs hα hβ hCl n ns hB hE hK h0 hc hn hlo h1 hx hsm t0 t1
  have b := radN_le hR hRs hrn hf hDm hTm t0 t1
  rw [hW] at a
  have e : sgOf Sign.neg * t = -t := by simp [sgOf]
  rw [e]
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

namespace CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail

/-! ### One real unit

The anchor-0 column of `capSource` at the positive sign: its chain with four panels on the cells
beyond `4/5`, the node check of all 1508 atoms, and the first 200 atoms through the moment engine
at degree 511. kcost: 1508 node checks, 200 entries of 48 complex products. -/

def cutsU : List ℤ := raw_ints% [799113636363, 800045454545, 800977272727, 802840909090, 803772727272, 804704545454, 806568181818, 807500000000, 808431818182, 810295454545, 811227272727, 812159090909, 814022727272, 814954545454, 815886363636, 817749999999, 818681818181, 819613636363, 821477272727, 822409090909, 823340909091, 825204545454, 826136363636, 827068181818, 828931818181, 829863636363, 830795454545, 832659090909, 833590909091, 834522727273, 836386363636, 837318181818, 838250000000, 840113636363, 841045454545, 841977272727, 843840909090, 844772727272, 845704545454, 847568181818, 848500000000, 849431818182, 851295454545, 852227272727, 853159090909, 855022727272, 855954545454, 856886363636, 858749999999, 859681818181, 860613636363, 862477272727, 863409090909, 864340909091, 866204545454, 867136363636, 868068181818, 869931818181, 870863636363, 871795454545, 873659090909, 874590909091, 875522727273, 877386363636, 878318181818, 879250000000, 881113636363, 882045454545, 882977272727, 884840909090, 885772727272, 886704545454, 888568181818, 889500000000, 890431818182, 892272727273, 893181818182, 894090909091, 895022727272, 895045454545, 895068181818, 895232360922, 895373812754, 895515264586, 895820895522, 895985074627, 896149253731, 896477611940, 896641791045, 896805970149, 897134328358, 897298507463, 897462686567, 897791044776, 897955223881, 898119402985, 898417232022, 898550881954, 898684531886, 898848710990, 898879240162, 898909769334, 899104477611, 899268656716, 899432835820, 899761194029, 899925373134, 900089552238, 900417910447, 900582089552, 900746268656, 901074626865, 901238805970, 901402985074, 901731343283, 901895522388, 902059701492, 902304274084, 902384667571, 902465061058, 902629240162, 902713025780, 902796811397, 903044776119, 903208955224, 903373134328, 903701492537, 903865671642, 904029850746, 904358208955, 904522388060, 904686567164, 905014925373, 905179104478, 905343283582, 905671641791, 905835820895, 905999999999, 906191316146, 906218453188, 906245590230, 906409769335, 906546811397, 906683853459, 906985074626, 907149253731, 907313432835, 907641791044, 907805970149, 907970149253, 908298507462, 908462686567, 908626865671, 908955223880, 909119402985, 909283582089, 909585820895, 909723880597, 909861940298, 910026119403, 910052238806, 910078358209, 910268656716, 910432835821, 910597014925, 910925373134, 911089552239, 911253731343, 911582089552, 911746268657, 911910447761, 912238805970, 912402985075, 912567164179, 912895522388, 913059701492, 913223880596, 913552238805, 913716417910, 913880597014, 914208955223, 914373134328, 914537313432, 914865671641, 915029850746, 915194029850, 915522388059, 915686567164, 915850746268, 916179104477, 916343283582, 916507462686, 916835820895, 917000000000, 917164179104, 917492537313, 917656716418, 917820895522, 918149253731, 918313432836, 918477611940, 918805970149, 918970149254, 919134328358, 919462686567, 919626865672, 919791044776, 920068925845, 920182627809, 920296329773, 920460508877, 920510986018, 920561463158, 920776119403, 920940298507, 921104477611, 921432835820, 921597014925, 921761194029, 922089552238, 922253731343, 922417910447, 922746268656, 922910447761, 923074626865, 923402985074, 923567164179, 923731343283, 924059701492, 924223880597, 924388059701, 924716417910, 924880597015, 925044776119, 925373134328, 925537313433, 925701492537, 926029850746, 926194029851, 926358208955, 926686567164, 926850746269, 927014925373, 927343283582, 927507462687, 927671641791, 928000000000, 928164179104, 928328358208, 928656716417, 928820895522, 928985074626, 929265931831, 929382609931, 929499288031, 929663467136, 929710968140, 929758469144, 929970149253, 930134328358, 930298507462, 930626865671, 930791044776, 930955223880, 931283582089, 931447761194, 931611940298, 931940298507, 932104477612, 932268656716, 932597014925, 932761194030, 932925373134, 933253731343, 933417910448, 933582089552, 933910447761, 934074626866, 934238805970, 934567164179, 934731343284, 934895522388, 935223880597, 935388059701, 935552238805, 935880597014, 936044776119, 936208955223, 936537313432, 936701492537, 936865671641, 937194029850, 937358208955, 937522388059, 937704194757, 937721822350, 937739449943, 937903629047, 938050180559, 938196732070, 938507462686, 938671641791, 938835820895, 939164179104, 939328358209, 939492537313, 939820895522, 939985074627, 940149253731, 940477611940, 940641791045, 940805970149, 941134328358, 941298507463, 941462686567, 941791044776, 941955223881, 942119402985, 942447761194, 942611940298, 942776119402, 943104477611, 943268656716, 943432835820, 943761194029, 943925373134, 944089552238, 944417910447, 944582089552, 944746268656, 944921968533, 944933489305, 944945010077, 945109189182, 945261847514, 945414505846, 945731343283, 945895522388, 946059701492, 946388059701, 946552238806, 946716417910, 947044776119, 947208955224, 947373134328, 947701492537, 947865671642, 948029850746, 948358208955, 948522388060, 948686567164, 949014925373, 949179104478, 949343283582, 949671641791, 949835820895, 949999999999, 950328358208, 950492537313, 950656716417, 950946482856, 951072070190, 951197657524, 951361836629, 951400428399, 951439020169, 951641791044, 951805970149, 951970149253, 952298507462, 952462686567, 952626865671, 952955223880, 953119402985, 953283582089, 953611940298, 953776119403, 953940298507, 954268656716, 954432835821, 954597014925, 954925373134, 955089552239, 955253731343, 955582089552, 955746268657, 955910447761, 956238805970, 956402985075, 956567164179, 956786892471, 956842441659, 956897990847, 957062169951, 957170799868, 957279429784, 957552238805, 957716417910, 957880597014, 958208955223, 958373134328, 958537313432, 958865671641, 959029850746, 959194029850, 959522388059, 959686567164, 959850746268, 960179104477, 960343283582, 960507462686, 960835820895, 961000000000, 961164179104, 961479417594, 961630476980, 961781536365, 961945715470, 961958835189, 961971954908, 962149253731, 962313432836, 962477611940, 962805970149, 962970149254, 963134328358, 963462686567, 963626865672, 963791044776, 964119402985, 964283582090, 964447761194, 964776119403, 964940298507, 965104477611, 965432835820, 965597014925, 965761194029, 966027964583, 966130556033, 966233147483, 966397326587, 966458914242, 966520501897, 966746268656, 966910447761, 967074626865, 967402985074, 967567164179, 967731343283, 968059701492, 968223880597, 968388059701, 968716417910, 968880597015, 969044776119, 969373134328, 969537313433, 969701492537, 969956649648, 970047627655, 970138605661, 970302784766, 970375985864, 970449186962, 970686567164, 970850746269, 971014925373, 971343283582, 971507462687, 971671641791, 972000000000, 972164179104, 972328358208, 972656716417, 972820895522, 972985074626, 973280200045, 973411146359, 973542092673, 973706271778, 973739504568, 973772737358, 973970149253, 974134328358, 974298507462, 974626865671, 974791044776, 974955223880, 975283582089, 975447761194, 975611940298, 975940298507, 976104477612, 976268656716, 976504176889, 976575517958, 976646859027, 976811038131, 976903876167, 976996714203, 977253731343, 977417910448, 977582089552, 977910447761, 978074626866, 978238805970, 978567164179, 978731343284, 978895522388, 979147560243, 979235418994, 979323277744, 979487456848, 979563777202, 979640097556, 979880597014, 980044776119, 980208955223, 980537313432, 980701492537, 980865671641, 981194029850, 981358208955, 981522388059, 981713072614, 981739578065, 981766083516, 981844441725, 981896294483, 981948147241, 982062500000, 982125000000, 982187500000, 982273320895, 982296641791, 982319962686, 982382462686, 982421641791, 982460820895, 982562500000, 982625000000, 982687500000, 982812500000, 982875000000, 982937500000, 983062500000, 983125000000, 983187500000, 983312500000, 983375000000, 983437500000, 983562500000, 983625000000, 983687500000, 983787146482, 983824292965, 983861439447, 983923939447, 983949292965, 983974646482, 984062500000, 984125000000, 984187500000, 984312500000, 984375000000, 984437500000, 984562500000, 984625000000, 984687500000, 984812500000, 984875000000, 984937500000, 985062500000, 985125000000, 985187500000, 985312500000, 985375000000, 985437500000, 985562500000, 985625000000, 985687500000, 985752747125, 985755494251, 985758241376, 985820741376, 985880494251, 985940247125, 986062500000, 986125000000, 986187500000, 986312500000, 986375000000, 986437500000, 986562500000, 986625000000, 986687500000, 986812500000, 986875000000, 986937500000, 987062500000, 987125000000, 987187500000, 987289493130, 987328986260, 987368479390, 987430979390, 987453986260, 987476993130, 987562500000, 987625000000, 987687500000, 987812500000, 987875000000, 987937500000, 988062500000, 988125000000, 988187500000, 988312500000, 988375000000, 988437500000, 988562500000, 988625000000, 988687500000, 988778613701, 988807227403, 988835841104, 988898341104, 988932227403, 988966113701, 989062500000, 989125000000, 989187500000, 989312500000, 989375000000, 989437500000, 989562500000, 989625000000, 989687500000, 989812500000, 989875000000, 989937500000, 990038117531, 990076235063, 990114352595, 990176852595, 990201235063, 990225617531, 990312500000, 990375000000, 990437500000, 990562500000, 990625000000, 990687500000, 990812500000, 990875000000, 990937500000, 991062500000, 991125000000, 991187500000, 991260376138, 991270752277, 991281128416, 991343628416, 991395752277, 991447876138, 991562500000, 991625000000, 991687500000, 991812500000, 991875000000, 991937500000, 992062500000, 992125000000, 992187500000, 992262197566, 992274395132, 992286592698, 992349092698, 992399395132, 992449697566, 992562500000, 992625000000, 992687500000, 992812500000, 992875000000, 992937500000, 993047391560, 993094783120, 993142174680, 993204674680, 993219783120, 993234891560, 993312500000, 993375000000, 993437500000, 993562500000, 993625000000, 993687500000, 993806827203, 993863654406, 993920481609, 993982981609, 993988654406, 993994327203, 994062500000, 994125000000, 994187500000, 994312500000, 994375000000, 994437500000, 994543483887, 994586967775, 994630451663, 994692951663, 994711967775, 994730983887, 994812500000, 994875000000, 994937500000, 995062500000, 995125000000, 995187500000, 995259996387, 995269992775, 995279989163, 995342489163, 995394992775, 995447496387, 995562500000, 995625000000, 995687500000, 995771194720, 995792389441, 995813584162, 995876084162, 995917389441, 995958694720, 996062500000, 996125000000, 996187500000, 996266639398, 996283278797, 996299918195, 996362418195, 996408278797, 996454139398, 996560652599, 996621305199, 996681957798, 996744457798, 996746305199, 996748152599, 996812500000, 996875000000, 996937500000, 997029845736, 997059691472, 997089537208, 997152037208, 997184691472, 997217345736, 997300643833, 997351287666, 997401931499, 997464431499, 997476287666, 997488143833, 997561807087, 997623614175, 997685421263, 997747921263, 997748614175, 997749307087, 997812500000, 997875000000, 997937500000, 998001949933, 998003899866, 998005849799, 998065407699, 998123015666, 998180623632, 998289176224, 998340120849, 998391065474, 998487062111, 998532114123, 998577166135, 998662059127, 998701900107, 998741741087, 998816814759, 998852047452, 998887280145, 998953670270, 998984827702, 999015985134, 999074696110, 999102249655, 999129803200, 999181723253, 999206089762, 999230456270, 999276370886, 999297918993, 999319467100, 999360070908, 999379126610, 999398182312, 999434089599, 999450941185, 999467792770, 999499546768, 999514449181, 999529351594, 999557432702, 999570611397, 999583790092, 999608623142, 999620277497, 999631931852, 999653892537, 999664198867, 999674505197, 999693925755, 999703039983, 999712154211, 999729328451, 999737388463, 999745448475, 999760636222, 999767763957, 999774891691, 999788322716, 999794626007, 999800929298, 999812806797, 999818381005, 999823955213, 999834458877, 999839388333, 999844317789, 999853606525, 999857965806, 999862325086, 999870539422, 999874394478, 999878249533, 999885513741, 999888922894, 999892332046, 999898756025, 999901770851, 999904785677, 999910466614, 999913132724, 999915798834, 999920822674, 999923180403, 999925538132, 999929980879, 999932065897, 999934150915, 999938079782, 999939923632, 999941767482, 999945241909, 999946872486, 999948503063, 999951575614, 999953017587, 999954459560, 999957176718, 999958451903, 999959727087, 999962129959, 999963257647, 999964385335]
def qaU : List ℤ := raw_ints% [-30308374422026199349131954132341526722, -30301220640100753906299537885034325418, -30293097720455628336003090201546841577, -30284973032245097060704773350907249424, -30276846574685197753408118613608495443, -30274775855369227467965319641766021527, -30268718347162201002352538687797896780, -30260588348891298768279246139286065636, -30252456579257989649063000559722358452, -30244323037476618626507395415482716018, -30236746259932253050970273206777178971, -30236187722931911099040170836776493424, -30228050634837363800458926724237475617, -30219911772576927718334297796326291076, -30211771135363250066990998883143307096, -30203628722579506209399407790943908803, -30195484533437492566540488311401310335, -30193695822733303946987931944438177023, -30187338567319607660702784042349117757, -30179190823436795843243195369726357131, -30171041301170677577343054010902255731, -30162889999731343866039951687205593743, -30154736918499635892633441229380216851, -30146582056684790030726126451394909853, -30144954689038416213780166634996322656, -30138425413666866960606621576647270526, -30130266988697083552959018966400965303, -30122106781026209529397507700198772913, -30113944790033132517164139129006687030, -30105781014924946695460168675194677767, -30097615455079756120356877930093108540, -30089761668533819982530820954739715211, -30089448109703795838574975010293104333, -30081278978174385103601976652383101643, -30073108059696898537601941776119362378, -30064935353647869357686539582318832216, -30056760859231810466936124939335383562, -30048584575824467809909865751105974368, -30040406502629491273620807932776390216, -30032226639021838291508895044708334137, -30027251225998239324974193310133847068, -30024044984204294435074097078759064393, -30015861537551027385674827957504061554, -30007676298263957097384425707196950468, -29999489265716460256116359307326070301, -29991300439109589894130347671338073884, -29983109817815930456124846908643586562, -29974917401035666745679881460515758442, -29966723188140589718096616514445493090, -29958527178373048408353142094627324091, -29956438462760288324842658345485933463, -29950329370974937723467484284701102271, -29942129765316856039013718518065299952, -29933928360596811853014457618837145708, -29925725156184606920600767287372522436, -29917520151277376917479454400213230819, -29909313345244125721669580016412490909, -29901104737281114868469759540829051100, -29892894326756549099680650069555595760, -29884682112865814489589816183177629661, -29876468094976315382230067046500459079, -29876201734534226014484583563985533698, -29868252272282561067758827011987308688, -29860034644151154228442913272482627460, -29851815209775726044668518850283632142, -29843593968522076270483954188439968026, -29835370919582956648335301060458325162, -29827146062323362735139791693757793268, -29818919395935165504700925240558907656, -29810690919782555045426526274890153419, -29802460633056520229235630297506764245, -29794228535120444402176850155142059492, -29785262477619244386924147424747057830, -29682161722192255393550561514631807633, -29565232654547672378677358495210878432, -29432568441411300409866296137488308814, -29281984339161481611994967133680339512, -29110972865383220560744355505829590375, -28916650492052278522818837831437956349, -28695693899266760892846094125927735891, -28444263275911591615535573197265518282, -28157909409895245356796665963427525285, -28024191217761630473782943864076152251, -27984237315584032360968678731292311355, -27944241072281905216644487583887782895, -27904202406202992360295469654579924225, -27864121235600688021119467867789887671, -27831460309059133451782806170210474885, -27823997478360603652829604619756745586, -27783831052181366706835869903023180840, -27743621874528345248962457463230944412, -27703369862587078026295289814997510235, -27663074933445126116526386489582160414, -27622737003817166497959587158691943931, -27582355990226738148338844283216718818, -27541931808959704247001129891642612423, -27501464376017416886168769305053081577, -27460953607299526058873366710582249514, -27458881719448890134990022135443867471, -27420399418327585779282955987921775515, -27379801724427756336615623785705112248, -27339160440684001145961055697923179543, -27298475481890983122951735511473691074, -27257746762737839976493514326512602405, -27216974197530287953038533991243739968, -27176157700374289190362491170300914691, -27135297185128980227119321663172426396, -27094392565359297005740308635677843443, -27053443754520725553918838099883581034, -27033104008548469273796081619703474052, -27012450665679888200377337471362789919, -26971413211699185090447304875051135700, -26930331305189451309866124387305610415, -26889204858462307425256508797434411777, -26848033783715894757902718298419372090, -26806817992753928687778103367490268425, -26765557397171323511877927814441522811, -26724251908259683736721968963951791541, -26682901437193833734086802266272047427, -26641505894749633481546353698369548140, -26600065191490396786465318517671997316, -26558579237719052063648271141019424450, -26545805211280250875679847634135773065, -26517047943429990872263385306242515876, -26475471218496599037681073652660963674, -26433848972387511193374091859343034271, -26392181114354029179298588235316274853, -26369798579819095957929022406063494955, -26350467553382002606573713487640773946, -26308708198143393970308548209783343474, -26266902957184820786136106215205155766, -26225051738642232877915449693491004942, -26192973686371697862198444481798577544, -26183154450429340474772317619347761744, -26141211000189211297494796647853248468, -26099221295245548931976161428841160034, -26057185242792255656001320510532818109, -26015323583284724181412635694657881601, -26015102749606516167330330379095710240, -25972973722238245029979183323930800453, -25930798066961396955105816003777722156, -25888575689724955056798569941227647939, -25846306496343524173655129589641952791, -25836841235932630508953866442308971755, -25803990392208804476605187940658948833, -25761627282480068043312071311888860827, -25719217072035178942719683017302612569, -25676759665421287930210905514899813745, -25657519521465897631328567124196853321, -25634254967046466199547722276360476971, -25591702880889552049060620628531493122, -25477351227244009996750150925824706133, -25296329049527112602073006251984715543, -25114445591652613074625777911023541774, -24931693362662684428556251626584201084, -24748064775607976021000345482838316958, -24563552146112330704349657073352979332, -24378147690409841129740306473471147888, -24191843523788563740788356490175031042, -24004631659001963501712087090255056386, -23816504004191906765735959956102241224, -23627452361272751312110947748593767040, -23437468423975283856296616052041449960, -23246543776155217925351841667095908603, -23054669889550131391401153081026344091, -22861838122003160707807174982668652296, -22668039715336258298126213624056031288, -22473265793489656866638054610202169540, -22277507360094924693618524432525696783, -22080755296467331515003277303191310085, -21883000359554237743582230397028415437, -21684233179357160741382137717541859066, -21484444256830021049225945780933692029, -21283623961407011893107135584493037214, -21081762528798651067763744058969800390, -20878850058192994612174458206599891498, -20674876509938024542429951722050800464, -20469831702840977869430245332442107273, -20263705311736328217985423215871017189, -20056486864441079984983281408982411263, -19848165739139801670335994441502789121, -19638731161709066614720014189600631858, -19428172202469812688693835391769489666, -19216477773428617337056828240132912172, -19003636625111005747495249230995683666, -18789637343662704338208207226514044707, -18574468347303628897037107202186215409, -18358117883274447559198465420482833211, -18140574024359120353053901677043094761, -17921824665673875948349548709696404181, -17701857520786940700433336555281391630, -17480660118274258421835358082503046895, -17258219798190635332681709532881083302, -17034523707912127110715959730386689660, -16809558798475539336356518978367416213, -16583311820461899456887960150963566910, -16355769320141174483659674454212908650, -16126917634904558608798901255540074585, -15896742889195075006356523859551281311, -15665230989961200349910146602615879610, -15432367622366929569183505189103494141, -15198138244761551288840564291772653401, -14962528084084227582762294659252325825, -14725522131148725260909665463320346739, -14487105135227112754943577185966626405, -14247261599130537767854756217033741426, -14005975773770568992568952750497371302, -13763231652964311530601714572687899135, -13519012967443603209934342710938459621, -13273303179358121746873188086553390504, -13026085476230785818691245091702863343, -12777342765146615115513392361822214967, -12527057666109162264596857170470542765, -12275212505817597825272170595623804121, -12021789311270950078549646856825373990, -11766769802575973170608464672634844351, -11510135386237511975662461079387272095, -11251867147842788312593009393481874800, -10991945844953930560265045221601795804, -10730351899093779368370804311211249143, -10467065388203336768656369135845432242, -10202066038453529478927651563710492766, -9935333216245593740217103374957616776, -9666845919255011803087046258771640489, -9396582767859426938925352164028384613, -9124521996312146811694961118466584350, -8850641442988567596030597350160120631, -8574918541074918382603445500410773726, -8297330308527845010064055869296385222, -8017853338176015833584404575830471903, -7736463786761881795459873026548347846, -7453137364401340724745073796580182683, -7167849323256418935210970166922944292, -6880574446314336994182572799448448645, -6591287035035981978550684417529832614, -6299960897312201132298508367455868381, -6006569335036652045849429033074560788, -5711085130564408112394433013559696602, -5413480533527317080160016700815939908, -5113727246737749841621913310021250371, -4811796412114882521136604282858055344, -4507658595329662369464284927331895543, -4201283770757796009109713282834812770, -3892641305432838128904271669951078043, -3581699942957905168157861441912078011, -3268427786030379440073517885463677602, -2952792279127747812866613501909258104, -2634760190599344314674677955039013570, -2314297593362568382324642665086435915, -1991369845788231051926147770863002137, -1665941571390992784741739679295468619, -1337976638327766681600311389102063991, -1007438137277803645126140520442323704, -674288359418468452104707260270185688, -338488773064538316873214226925507787, 136767578, 341218209975117642102833478154847474, 685207004613014212074634621073957652, 1032008455737164495616876830719346544, 1381665587602722114454427076957241360, 1734222405388094339401972619822588086, 2089723925344183641455944558021161308, 2448216205526084286895626158955646169, 2809746378685428596218651605131662432, 3174362685472451747730549316656353809, 3542114509535227253366418532523212453, 3913052413414753864051888626765514697, 4287228176879504320157991206387731508, 4664694835898245892039257663027598036, 5045506723193898055638268772707605423, 5429719511388020286638000770373848706, 5817390256891986881109392280274748696, 6208577446255133154055470392442093873, 6603341043825659724125187751858851391, 7001742542500531276027496645635395812, 7403845015570097675757548022113394876, 7809713171449755702169339207259471560, 8219413410133295884643030802086703967, 8633013883233367821688882752672433163, 9050584555676740177188250314676974218, 9472197270151993248400146864458386729, 9897925815491565909768203227085784216, 10327845997015710470623677950751607606, 10762035710803156905170681670835228683, 11200575020698281404930814731741678544, 11643546240109409265710240975768202827, 12091034016474295273666737553414102279, 12543125420478622032610564905638217240, 12999910038835021712521144972713627425, 13461480072811336736638201712249722132, 13927930440475794681430958933674915240, 14399358884008058476975705743852385041, 14875866083537701812181459018751648037, 15357555775456152961625483379447650855, 15844534877559005101813283647531068775, 16336913619860952305919445337642474058, 16834805683576035936918276060717261284, 17338328346085178540607730987223032452, 17847602634452036679769490392331444558, 18362753486386113341772190886104008083, 18883909921377781664213060568584823774, 19411205219998282274810445850560392529, 19944777113187067819117571928483538848, 20484767983514709129260769144499591113, 21031325076461152024332495325715992147, 21584600724769040485589741150419017115, 22144752584989955259101895793594912098, 22711943889524000684496553832151303416, 23286343712190898663306231940562950263, 23868127250803990869957794607248966417, 24457476126106093199000638203230631565, 25054578700850797668397132878152489264, 25659630417474831920179962825113787034, 26272834157248674084982127490777163160, 26894400624081001780117059343186586221, 27524548751706677058605038962828083567, 28163506138850754280392770693552881874, 28811509512543727220736799836767956211, 29468805224712966116938953654092076158, 30135649781239954856352970808190047392, 30812310409106827121527128967717633203, 31499065662676137703127723457945817851, 32196206075486094005727037294433772412, 32904034857962243416853386413914280051, 33622868646857360949163080214845430738, 34353038312881030676055185682927454230, 35094889828095533128567973350417386468, 35848785201884633903606613360667661529, 36615103489542810064477040112307992846, 37394241883838696700744632576172443543, 38186616893448428646593973270487308590, 38992665620369255001932915412236452447, 39812847143720344309887058605574895597, 40647644024500603735197919696477647908, 41497563939691414781590088334712281572, 42363141461606323658773276413836910299, 42582047704485337560109443136240751397, 42801976707553842597323212537061440283, 43022937690997087939226265927596281642, 43244940000461867333801397691568880952, 43467993108868785564133242484123635269, 43692106619710091428162385832347166305, 43917290268006749139716503326334758119, 44143553923713697476622334733156687247, 44370907593987108236669686965237604740, 44599361425749231623528893644330285354, 44828925708313687529050748155340593954, 45059610876072925795657017231660893275, 45291427511000246492355632995270174759, 45524386346463328084919976045627618805, 45758498268616466000410821293780822998, 45993774320349016001252568539882577670, 46230225703809089017085434319493702042, 46467863784519874475203889981613431623, 46706700093033174519265014358042527866, 46946746329197403426720207286325429125, 47188014364979713453439486974218987849, 47430516248920795314012309129422869668, 47674264208084646337313305519983076951, 47919270652684272931088783703799675986, 48165548179505508692122872279966059697, 48413109575682611925900441899166793831, 48661967822570252917811846901734295108, 48912136099714869250376284573493664429, 49163627788657867196046878224561435699, 49416456478196077168640257417440231053, 49670635967050848758693914220429520415, 49926180269347031785869549426963661388, 50183103618584148332041648985287528960, 50441420473377257876757109053553517969, 50701145520562657855413746734655148219, 50962293681186788494303846491231558136, 51224880115250399085586885774049042597, 51488920226863621033516003831510781920, 51754429669541424871451942053598771977, 52021424351644090483451458350381450787, 52289920441678545729366434212202974850, 52559934375197653919105506164691219078, 52831482858976509164409964050262669091, 53104582878233903543253360161607357654, 53379251702290929285223013443281460199, 53655506892170131431688288524563365444, 53933366305428269015314641892035233059, 54212848104124249222055895425088143790, 54493970761209012399805653231685381814, 54776753068923099727501521077942220516, 55061214144385342961661799347794805859, 55347373438413857368504790976398070314, 55635250743066156168139909459898291979, 55924866199713038742617200418474869488, 56216240307353831255314617456051824153, 56509393931181722658723083701591473219, 56804348311090801584286902801124315170, 57101125072037395933842775496556998866, 57399746231512790802029183763549415626, 57700234210468301005801051496918257760, 58002611842634851836161191218344793050, 58306902386094748571336574352829387332, 58613129531929270609505161507491969374, 58921317416444339927269324787634683062, 59231490631790800853963466288278219722, 59543674238937156405911912256976398370, 59857893777687003712723043981535946570, 60174175280413116255572757637044713222, 60492545284535938804143815840095868160, 60813030845755484488339391300515564043, 61135659551721663593031047585793905300, 61460459536160664220549675854685433393, 61787459493123721712400900534717044283, 62116688693487909180647468239101472143, 62448176998459456025693117846691540456, 62781954877119236871858001781209201648, 63118053422412886030148080129170330847, 63456504369878843884395110506862206355, 63797340113372577711576158752878398662, 64140593725026396750537350451631086222, 64486298974067891447094113868181535035, 64834490346684512587579946644922268555, 65185203066604695120271383006444862509, 65538473116426901195699616348834777885, 65894337259346268602370890939393333129, 66252833063610580719642086008538048056, 66613998924006645781417772260617781450, 66977874088053430792442745748213658269, 67344498680826092261577778596783886408, 67713913733106002342141086599898265450, 68086161206612184309725379733627687675, 68461284024230423555628990527178786736, 68839326098988605291513447999923163935, 69220332366626348007473898009944865397, 69604348815329419882349452588083649795, 69991422520801711618446812437915777178, 70381601680659486131503897074202658234, 70774935650641605492536051605710991222, 71171474982301219906753147336327567038, 71571271462252584918856058116712608272, 71964506475216946207972037121403889612, 72360942672304729277135325377335702162, 72760631770078789666180473525563629289, 73163626759693861123667817316290421013, 73173744457700279113016943701852243573, 73183864257065416571697655001729761267, 73193986158203966643667147424203846542, 73204110161976287603706545244311009722, 73267168072429210769980392949376597638, 73330307673830995425616897185890521890, 73393529174560890219223195481914973930, 73456832784252532654332514715804467757, 73530410712876736891665417547852808467, 73604099869688256576117472703586637846, 73677900585719267290432317144716750018, 73751813195300068053920424804036609191, 73825838032472105135397908901791870511, 73899975434598752451717216147405416801, 73974225738767555303251724283162846717, 74048589285412106511948083736125840462, 74123066414703447121651997799593545548, 74197657470183106806404204948088442509, 74272362795143598037391147242003536990, 74347182736272689951874933098646008256, 74422117640022931942135596430157000809, 74497167856267230843963045010693852980, 74572333734657339350562418629039595511, 74647615628290807057099724234426647359, 74708984728464489595624757210178247204, 74770431135028399895972966649458174516, 74831955040366880350677096430619090032, 74893556637590012876296476123706071445, 74907638988849685091225208929504729390, 74921725406391461330168484037308002730, 74935815892533064439082589259731715888, 74949910450055959667920747441224784624, 75025777757145008163650731428871780226, 75101763227073708653353072818956681744, 75177867222694710065145269164493749163, 75254090110411726221201557071719238201, 75330432256481859659419621838039046132, 75406894030740504372615244040956909271, 75483475802892234928512292149070647996, 75560177946247521038880945686185288696, 75637000834002113340370934260531768985, 75713944842985645339680233107613154296, 75791010349929446614807608625453860355, 75868197735227108438191269942306502258, 75945507379190654548341431836826767100, 76022939665823147519346320962382497884, 76100494979063146636477511560412289576, 76178173706569432857720137554487684884, 76255976235953682703741221854925405752, 76333902958577390445362725795414510582, 76411954265772686288163200327243731210, 76490130552651535219281911858098018094, 76528456792215587223752721245032160739, 76566813140414243230270002996788937395, 76605199644024560744997557715222489616, 76643616349933761709150601301048690981, 76683686205217875770374710528585267663, 76723788970144959017858987542192666666, 76763924697218482891182095865978481877, 76804093440988908480343338178166822685, 76882900602491164124221039979687522592, 76961835148809131556873682268963205136, 77040897486645740305966473505671058655, 77120088026608192797470828728105495892, 77199407179368405668479639678150618797, 77278855359534812204401576013766543158, 77358432981800503997512604174415143258, 77438140464827804087454207173108282294, 77517978227384032634147672724704295359, 77597946692238936123406044277929115765, 77678046282288000034305308519504878538, 77758277424462820368861727363036868882, 77838640545841885597724718648379070405, 77919136077573977683306036688466041459, 77999764450976344883642659751620241567, 78080526101471220362352870261819633460, 78161421464671306718622996141194790141, 78242450979835548355326478626394574043, 78323615087916838182032818579799625282, 78404914232563783000802020389856381829, 78418365143198254459815937202148466182, 78431819757270634988872206035814334241, 78445278076799629798163837819398448432, 78458740104301756172790788013265174006, 78526780049628817790668583322684171655, 78594914857608716168656579589056573517, 78663144790401742201665835291135349277, 78731470111766675246757731007920595568, 78813451161612079466096917672424231229, 78895569953985487140067592050228738386, 78977826946861473774267999306517328680, 79060222602538996561324611573011976142, 79142757383649046612807774344027018285, 79225431757185537879381782705127760300, 79308246190499696570376183331919566782, 79391201155344807389169046006911217874, 79474297123857255018512926803749941053, 79557534572615224736733891118003233126, 79640913978606310059934931623621761563, 79724435823300265879987258978585924303, 79808100588603095558942658673950974580, 79891908760943955822083139311079310053, 79975860827215635795171597691845752085, 80059957278875713995363990517202422148, 80130786866953010033933143394694943857, 80201719197233954168432887872576734150, 80272754564512313579845590668916031314, 80343893266931819619170999159538594105, 80357363588997324387466711118613752861, 80370837622375827825625231203576726803, 80384315369095005168235870808406556370, 80397796831184211881313607486024947940, 80482622652714151745139744221133761802, 80567595856185295678556844275638060641, 80652716949145716101157232443312111807, 80737986443881527171145428893226471422, 80823404853287982095804916657020267602, 80908972695043435841471795126933235494, 80994690487466291920780116475915287235, 81080558753703843570416746160444199546, 81166578017574976615300428033180018262, 81252748807773997738325215862646467543, 81339071653698999142189188954678116084, 81425547089670783796748586635394447049, 81512175650746796730001867057670609095, 81598957876955258420973912280227590689, 81685894309094566652285969977386385659, 81772985492982750520130040106852955526, 81860231975242245871821925079170218043, 81947634307031948315951631319630512010, 82035193041947651675730601157512246832, 82122908737108333076810626447541828613, 82210781951039866386671078548101947944, 82298813247439241806107222199473294681, 82387003190914870960521862289385027567, 82475352351298474940567030278653716773, 82563861299370365779297586039725403776, 82652530611187237803270213580814384407, 82741360863792323821218384634125005227, 82830352639559210554724494340850781230, 82919506521886766893390417455765328853, 83008823099559105641292154583886052329, 83098302962425180212354810573541618355, 83187946705775016421427064077164276510, 83277754926003873001641133549252245866, 83367728225004868687700925214461912669, 83457867205817600934335885182939533389, 83548172477037295084893511772770219896, 83638644648447774656502688848470568930, 83729284335447260959928168503653649735, 83820092154665587292668334741802417492, 83911068728406778976914832024427244866, 84002214680250402766448776644052508397, 84093530639511058899120919741015020170, 84185017236823755977009175485754507314, 84276675108620448288781694431171887906, 84368504892699325365070559704547237633, 84460507232718529515110906989540840675, 84552682773749248190607657694227266537, 84645032166786748400888985822084540820, 84737556064287158938635772746199223994, 84830255124695960089200345835531776291, 84923130007968341680376888487353316333, 85016181380115288285292773768456770551, 85109409908707397955871890048008754839, 85202816267438704935606499191069746324, 85296401131613842822458651584606728025, 85390165182729748658690769871969034004, 85484109103946053143622578713784238675, 85578233584684811853389973541785415284, 85672539316084003987191373888977515125, 85767026995615438391235251057852615737, 85832571284839480505476971200613475381, 85898203409965642322141651446292929392, 85963923605738652245502280394494757730, 86029732107857252077457500152294256263, 86058975667350695481502807381253466798, 86088236698675247969263353507904988296, 86117515221476171197017428134047851227, 86146811257755821536186624519643394888, 86242219262925797768647749583136235557, 86337813480197601617691660411552528056, 86433594635070459809639849606701776448, 86529563457930297665059089488186158437, 86625720681744845590416900645714939781, 86722067046193016247242530920510382865, 86818603293014500546556928026148672544, 86915330170739935988012295862067214759, 87012248430022748776736986018126463191, 87109358828388587682074472656957251144, 87206662125549284251847591706846438759, 87304159088171716636416862731253692827, 87401850485173758635079626584994137656, 87499737092512740218372051032887041730, 87597819688463254889643668591996198537, 87696099058425385971946944292700567269, 87794575990184240504828224112456431009, 87893251278738112743037056203778085148, 87992125721539611534325163569923350402, 88091200123343934906861232633035059023, 88190475291431456588418421660857849472, 88289952040476288039140049284004581931, 88389631187750188476026112539904776750, 88489513558011593238948587929312928168, 88589599978690710376936760714675595009, 88689891284799196819523352761950024720, 88790388314096303263112008982788010477, 88891091912019382258333153472195783391, 88992002926830941805907221527919845593, 89093122214570172165240390168505736118, 89194450634180767229845343389597361723, 89295989052483659614504810056956376270, 89397738339285467530669056038759842433, 89499699372372630520809402390723433761, 89601873032600338194490781127771538126, 89704260208908261850737360769795120466, 89806861793389820065914560235096047322, 89909678686329704379805732550441999738, 90012711791253335347290277854089579042, 90115962019986383463219747709929882048, 90219430287684267901432042232187311152, 90323117517913876919320379217312027091, 90427024637662960110290176640204030583, 90531152582444255663108469305141600028, 90635502291284625547831137983755238285, 90740074711214178917257877719394997394, 90844870794784118173140954070854325015, 90949891501394677023637639543367938369, 91055137794789685294443701555430546112, 91160610647592931529532290463551141596, 91266311036235609315292418224929351903, 91372239946152210904097359607140316422, 91447660502297094723522884061236842531, 91523197332832670497969758131021387838, 91598850797018516561487334875872343180, 91674621256455012295125887501905534289, 91705501880129122515708140787179012326, 91736401979105249242273045864564463214, 91767321577981502220698141111743095377, 91798260702054817243874463780966081640, 91905347205783854673066093038761361470, 92012668273966046523426703557450840241, 92120224936091617925663050428127405451, 92228018231174360566156265623804331606, 92336049202573119205829352514885548496, 92444318903307466277790719570468700451, 92552828390857511631974974459704212253, 92661578732504246732946348964571956314, 92770571000107512613876487353479515721, 92879806275471260684282387793238177034, 92989285645099512408621919238443644592, 93099010205586787872847878631172192292, 93208981058351889233126142542493049628, 93319199315053752431281622953579518505, 93429666092302884988809637295766956267, 93540382517102900607937339984978190107, 93651349721539440416208532499130547411, 93762568848247654645489756267693088718, 93874041045078434964037170979267779580, 93985767470592111993988569158652534124, 94097749288701824902119828027477769505, 94209987674193708200982760905489011583, 94322483807347223307761421525145785107, 94435238879482112879199917568976096101, 94548254087555517591395803804777569562, 94661530639735981188137396836851026564, 94775069749977174284535250044684028660, 94888872643619238366655695389657120583, 95002940551938936980102708924969019384, 95117274717778632110377568179155468350, 95231876390072681685497388060515621222, 95346746829504347096006962800764759958, 95461887303008254520182901741896275172, 95577299088751746241158109818048391504, 95692983473426723878493978033212886290, 95808941753745572074558849917475911536, 95925175233705383521268307317006522444, 96041685229628372794311514156347489654, 96158473064591420204046527598018494932, 96275540074197803160877236488786713870, 96392887600982059974559621624767071956, 96510517000211231278460904158324131366, 96628429634264854424568621824101108623, 96746626878466048888333821203428240983, 96865110115436450598472472424080674085, 96983880740957481688608916687677245875, 97102940158300032820084788749541091081, 97222289784116264274738948632163222676, 97235121434338231301272697856560130668, 97247956448244851067954334349358451603, 97260794827609587178818400480906657455, 97273636574207327816452326786566603124, 97380530327974937499951039988842596768, 97487657968615877604313706452792624803, 97595020526118005390322665127334301791, 97702619040341148503392514158629382249, 97823441306609113154880033578884106314, 97944562498753056880507390944417231344, 98065984106924631002830004604649801172, 98187707635598784330427332161165420705, 98309734597774263784537184448173078088, 98432066521023522849274915066807263316, 98554704941666793564523263691687112052, 98677651410854758670158090381292902521, 98800907488715995092823891484121253882, 98924474750472808940625391235831768745, 99048354780561849671815442876192778734, 99172549178783515471887141949637198428, 99297059554395536414229996526478346613, 99421887532296366386078740891947074976, 99547034747091532740033057732564657169, 99672502849311439839411328743136377616, 99798293499450281960698054923066466081, 99924408374218692713557458488637542848, 100050849160555017293654547887954947602, 100177617561913251509498297570394121651, 100304715292246468908948957998838633308, 100432144082330502926358098299099037798, 100559905673719323921112534428337897916, 100688001825104928057008248012784762038, 100816434306244458904518548395980309359, 100945204903571413724308601744553749304, 101074315417233681569162150543332462142, 101203767662821314945600278587509048907, 101333563468371771338538355136558357804, 101463704680058011521596120433658831965, 101594193156029620531779090741327182300, 101725030772922373439731240769109433212, 101856219419670277871074980786098361804, 101987761004053828127212217322875870283, 102119657446482763730552790493951125976, 102251910686583543562476276292626045793, 102384522676952615291287710748878082868, 102517495389783653930550118748301196634, 102650830810591137553574405570120965284, 102784530944877907858402696596120547865, 102793926693819731404458824229622959173, 102803324249290521595845160507348589433, 102812723611992104525212810241503259291, 102822124783442819891421425221275493520, 102946867942087955801521892385086169954, 103071930305839453562773518936343671456, 103197313529405926107066986105937380805, 103323019281440778480897286730405937116, 103458573635975925595135086439759303090, 103594505089784300192208521178069234766, 103730815767797996397306319899195328108, 103867507816615877217897091654440117155, 104004583398075644830024777427038437878, 104142044696131870279531642740702234491, 104279893910397164679613527270586227071, 104418133263064180981380871780582753312, 104556764992415690986081538157233263337, 104695791359791223404225671531007061098, 104835214643065853942213859800832566620, 104975037143662161455615772883765433582, 105115261179997541031127622616863420446, 105255889094542178300999654386062358733, 105396923247234698428836428681549978085, 105538366022586877621760347814281397159, 105680219823067444265593426346300251509, 105822487076254266384206108897447661697, 105965170228186124880705235210875168821, 106108271750563136186698900073239369698, 106251794134066321677597150814056937219, 106395739895607046067579601070138145637, 106540111571614211607163195167624745138, 106684911725333514954199934815537968780, 106830142940082099760620876397411268474, 106975807825709900192666611604595196117, 107121909015373155995993513400537245158, 107268449167612442367226863630565294534, 107415430963088028876278454199859017539, 107562857111147735569678311931619618937, 107710730342983019928082852717034126798, 107859053419136011140760668988644926567, 107972817219032558755076272170690661574, 108086847123808996838786552726979439634, 108201144399485077384944597599460119189, 108315710322216408786484908022867163546, 108350969477254496397748635432541598642, 108386254158512044884280566700461486289, 108421564403524393233304284876999826155, 108456900250827215412184722843981836903, 108607514848920144145817168436226163009, 108758596403384104888063477338696121018, 108910147860894307962457803987226787604, 109062172200348058423208217340288818131, 109214672425853864621808625456928708641, 109367651574519331334630083582058497257, 109521112709406547751164266421994867754, 109675058927379270936710202820555829781, 109829493352024510438017042280260065249, 109984419141560120427976116232292497218, 110139839481722510895434696910913802099, 110295757593735803704204909149804517663, 110452176727165614146360076638890392940, 110609100167950964744928121970822194958, 110766531231224095878658625555803968411, 110924473269406371565390582141688906672, 111082929664994093991269082992280806238, 111241903838719677835567728012907038867, 111401399242303460944843394213344364402, 111561419366681468112757645047157764846, 111721967734723228922407167105329610461, 111883047909527498396991515345810655182, 112044663487106113291315163016987059899, 112206818104749085809920585097244787279, 112369515433674551468923953120235532101, 112532759187464703275423757626377732969, 112696553114681907819065096450035091617, 112860901007377001067830914864967029757, 113025806693671674709638089497821419050, 113191274046340711203219294905005667809, 113357306975360769707946879548457975230, 113523909436568197403974808573056632155, 113580408206370134634432416519525111502, 113636972788634452833659525769506762546, 113693603338807614993755020998120087662, 113750300013922215012811798391163917538, 113861365607963084788307815359889324141, 113972685867954798370805668934460725105, 114084261985365740088715726481491725185, 114196095164344898390304890576210447464, 114365606094385153883919325661906946796, 114535711192480720615694977624664780300, 114706414720724177640863182525829358674, 114877720992352600803893331917058522272, 115049634364131399041248904428313650155, 115222159245416866899060573652595090885, 115395300090507899492755158181400333156, 115569061407795376888763718489977473799, 115743447752082146815518685754713797594, 115918463733821391618586235408228331362, 116094114011405317099780104268636087738, 116270403300494743079019467387208506541, 116447336366276989786987332369020897803, 116624918032889028503602953778400005083, 116803153175645114036558327974969184423, 116982046730555932806254207836127737620, 117161603686526591423923669482778503501, 117341829094974306334674899710792806771, 117522728061997424707683239876147162333, 117704305758094312741314046078468313355, 117886567410304156366109552518453738882, 118069518312029825000492414633659231583, 118253163815151276348928849587680011271, 118437509339955299251048629645079434578, 118607746685325703081318272616881780104, 118778585605018627147196660744941944225, 118950030464959528660988656140422372736, 119122085684364277642913507231396855079, 119137057874386603419631679503907574274, 119152034705046489368406181832080112034, 119167016179290684626056783216803435729, 119182002300068804826274987794903901098, 119369931508924153466928043310506671251, 119558594650057434042868933823927137633, 119747997617031037813029630629975103639, 119938146380864087810735200171219346716, 120129046982024358876755590126022747951, 120320705540940981277925045877134808751, 120513128249975890989635095385390476581, 120706321384063970590474109713967091255, 120900291292665587520990025043232910345, 121095044410538213988689671633467120704, 121290587249671751170184661618518959290, 121486926410195876840764459465117869310, 121684068572300004902795540130440046727, 121882020507280830192728208476908276803, 122080789069448936261144697102711571293, 122280381207321242395375457757511112410, 122480803955516449286192895884436992670, 122682064444868919653866358116150457085, 122884169899223874727681888315393493682, 123087127639579694520143533394970646354, 123290945080866671622746839490391945789, 123495629742381698581297031114503545466, 123701189239665354313246269866164512025, 123907631296326311277771846683530042161, 124037083337143038735852845883755539413, 124166884975167814279491964194096285930, 124297038156261375231023507242551040893, 124427544844221559936778862612201775931, 124506061193089493760705446674418120730, 124584706086231455037233297750555117960, 124663479956061630168428425109864747151, 124742383238515726479650477560460960298, 124953357643590464496632837824813754021, 125165263208365713454392337757091062809, 125378108428428658460615049987791821605, 125591901924064511257908218214454723974, 125806652432168047687207284108463072200, 126022368818999855869165506490063707798, 126239060072117203825498047170469119630, 126456735313339473045672293048291303759, 126675403790703351688119014893307593334, 126895074891646163530138749378608265937, 127115758134990809556130132006523619730, 127337463184356249483694609825303289230, 127560199840178079224768620910848721668, 127783978053356012436278981834439268106, 128008807917316486895566913965528526843, 128234699681907630811633796602636907422, 128461663745510841554402878582198366426, 128689710669194410171684031638939198312, 128918851168881615546442507009847271080, 129149096129774925550293234420536175578, 129277163416389192919568340834037501353, 129405575143214377837377303950020579636, 129534333226328942639094206975005912955, 129663439603924300922799168637028072158, 129767573052769431338100405193761382770, 129871934269244756903342914506075458913, 129976524285162300012573616833151631560, 130081344139527498453839708104137512978, 130317280607029888399606565636052389323, 130554390464893419512546206411387699419, 130792685838983820069517216760488939013, 131032179054529212348602600802141878801, 131272882628709025342130182708937528974, 131514809286640598605259693421614086866, 131757971954085905904675061589315660565, 132002383773799799887118467103670373208, 132248058098368151851306131533564316929, 132495008505428914743648425278872572838, 132743248796680875300596021183970136826, 132992793005989572097377173526464798889, 133243655398542836895137351413421312471, 133495850486905099901423515609994269260, 133749393024344253853941439650772496841, 134004298022834064304252835286293683299, 134208592574150909958660714619040450507, 134413771410163704466205917685391765735, 134619842506425652127371808905607475962, 134826813951157399486042397654154341079, 134879485337171124414719561743599016285, 134932215376467912573744225401521700224, 134985004204739221201814326161213355319, 135037851959750697990644569864254119073, 135299803648113071087618932827285869679, 135563213496197284270355141693243657694, 135828098452351088040193804682684741920, 136094475776187812793163883762271368687, 136362363033141130027261807608489072452, 136631778115139744330347478007102254005, 136902739235488567009618899563481745870, 137175264950182096734269731458552098585, 137449374153145168056476987292548343758, 137725086098226868353809921602726578343, 138002420394837270119707932184928974249, 138281397030667416115856111582041952403, 138562036367762045693809072467278105440, 138844359166015254138772641621422856917, 139128386579723223511426405801120655984, 139414140181909673740781011515297331311, 139538852810557914714428847359609525289, 139663897352901660362351505434093381481, 139789275652611783727941210043147644293, 139914989570938411460817899647796656557, 140079090091246241110934334290720759870, 140243766325846643692373490554625268546, 140409022498320173750093818536807735259, 140574862881919106392536936443467650406, 140869586159053125824576147633232115109, 141166174328749332722383575033282609009, 141464652167272252992685955043739512430, 141765044968541260342599939110086741171, 142067378543918342542416531204365947897, 142371679251690337429242719952269363796, 142677973997714389451124484910679480493, 142986290266181843703409951093932452915, 143296656121209813591993012052291086326, 143609100238990379767099443861626226828, 143923651910426437993536363626032229226, 144240341074780642027980049744673242770, 144410702587914123116812316563108431030, 144581689744075534872899523375164991434, 144753307364132105570677963833930291091, 144925560334294041567962655925343795314, 145075711002594252918237871939791220529, 145226348102178261329145090958746683793, 145377474940391147542167576720110104340, 145529094861349730293153715938760327933, 145856944315225277727012120157697931665, 146187125453133709724301674787852089335, 146519673269908730012995611272271755864, 146854623584448394343809149803424621903, 147192013049482453647735509071748085581, 147531879194919425121748390518865082535, 147874260439534522126616655047664252199, 148219196136819793056322964933616439289, 148566726588805442641776735740915766363, 148916893094653620448223903893413990781, 149269737966852395621953093885702319145, 149625304582822793432360476177753193376, 149682966229100781949233895526141186560, 149740700162339851655441911789067933105, 149798506570959987630477756350042243948, 149856385646331194653187600164947227793, 149969825661632258943735391207219145371, 150083545965539699700745475728466623788, 150197548017010327439330607446040431679, 150311833288950192417465018111991478837, 150449963975346468019828634405938558990, 150588510905161302422947577432594533557, 150727476723470598889122191719603535498, 150866864101359355542653253981464288233, 150918982857499183079933975353738212778, 150971160825669421809177842895373720509, 151023398142999673641411112338724880765, 151075694956097146529180983315975439596, 151163687925234742262100781471681909333, 151251849893767979468998398722611116930, 151340181541208913356406488514942335066, 151428683560358363786443493378871620334, 151570219737402373189616400540469926666, 151712194066610987369037030686522224717, 151854609411203743413833018872926234701, 151997468663361802492346633609030292324, 152140774744626180934144877370103868041, 152284530606302919812597488259916637722, 152428739229875339630250284264737671403, 152573403627423530354454592885517229257, 152718526842051230800311288026196033135, 152864111948320255215334261697285839390, 153010162052692628888839708934069035629, 153156680293980598692558708016683156964, 153303669843804688661118267200718087906, 153451133907059975045745403728356560943, 153599075722390759725868728490946998126, 153747498562673825445420774835321064451, 153896405735510461057935924484645931478, 154045800583727449821509270931119866156, 154195686485887218786015847831498853785, 154346066856807352465547740048118603070, 154435680173717582666456913285093305584, 154525470110827402862711314161802656012, 154615437398887204855547727895638224947, 154705582783064354930639171336466336085, 154767212178618956303913659413133701625, 154828925125786046449692738678317156955, 154890721858945290262819353099367152144, 154952602623278368761788029118681742054, 155105507866784909715747953794921705062, 155258928859642003809709951864608699685, 155412869285831517461230482372565254438, 155567332870109908215895088677984782288, 155722323378622091209791024316047362911, 155877844619527021822367908113967357241, 156033900443635265807155758327023736918, 156190494745058835583147721976579148423, 156347631461873578997212113451358442096, 156505314576794414735936558868887881513, 156663548117863716682416368159620996661, 156822336159153157888613163226177183902, 156981682821479333476320068514597071271, 157141592273133490699142472836774936494, 157302068730625703604295497981940679528, 157463116459443839236896307643069548173, 157624739774827672141683514276998779241, 157786943042558514049065520215223407890, 157949730679764736095889285115650095483, 158113107155743571738622887241694046069, 158277076992799599680561290142570694566, 158441644767100317668530099164217816695, 158606815109549229932269748571517825089, 158772592706676883355709076813600552573, 158938982301550300198769963681010639999, 159105988694701268346910245128503988290, 159273616745073963669706390259271542311, 159441871370992393136497126915547831951, 159449281287924799736552768102974031907, 159456692428104629541393331256742184080, 159464104786562027931660596523848682309, 159471518369119376771921521809701853708, 159633074619509643529983575817308839057, 159795213346323678037018811527204931653, 159957939008964094230842895782575956813, 160121256130800504100132945910510703162, 160292719557927730876641238883064943379, 160464840374325444607545054670331502397, 160637623942839394780260930530196569304, 160811075694211932306126871628553014867, 160985201128252402951852559094968000305, 161160005815033137260294136495660622243, 161335495396111716575806502010872378631, 161511675585780216047253829324477758699, 161688552172342147506007546639597503178, 161866131019417847938256975439087702614, 162044418067279082923460939555878332979, 162223419334213658928044071228181661181, 162403140917920863761336554401684856562, 162583588996938580856780968695412816535, 162764769832102950374843508199219775651, 162946689768041478475966656029876293162, 163129355234700525525318018299544421621, 163312772748908134511092005441292611349, 163496948915973192631915450297685562471, 163681890431321951885957351355103745766, 163799150810462259369123114536588085562, 163916721221542312049385227684758350388, 164034603411273267693259470252657422059, 164152799141627986155070793612225835815, 164221799739401034210939759865273167003, 164290907699835067371006762517738587918, 164360123378577077529733950601103238738, 164429447133098921677847976764597650994, 164618319094858317678167404202584530717, 164807998566550695324236453243243464185, 164998492923616410964165220431669924925, 165189809646185270252812535226982298865, 165381956321101533788904216823504133062, 165574940643998653556367264576001911349, 165768770421425223863256266173737477337, 165963453573023682652298332480850966674, 166158998133763353354317328902800368180, 166355412256229473967010011419821364558, 166552704212969918869146961449390404017, 166750882398901380131975653901754396053, 166949955333776838878736407396531790342, 167149931664716223689021966766860284858, 167350820168802222272752659012657791163, 167552629755743284780979178744090001816, 167755369470605932316774567763867589299, 167959048496618562605793773195551318076, 168163676158049026537210247329717954972, 168369261923158334554590722016400964850, 168463705387893274975191031958826847601, 168558352619354011204180202037498922141, 168653204550691098371814336375515316347, 168748262135024268291180298761543572024, 168861103103683640315060895509895143663, 168974235430624216647405050993841653241, 169087660718582252972391617782210125930, 169201380597465236714598965651913125295, 169411904161521705918232960892779456102, 169623445838316222533389451121825077748, 169836016193698937776151526463256468931, 170049625964197802079202842394820636293, 170264286060779643058248070809833029940, 170480007572716562759941492617234151315, 170696801771561239943580119785710987963, 170914680115234867176253019452326867165, 171133654252231603226045661327137786468, 171353736025943578971743951328516903590, 171574937479110660182464927531850471111, 171797270858399343451044652567826119735, 172020748619115342708663979097399307052, 172245383430054613548014249828658547282, 172471188178497761507993839138586857358, 172698175975352989022745281134965130533, 172837197871943503674914324005578061762, 172976667838000783858089196230060931219, 173116588971487981901025887186504234276, 173256964407385503574401722878570617611, 173346997428240817824192348120531183906, 173437218469523102433947725030716912406, 173527628373785341122205171885173923076, 173618227993162157755650294339440748800, 173851335902545329553371491660335951623, 174085710530093893040268767612091413421, 174321366709777672490969843245941586331, 174558319546381030882684067800086534828, 174796584422254541544432252867257490700, 175036177004280757139601247894273920210, 175277113251062337607226016304709588921, 175519409420341175114312844457751955764, 175763082076657550312011659702257672912, 176008148099258771427517119888732433565, 176254624690267187225708505770610775427, 176502529383117927989614259844267995778, 176751880051277216838503244061204419643, 177002694917252608467195660092372528733, 177254992561907055396732465831640443851, 177508791934089274835904595529019852007, 177551073948462822655504674057599708982, 177593397978878212119903530214985122554, 177635764111018420019485106226962777771, 177678172434936882457126050526661010143, 177891849435890524790799412557983695475, 178106605006765434195598649800619082627, 178322450912429877365471890668362308156, 178539399122040249989887709341912051960, 178801004960898092877609491704630267738, 179064234530665727834952839690039029066, 179329109655226964105194545551319394205, 179595652616594235027303282504051299878, 179863886168059029732967671053589044298, 180133833547823010183667403663313947841, 180405518493131218826954086756386381702, 180678965254929908878336208792078538451, 180954198613072724552177410696862417042, 181231243892100227221323710398750840028, 181510126977619110599551553505442668038, 181790874333308879133328345375494959393, 181845885001919228662836616365094074793, 181900967909143469904921661495444675070, 181956123259711582700674785762492034003, 182011351263785666730835312866058375869, 182239882090754964652325801852528226041, 182469666659316516353748868789018044468, 182700719886852575638597923741040104576, 182933056972585417697686500817339427731, 183223544142749212522135194096969039971, 183516067543859086154769173306008193657, 183810658221580324674840516093679905946, 184107347962175892829042855650553531819, 184406169316696376271017903728604000790, 184707155626177262965763374221962251471, 185010341047894727044832533995218146398, 185315760582734153625076243002105847951, 185548860761691444690979846928561614651, 185783282070635051426638482695035631080, 186019040799501089401142321472116760366, 186256153552104092045848202802600559442, 186332032530829944248277727749854441203, 186408051396987363280390713353032780497, 186484210709437182943236903744255206177, 186560511030513456858702498122960981327, 186877657739082637300317281556535359558, 187197267969989368549763387703374096625, 187519383502195253096801477272813771968, 187844047224987868047552446747790333561, 188171303178432996490906989923533579885, 188501196595707949870809619638697628733, 188833773947422786974930685860938282655, 189169082988043419509854929292995205584, 189476370107074528160502425582680988279, 189785993989657043827127743401819587927, 190097993502815565808200749345440412539, 190412408532447512503989276250674465271, 190443929288857843589048777425696191790, 190475474569922785360800661435602205353, 190507044411497494447092052861437017230, 190538638855100170068801401900774150705, 190888371133245701673266046831139403228, 191241151485111094089180490638787984018, 191597038156375327890185819188284456055, 191956091140169510649357485910909436236, 192318372249053713950327284571656785464, 192683945190783131506525312266142819936, 193052875648107476044159036793121593323, 193425231362866159164912404920027468575, 193686352459575584933270212505413579168, 193949189539918899968898249200091716020, 194213767312059804163354148582296299866, 194480111047752905959799583006584771740, 194597148469264911876508505589569891608, 194714530752162152379751596582670042875, 194832260115369773651588488286634757336, 194950338806300977857784064442402553518, 195340915494029570125598760058598359375, 195735372457872633132172018898289911026, 196133794634215862745891929639430191658, 196536269885074683832858232991306467748, 196942889136708620708524975053056574797, 197353746526644902872049168170520613391, 197768939559736177603171000935344878476, 198188569273932384905940163961959595575, 198256104267060955325798501184148112435, 198323755873077117997044471548339821222, 198391524525433743348040774195180889406, 198459410666923529072011924189870378859, 198817913090748360425256826189287754121, 199179734790130503313911784436697890987, 199544943601757900980951905119519354588, 199913609550388957656074505001161975007, 200357074889759787979839288684493528302, 200805668041894775809423241008643744836, 201259520408143850927826178939606517782, 201718768703836615918179170101741712298, 201875757141140281889716703542238292168, 202033388133653964039837575748202780151, 202191667456178022003529142594503389858, 202350600972272333242575791945655994100, 202662240501910623948221249273889173037, 202976432268130513948599380061289001758, 203293222482712008525451297037062982474, 203612658680537667125340814491801573202, 204101145327498858454192689115593800198, 204595977978818640081563930770071689841, 205097340174855283501596862611495752094, 205605423853960197255706060566623055094, 205741849453836919544797697336831996214, 205878769557679391285505616246040802329, 206016188098815040204866234670403297246, 206154109092881049817032286165136071661, 206536873578532333008766156435013027717, 206923572600544180486163612283226147861, 207314296046586635399749395699155455987, 207709137078184749854797385967567418514, 208237819762784876085964963923483719253, 208774106857280738076862165648201958648, 209318243030592613127461154832915807838, 209870485473743698929144324764078516749, 209887436117618005545267213934014953752, 209904394548851409375646869669949113284, 209921360756943441840080422118561844059, 209938334768132907229595174757702235507, 210517236178268313838208095475571448376, 211105382504670627892232874230559654795, 211703105235491555415413679155745865298, 212310754755140339835749433178442482798, 212604535928645129470206223352078660273, 212900707112414938270590789181228252633, 213199311606966478730251603562370742413, 213500393947794276595234486939079409447, 213832701326188516583212709028037622791, 214168091546600776739427272248767984021, 214506628446983572287116630576384582581, 214848377949739394409775962389605170396, 215384915840640541484813366096445816982, 215929610538709254689887871480187533736, 216482741199655108356909569352231131526, 217044602175015866552953942721809253112, 217177432989949470950532592895086246079, 217310763369617128655833000680017841499, 217444597477916876334047101064001965769, 217578939544591593532082967949249985707, 218287670206906806637662820370381378517, 219010958072875069091381452835176145240, 219749482202332800516403991903902335333, 220503972397204493421431455631234076974, 220512524328588317742633028686157114956, 220521078365916089812831298829549578678, 220529634510337989184236021443460576251, 220538192775357836771031045835738025642, 221318958732553954652807273129839606527, 222117772038672764255943149661598271265, 222935585325533725352261885605318276335, 223773432075316480207605225905068491512, 223799906242943157996058288456053254206, 223826401032056592881111011286584957578, 223852916478386023642730372955709131628, 223879452631371441575416600130475788319, 224672934832209929321657772301148245623, 225485482719509413116050089298027835664, 226318146153584574242553709223301800971, 227172068173372980021553865970256448713, 227945928841105398732846364082326516568, 228738328166693221733823985605333586403, 229550286248014113335586497438308524500, 230382913629595473199146105726519864437, 231137423431297738520993882048168537940, 231909956623667543922546694592653881163, 232701504245775089595450679281898017288, 233513145177107777656510598073418503136, 234248588418628510988243139263096746291, 235001551518458395603730878448692644067, 235772997180842869919616306200368914144, 236563973411785380166213936393326190165, 237280646349014150229185328848363522901, 238014347328567171848307336870226503560, 238766011414963266795038241801315128125, 239536656522422459920597398569070596546, 240234865839202531513568394291204412336, 240949622974723141291855331403611588474, 241681836099480152964760042157476668346, 242432493806750408514821210775787696246, 243112555054746792373535650667341664303, 243808695493136808326441946314651730737, 244521797049188711045434244003928911151, 245252819754736781928259751977406824908, 245915056082286362087293413356551951534, 246592914398033804087435900511877768990, 247287251063453278196882541822495292773, 247998998353233634188945564428112742699, 248643739136966895817255309419281206042, 249303656005182392399664841103158338028, 249979580513391277024481218056678453309, 250672417799770938347826766420677775572, 251299997432497641125311811436610567911, 251942318502316438703517054919863663630, 252600188331659775350276499899261510887, 253274485700834971196763103750749394984, 253885242576762502985419985737365488936, 254510317262540625302323448254695599139, 255150493487215067997746962615501051642, 255806624457264319018847897861677830646, 256400899826967415330022656032993234446, 257009080270642056827634992577173292004, 257631926636824667118287633826216233322, 258270267100556366007291859488810496381, 258848404230124283429503116842443133582, 259440044379642131995371673839883950149, 260045926145364938117481223121030505008, 260666853427188398044452856845730375707, 261229196607712146974250952311208947720, 261804651344651882855618437622503356887, 262393934553463876229221942692033428931, 262997826525241159661764475465224454901, 263544720282447771977976977076458929941, 264104344497808074712924690729115384781, 264677395003606248278061346748790067618, 265264629191571052548986467983989481793, 265796417621172858280605191946903957357, 266340565650042673873275284250465766597, 266897748554536219131624364076222280862, 267468701349459585348048661864055311585, 267985727473810258804882631710721705022, 268514752207080183842549437671122688474, 269056430956509842388696372344561440239, 269611477110402959792127719319159042627, 270114082074466521865627535461254891063, 270628334577392760628068436842381643469, 271154870513920979191719059976158826792, 271694382263228749843736814588243520721, 272182904978609978446773022127454988485, 272682733687916204335347620421147981189, 273194485531013096190874259435570071167, 273718832246719174550290069564617289973, 274193608894660575401496593187533051113, 274679359297051238567010379493877560796, 275176682380180320027731154644440745904, 275686229970545708965640168114645539899, 276147593325942798828321154215767467510, 276619607459460060906010582399561589683, 277102853526821256929502998615470586826, 277597964008506340483933117293855478346, 278046243199277524637407928167139688008, 278504859278021213599871310369927321603, 278974375926202034039572983886779122902, 279455407046035647330831560635373481492, 279890927290388417136536113680897465369, 280336479217454336962501705867666770717, 280792609718354891511364356925595928056, 281259914461217431712247625394220340442, 281682996577441287161973760085371713671, 282115813746237381833040299260145615813, 282558896547937017401777222799081735538, 283012822943315141468677715097389756358, 283423783267948476095995747028376296006, 283844190252357157297219894057323711224, 284274558912322053768122174728540110376, 284715449877386020885668887102151781632, 285114599737731617255298428834087500849, 285522916161904552479111825177242356861, 285940898804278933691586986448073540183, 286369091587705258784766130159814337817, 286756737339077293556114471126238926214, 287153277530844547742536190141471792300, 287559196901238630628938625983413158094, 287975023152840360007531855733446245024, 288351465821446684045514557033621617192, 288736538764033691640242777173223913862, 289130712057940012970126988728663217177, 289534497463472268668694304104535677912, 289900032830049343255238349412380895182, 290273941716562107270070785611355243377, 290656680121938609886908071621065562530, 291048744501745881695906199887853955225, 291403662983869064957327285408076551993, 291766705402663931453082929917726237457, 292138314302620318854140430576494251071, 292518971517858571838334903244715529625, 292863557646177635498138017808893082725, 293216025523602779559716227011500033513, 293576804443880659555717870873834815060, 293946361841810766619152953785871879746, 294280894525395039714151871896949357392, 294623074047564321844149831299192917677, 294973316303223848113884982914695485331, 295332075018236441373780557690514486271, 295656827506930138552723516558744287567, 295988998503311446299502490463981799218, 296328991670389941021306217988412291011, 296677246596994576193063366359623923469]
def qbU : List ℤ := raw_ints% [67434166887571835030318748393242701190, 67441780983753587364683599448808154461, 67450424940173107365361313601426102933, 67459069037607880772995634686141772111, 67467713276431942480697464939245593394, 67469915654358113064938803179474885251, 67476357656837786234314870513642836229, 67485002179199422737192085173257940051, 67493646843709315733455659838950877717, 67502291650741452021294450572306400537, 67510343129715120980522301635150978335, 67510936600488265603819947192238643364, 67519581693323719658450262718835648137, 67528226929440218707764198639244818003, 67536872309211702592567758150016393334, 67545517832830546615165976613854981234, 67554163500670667563686031866596012874, 67556062118034421004613828634147538620, 67562809312924411780195293629487518891, 67571455269965673283850700796808106024, 67580101371986769716295863089174909723, 67588747619361572611202017572244964884, 67597394012282371169381349692688936025, 67606040551123014722280529259891829737, 67607765828324774547170140036447230513, 67614687236075764289251706235139701507, 67623334067469051032725403012914030279, 67631981045631296799234667904981658319, 67640628170754720821781194331300458177, 67649275443213118164057459520083922734, 67657922863198680525071020874769977315, 67666238467833060796612167116190915592, 67666570431085181755953755488265762662, 67675218147064786280322037056777881102, 67683866011511247019010916643260026541, 67692514024616701378630368900512053681, 67701162186754881631762512488246193953, 67709810498117898426178152311673065209, 67718458959079463668031121776689387205, 67727107569831661504203340307594741422, 67732367246314730671055519364187692014, 67735756330748183756026388774030791582, 67744405242021088327227248759172735796, 67753054304024047235703296973597165947, 67761703516949092399544794639821923717, 67770352881169876314385606485731131308, 67779002396878405169982365229147812206, 67787652064448312220659385780388316255, 67796301884071578184928241187991211322, 67804951856076404602906213916694541634, 67807155983018123396432301445133076128, 67813601980790985239640480905787701175, 67822252258407263088348333665033936749, 67830902689298824527837158020572465833, 67839553273657587721866006537169439122, 67848204011857120789573828526255320537, 67856854904089317321603893544198357940, 67865505950727727457413088410788649956, 67874157151964220470659520462920322147, 67882808508172328800891067312350867443, 67891460019543897660700051734687883316, 67891740537614827474082262397596071206, 67900111686452442069285688238468205916, 67908763509089783433883239663239292620, 67917415487829419632691507964896406415, 67926067622863148523087355819508308357, 67934719914564451121405937316879362195, 67943372363125101990454896154074047188, 67952024968918565563631625134892117347, 67960677732136593364254835924175928016, 67969330653152633521499774339958850087, 67977983732158414774068195161872675127, 67987406318538415610550822512546958031, 68095608161265555429374815435350308836, 68217992914710845735666820136300857078, 68356425128785760852303898554853935666, 68513016302395444860748779709796941088, 68690158231868903440101185242052151719, 68890561098282483758765588573395564449, 69117297058042234763441499936254333581, 69373850255960118484308400234943999032, 69664174383110147650823213380407596101, 69799073442532712410201455533254970354, 69839297588215537727537628797246317901, 69879526419570638408574950201059116794, 69919759964582714348503506505885528043, 69959998251101560595434761291221160949, 69992759161305050499987826474110782518, 70000241307116095627766116942838264461, 70040489160571898884515643732573883747, 70080741839416988039152361002299283496, 70120999371647628746439218329368399255, 70161261785125751861635535611255463853, 70201529107853144082806929586812529150, 70241801367788875847209667203314008504, 70282078592895104819820102337662115579, 70322360811182912811449910310486565679, 70362648050529609890407678234702922271, 70364707482273179932051080708407216323, 70402940338953092172604282130033207146, 70443237704429156937476944106891850468, 70483540174937333148836570195043137476, 70523847778506746362081799458742044562, 70564160543033306578931083148591534832, 70604478496554237969212643044733670239, 70644801667065278056494107956684342589, 70685130082566536087699739809655740696, 70725463771108386746188719166455275887, 70765802760608538596430476102959872336, 70785825387325939294747256679979408933, 70806147079126740522935492712716088151, 70846496754681861832045422142188929799, 70886851815297779285675168445184077258, 70927212289049300436027969303553337166, 70967578203879109502962036071055531319, 71007949587872655317606391416048330012, 71048326469075109182667588094905878231, 71088708875583103029403394244404707162, 71129096835361574964902044907338081304, 71169490376518805868209012553745435670, 71209889527123277180940688355274461001, 71250294315249611587892379066635235291, 71262727696289182224943177371409718073, 71290704769024551723520013321889242010, 71331120916443677457225756377401319603, 71371542785646632618645254950523188218, 71411970404733854851447247212652185766, 71433670826026433520887240553900172209, 71452403801812547235765331181068050687, 71492843005042688895726290198802666293, 71533288042453620851875905690246724880, 71573738942219467671725211537335956303, 71604717563006728199843385857957858701, 71614195732475736215541142796901850402, 71654658441365319012348752058312465849, 71695127097084537581052794532790892925, 71735601727699593673533110893114372219, 71775870034704194346541704216650915631, 71776082361422190650548167316425894826, 71816569026425997942736458650704235994, 71857061750892686991112892789764952545, 71897560563058008093604338512069330758, 71938065491028103856345876843587480843, 71947130371123126484679583627871878021, 71978576563055335099524730584406771293, 72019093807354607850831185652757468022, 72059617252149442660593477365168109611, 72100146925718085784864094306825123281, 72118500704781118183456247137327310721, 72140682856209681656054352477654673146, 72181225071920308128264018159700969885, 72289983170966751426998909903835746866, 72461579907720460486116793198188704532, 72633293056274642269941203323803093625, 72805124761032872909122274973621280403, 72977077169824420844692722804573440232, 73149152433881209797034661665249130601, 73321352708275309724142634910099966154, 73493680151940538550779122292041514078, 73666136927692619791516846304667928028, 73838725202664754161751694540209196609, 74011447148280035781744045592133342741, 74184304940500525780920591392388944107, 74357300759797305750005724881878666869, 74530436791583453939608328518554709547, 74703715226182403307065520763724922675, 74877138259073766765200253487861504914, 75050708090859179321473777138176970944, 75224426927692512307256779256971765244, 75398296981290544575349118670084464958, 75572320468941917159250144609533366288, 75746499613935073451779582615963865270, 75920836645518702822784486575015076633, 76095333799141107736668693008972972622, 76269993316407665702320617957780858338, 76444817445505323317816914222986005172, 76619808441157753819915581702055770140, 76794968564860281437723122018106660588, 76970300084831653005390457033443949588, 77145805276434420468869121344814132967, 77321486422171150682405299503987945452, 77497345811678296073614065256632975751, 77673385742142910116844024046161186308, 77849608518246428409048324355548289194, 78026016452389679495838962309182442520, 78202611864632259538102695130037502172, 78379397083103349252373111736928377186, 78556374443937301540980636048573502865, 78733546291491266643863020919156412318, 78910914978275565910637520373992850634, 79088482865357142516907115811720463717, 79266252322333014442785067116649327039, 79444225727300203544454736250234741767, 79622405467252454996663994539826540132, 79800793937997229285552557994368279661, 79979393544356036429314212622804033118, 80158206700074280145631433759998220550, 80337235828207004503677344356647200894, 80516483361022027126062004211153482113, 80695951740187059587500372900597343779, 80875643416664208061257803175293947454, 81055560851081929174510188864955095782, 81235706513669582120296306883804276884, 81416082884186327893796164443847798615, 81596692452280474441934556641245092675, 81777537717360492960277249482794067867, 81958621188750864362532454212111663662, 82139945385550967891308888546594437234, 82321512836973913560773596275439251009, 82503326082193328311973850175907355570, 82685387670475219758509427533905775972, 82867700161009975371141082529650632426, 83050266123225518519691825654610355726, 83233088136653389614725526118111411945, 83416168790785407913986926942721416076, 83599510685363442590890918004718102380, 83783116430169638872890459416769786487, 83966988645101540007440432247630614507, 84151129959941285024237916844993260822, 84335543014607492998934387267138938204, 84520230458902618997880183613352503801, 84705194952544616889372425048087130556, 84890439164888513873236715169178650587, 85075965775131057312185936170027266160, 85261777472055107579290162042285648456, 85447876953757924893445747634398172454, 85634266927812910514020795320063962052, 85820950110916498616309081936604570399, 86007929228817084944509851801236059527, 86195207015924930531146719409436896162, 86382786215404520383152514373578217061, 86570669578745012913684883363383534201, 86758859865610462098949468098149285432, 86947359843364687111536552858234145555, 87136172287077214150408325324955144222, 87325299979049948043809728923193895012, 87514745708315692668633442966170080039, 87704512270565594476478127701524498733, 87894602467539558959334859243874053207, 88085019106690019077775754218644856951, 88275765000506318408662626336393859076, 88466842966315076100435502002688393392, 88658255825532819327628071994765584527, 88850006403186377355520113883278605585, 89042097527083627107394612268911937592, 89234532027455198418905175799473665684, 89427312736087525853575586350565242726, 89620442485405553015805240844542246557, 89813924107969870367021887032089845610, 90007760435402302809801567579483565045, 90201954297564552538211929785133369564, 90396508521363633048920963015025277459, 90591425930013992137675743331953624985, 90786709341710566231978939354036547500, 90982361568542599960842979183619845137, 91178385415016444158574303492028589225, 91374783677022523521669956283803500845, 91571559140244709284301678050900711856, 91768714578477191523723646488093027787, 91966252752320855719880876399103746889, 92164176407250000734941559304008348256, 92362488271888192085305853345784256449, 92561191055850746586290845980011946078, 92760287447998006930764180107549371096, 92959780114027915663962859090096222927, 93159671694251525434870554141802239319, 93359964800902041431153676790374518193, 93560662015826309664574478431053301775, 93761765887530626217148910125565662941, 93963278928050898773941504572531659822, 94165203610124304897711218028247318638, 94367542363625300751489091110648838183, 94570297572117046761364672787258328836, 94773471568854836472156548414992422085, 94977066633097450127046869498829004081, 95181084985623257695486777569098998301, 95385528784305362243542063962777988449, 95590400119072824198569252371087044497, 95795701007116635401235188504558415625, 96001433387278610405987918754830305598, 96207599114092720343140732691668755474, 96414199951955109386645704337769509885, 96621237568348827254179235319335119801, 96828713526979971345838998493445062740, 97036629280131378125275254574388159258, 97244986161093392035945481107607907906, 97453785375525200884881816483707914593, 97663027992601816612711216851224676661, 97872714935237315731579662614242101556, 98082846970240725669089054984493729528, 98293424697293472220505785913806009527, 98504448537202491485703283125639210161, 98715918719887810479804710523027848745, 98927835270974148973349151928259953080, 99140197997829494764453323413155050552, 99353006474303532707326870299426730736, 99566260025005478684282028436990621577, 99779957707903951330137543211678289146, 99994098296076250337793087265380426662, 100208680257828756045446551503314901603, 100423701736007783128167216771872842373, 100639160525301319217107085983564774084, 100855054047928105638607051449364651425, 101071379328108475972445464330587015931, 101288132964078141318036691963483502373, 101505311098417198232327147579992651100, 101722909385830999723744623386247542514, 101940922959132465309961609620401767878, 102159346392060836439093039761822067137, 102378173659650726756024733753364312409, 102597398095209927973404921895581255496, 102817012344582081217610016031045017561, 103037008316290160889914324521975217421, 103257377127769095771564883691368803330, 103478109047871340199387011968120593270, 103699193434138123842451730079718516086, 103920618665355654953939815067082641711, 104142372068215941579654723575260504571, 104364439838512985742187955120594179916, 104586806955110881302574008662654060153, 104809457086996589269185256499881278483, 105032372491994384365352695393424413972, 105255533907310275431384560561159787409, 105478920429895185520213155069098002604, 105702509386185935954221561999070611237, 105926276190674005335516233952656072020, 106150194190943233413396606398139550756, 106374234498769318586432298132467245253, 106598365805028456531016360233245674390, 106822554177654865361575274025869888751, 107046762839506947249338535389540813083, 107270951924918579878338266082612448059, 107495078211745617294941038898477932863, 107719094827076251174544998671273009309, 107942950922294302189279668616413277014, 108166591314437804492694167533870272705, 108222460797762604690966213346876678444, 108278312095417940311014692252525409915, 108334144201803946678698677665638516814, 108389956090293966211234768048471618018, 108445746712634489299874878071880019100, 108501514998691661238453728884561215739, 108557259855585958746626876434647003772, 108612980167412092577457922349572410533, 108668674794645561504629596304979755974, 108724342573594707096869773825755248010, 108779982315837934118841108009278361556, 108835592807645629649970218472077417131, 108891172809326667120422195160991436247, 108946721054856808809597354643000342497, 109002236250893864434347362466909331697, 109057717076372009664527370797649106153, 109113162181720433990148959355498735333, 109168570188420622221967325002542944251, 109223939687949568121108493111752998857, 109279269241298344724722559518156621906, 109334557378113441327690855476938422671, 109389802596173199460895694737608552985, 109445003360249234565620330192307476591, 109500158101538799717034372372618704219, 109555265216777219224437712034155887722, 109610323067385705687965862833634606925, 109665329978594394922772731530803098765, 109720284238539757815952538862914891792, 109775184097276628255330687751340052426, 109830027766057322918756036181289980545, 109884813415993298247538153520931476016, 109939539177276710069082929534571885885, 109994203138018318178608452658136545623, 110048803343406144681659343449542970051, 110103337794245041831771905515959642824, 110157804446049305036365292573895033447, 110212201207807005046724970391638054130, 110266525940766913351991144477243557661, 110320776457188028026256676300393217384, 110374950519050350985589777024564478375, 110429045836667501107925161123218168658, 110483060067547850215925574990814012679, 110536990814632061295320622950398430230, 110590835625066520252299055808837562457, 110644591988582338541256146414369266539, 110698257336172639655260139149740495780, 110751829038143117590395524732305287230, 110805304402687794027102609946974148407, 110858680674065189947103728953572550772, 110911955031062673336259411194555549815, 110965124584830140952051748244637703444, 111018186377226452024203429501149133433, 111071137378816776680034711050584051411, 111123974486862331538847302527841003366, 111176694523242621522791537505661561654, 111229294232307527253529369854913378524, 111281770278600208083068551756275456210, 111334119244785538942830423958487152616, 111386337628936627575779993007192224967, 111438421842302558864113494042317757189, 111490368206653278715954052421683910762, 111542172951870479727205667618568257841, 111593832212888605707763481000222857975, 111645342027097111259210505537657544981, 111696698331308339782585523390488576969, 111747896958951954792658045372852435823, 111798933636609388984959072880664892966, 111849803980985989895926217321575428324, 111900503495488872389269999531032466146, 111951027566736410175250827341543691027, 112001371460938827869630723894777837125, 112051530320144285043855206297784181193, 112101499158291039917159463203473968639, 112151272857380843038019434517358898008, 112200846162963180184019002485631340267, 112250213679996050072379116471227825218, 112299369868218537252211146860124282942, 112348309037665839177804260570441442464, 112397025343474316275431768827052005353, 112445512781023264107244400502996902033, 112493765180612688424775283873593972032, 112541776201984756919284467815617576517, 112589539328626251239548751253408103513, 112637047861841676930348413435899747144, 112684294914535561215521687950155394597, 112731273404996088148562174661850035563, 112777976049908048383723035274271074996, 112824395357596388988249947886476540726, 112870523620676170435314151972751794381, 112916352908695795569046159009929945864, 112961875059965734699968133468584998486, 113007081673546834213775648313386142311, 113051964100589900877440733815163268978, 113096513435594573663317273588641808880, 113140720506797173981939771706459270165, 113184575866630768423385012660620906450, 113228069781512692316925189427029425965, 113271192221226604540573494819373496588, 113313932847826711555050396963133496806, 113356281004038662791501763273251957242, 113397207548040640004593641207696702656, 113437739555498353972715319840216083677, 113477866183246352663080670382983167141, 113517576252348773103048384168875099644, 113518563567943752234943621625578252741, 113519550615864185099720621738044238527, 113520537395883519235240930328887576203, 113521523907818508309769022290914606739, 113527657802278103590672653153004916391, 113533781260622703252689029022935410769, 113539894238257308140117948831069688741, 113545996690414839076768977099337293907, 113553066374963907882287981089683143237, 113560121748758361422766336329070266878, 113567162740608176779581681110769663176, 113574189279093823815888807083647376241, 113581201292220395052302123231719515164, 113588198707757180513531137304131984299, 113595181452893162770938470494351323482, 113602149454575125309413252510249046582, 113609102639164525898301622255246944784, 113616040932774123358410886427748733602, 113622964260926242561533028050994908361, 113629872548887904294293563370000778915, 113636765721330495326891664299222709178, 113643643702663385884492144782639580167, 113650506416695018367909782990988273343, 113657353786964996754335423113904758092, 113662916503276169087451466934613980269, 113668468958854003233771193708970587385, 113674011111757999909599892258208652449, 113679542919851134572480016660295203040, 113680805075014181255012135498771213935, 113682066687685115895196562478589952225, 113683327757357358393632238341679800964, 113684588283565066293433619473437959335, 113691357771131775702671866808116174378, 113698111446337251718249607670697105514, 113704849229413931665293451594395938572, 113711571040296989126317684777489854156, 113718276798292724757982247596623076595, 113724966422402773343905026873508817477, 113731639830993997841913585993476825346, 113738296942121070160615638250004797096, 113744937673197883064067469546319524431, 113751561941318487585629094991283674585, 113758169662930037573479321966827098920, 113764760754152066441078956191056464422, 113771335130450979295372394142556028424, 113777892706957651505524476531100434455, 113784433398143483515984811104032850604, 113790957118136303493980985153555335537, 113797463780398000091908120823390122594, 113803953298038711209280899312870509813, 113810425583496050133170933936452778943, 113816880548847562221868350508726420084, 113820035004157160117451431825764398084, 113823185274851976336860204768559914237, 113826331350462224374726806882385974337, 113829473220487683790552129934167069157, 113832743171989436159572403844317133736, 113836008532161661146900977478297430745, 113839269288933872453917924191953080929, 113842525430354929825800794470403160795, 113848892456525910267298758065052549580, 113855241623490710712841221899164445469, 113861572839436887966222150918956709461, 113867886012157217569682166497911243365, 113874181048737124155723770278025380806, 113880457855858196585535962531243534012, 113886716339487307814225031033141374253, 113892956405178283781547395996963775005, 113899177957762729426396995491024222590, 113905380901649831428503266774190818617, 113911565140518907188941544216328599968, 113917730577617321260725365951386638792, 113923877115454774295226164183352921767, 113930004656099312734431515457954715355, 113936113100873374908499813561125294880, 113942202350647873292773003791653164250, 113948272305540015129276015434637720556, 113954322865168642140718998316981522929, 113960353928501138843904413385243898521, 113966365393922475367991399680997527146, 113967357130086838040663866981692744382, 113968348327568395147282941143192058471, 113969338985903175112502909589283929432, 113970329104663212055403121226287171103, 113975320944270439677539213402925171438, 113980298950502476951184592041544977438, 113985263062991656304737877381737223666, 113990213221095862965802431094492732098, 113996125149972321310194901794347812169, 114002016857762577237411462117194532270, 114007888238276338720398492866915663976, 114013739184808774140968497426304814221, 114019569589849355677854938740177445619, 114025379345361846353145917805900867345, 114031168342495045000150767866988979410, 114036936471860670013985214871404773249, 114042683623246024856563743811954073339, 114048409685889755166519133061233262586, 114054114548196453967553507439875081790, 114059798098010268472073446201969575425, 114065460222331464370547005356095360591, 114071100807587858336668841414123191272, 114076719739353360989304855047795983581, 114082316902617210774537697274957380344, 114087006673944119088491361848812476026, 114091680901020811100434554519971027918, 114096339514147259079694234890261479836, 114100982443387131464191724023696610368, 114101859065334010967721126544896600555, 114102735122917403526761990409513002782, 114103610615658746959025929939068441128, 114104485543078995596535846696802894462, 114109972111778041512006682635346982004, 114115436206019736922253866707543834147, 114120877705443749049732710834155335454, 114126296489053881806197044197465105922, 114131692434946813658452783130747115524, 114137065420569961458541071892525313862, 114142415322452319168342219613402070789, 114147742016459969789112270408814803540, 114153045377529046106627372026372945407, 114158325279918863891122928317102961548, 114163581596947026059613226977265503841, 114168814201240149932401850170778740905, 114174022964471136446882986785465345503, 114179207757607463864639107936303472370, 114184368450650643911449457111286050629, 114189504912882053929390151594351465374, 114194617012604602060961856959817428795, 114199704617355156163907434982431749881, 114204767593772243898081078509547478661, 114209805807650946066962848504353208114, 114214819123813149923711656092149919951, 114219807406314761641814706038279348468, 114224770518194133812813364003640571249, 114229708321707763059566181061386732073, 114234620678081017537612823810806029416, 114239507447741226697819785131410281599, 114244368490070732167383509195618297646, 114249203663637339091715974295963213096, 114254012825949714031253624042102586253, 114258795833685166855308598072393393993, 114263552542447419553898690501387292973, 114268282806991687190096751745864178696, 114272986480984841792040773273455473899, 114277663417227760394828222670315607488, 114282313467417908446715268826867486519, 114286936482368922486586637907840699436, 114291532311775637770118241137797981256, 114296100804430872634061138154286610070, 114300641807992925322830122807749449085, 114305155169199526586019349440011528177, 114309640733637830963496782242223086218, 114314098345955503647457693265144420524, 114318527849633231764655474870433387399, 114322929087192911008627880717154484905, 114327301899972702741180769616940451371, 114331646128332285363912249021284368639, 114335961611430483347487597813726378369, 114340248187427547763950961032447374598, 114344505693265383641684881766780812327, 114348733964866823520941071566130647357, 114352932836918479824662161741838869453, 114357102143066974728875768897358795383, 114361241715704444534762183358937185338, 114365351386161688562722764016338496468, 114369430984496352809195506593693858802, 114373480339682959978002508377189674888, 114377499279403800006432966774083922639, 114381487630235802739556881573099920539, 114385445217444163213996168253504297579, 114389371865166017859913366555897430611, 114392073032125553053882623127160799130, 114394759215649438688356446915884961149, 114397430356257813692806185765455564946, 114400086394180558241345846921141903343, 114401260666142017891806124288917096105, 114402431944506914643938415330099712288, 114403600223943764331499818476382432832, 114404765499202305349331937759977402795, 114408534767051464313616611760055505550, 114412272013590415319832220887779504541, 114415977054025862044910859164072738094, 114419649702272413791163063362181000054, 114423289770851562983133952706675096865, 114426897071035908648162111022040220776, 114430471412659793279283488435736711650, 114434012604282942268000324555540376326, 114437520453004039490291260726825559970, 114440994764620877896416922942400760214, 114444435343446904240363148615334222910, 114447841992467836227297219731878202094, 114451214513161207135281837557708296549, 114454552705649404164622243313266752692, 114457856368522244031700049018586540314, 114461125298986386390785127431733569328, 114464359292690971813283580138748053839, 114467558143873363361119668167904668619, 114470721645187878700497402982502018283, 114473849587847812096158840652168302128, 114476941761457292746843315894431316015, 114479997954149538641051837060178575715, 114483017952421873541663669964177291549, 114486001541270163295715011211981757313, 114488948504027024238003346047626700796, 114491858622492391679233805754911421561, 114494731676774952842802912258829180060, 114497567445418796366867997386757830360, 114500365705248103234740082928681824107, 114503126231489825216357655358852174046, 114505848797621667600710469630891911039, 114508533175490743570192279448271223427, 114511179135164882893090141932203498477, 114513786445047208269670047834172925127, 114516354871730804493855951810547416771, 114518884180109161831960377190701284385, 114521374133234240515088612471227264637, 114523824492422725209428975705109785524, 114526235017117520054483007763677879488, 114528605464989757257014599320879062074, 114530935591803758244746330780884689275, 114533225151514738363640975139464465539, 114535473896137270072023496087621454719, 114537681575838624642009544811539272744, 114539847938810773674903661570614867224, 114541972731346492802214585181540711272, 114544055697766452898063455004258865571, 114546096580426000193443154902681117304, 114548095119646367385260168833178828566, 114550051053781491774178808415685578920, 114551964119100852991611651024884756932, 114553834049864749174701691926214053132, 114555136597073403058463753598000392996, 114556417126728838235314594397304581771, 114557675541512774453208124229264025397, 114558911743574955939047098634099629637, 114559408630833464533137243285894668889, 114559901813587902222550277851671995913, 114560391285157074600532786925010323054, 114560877038854775071005591169971335979, 114562527236924787781138572950541934425, 114564132661525079281326033326341940157, 114565693031897591281376489621773371541, 114567208065097367168682678046621391390, 114568677475894208906899148666389803856, 114570100976823900053708798342405561196, 114571478278093743493194395114092412005, 114572809087628764655528469655474402244, 114574093110981169896082559487082068629, 114575330051371456934896316759006938157, 114576519609601834038839622059611908947, 114577661484092163225057472684079122316, 114578755370797380742325921543599408798, 114579800963238197068312168438774595095, 114580797952422559522143801333203228478, 114581746026871031528825226104636055548, 114582644872542338526435704909281214359, 114583494172853347370898480306268522080, 114584293608608737027565827265467544040, 114585042858015497344175458480314445565, 114585741596616766337261656556657033658, 114586389497300765868915866831285054060, 114586986230238847652833237761780524729, 114587531462888781629709907810573333036, 114588024859937053125102591014156886488, 114588466083296417927157593132594871717, 114588854792052493328090755927458217390, 114589190642455492064586929320022897994, 114589473287871150265813795195521146637, 114589702378766550519306106021100868729, 114589877562665430030173627653740762152, 114589998484128001121554824936094635109, 114590064784710683181175968495022906595, 114590076102939926139908421959608245747, 114590032074276351285433798886604514271, 114589932331081866490040746992035244044, 114589776502588990713024322959952348684, 114589564214861859480529216511998651481, 114589295090769492191962130050195586343, 114588968749940644285796286437508895470, 114588584808741675113424605086422337260, 114588142880224907657170300108501697604, 114587642574111141716047901644573035248, 114587083496731416456018617097534529967, 114586465251014213839915613488441485363, 114585787436420516877365467268689252535, 114585049648935748400598388883292363090, 114584251480998015392564417368193815823, 114584162176619364941065789764227743331, 114584072170933574388698351259183483292, 114583981463428844776100701250060116509, 114583890053592896390545801815618968671, 114583102834572581117712269171276781363, 114582266739860292739752860664709127158, 114581381471196695929777528795624157558, 114580446727950478303798892596023056630, 114579340418153994419744052947028392154, 114578171206217921410377824758598832346, 114576938658763757779510325449402954106, 114575642338524255575258763923907000101, 114574281804359716876127730597216698227, 114572856611150431337921203547550938182, 114571366309817980970827042227369043290, 114569810447210149091306894143062013647, 114568188566127279028778972491281470466, 114566500205199525025408480167719783540, 114564744898918310472114800598010739363, 114562922177505788076010571837067954855, 114561031566951443151045094919227982342, 114559072588873627039663009902059551431, 114557044760561350870850524154495118623, 114554947594827752774656477002049005820, 114552780600057127366979387502277696034, 114550543280050183727922107352651214879, 114548235134076355675413930350156284537, 114545855656710703785704045641836443189, 114543404337891551273731054229277470324, 114540880662748879510875185811067945417, 114538284111667334035540459297120758608, 114535614160105959063766014837186362260, 114532870278666617805228901911370936181, 114530051932922301518434127526063199136, 114527158583421889763377313260208681615, 114524189685595075626135849418591274509, 114521144689763537703411026518404842377, 114518023040950661759305681614957962835, 114514824178966464638010240659786194807, 114511547538191055387613912140836174775, 114508192547665145482715600879967413105, 114504758630864011807162483621125546152, 114501245205793634672079673478497460212, 114497651684754981166126160786418816268, 114493977474445811694673557330737571595, 114490221975715097101126435675265492137, 114486384583670533607106798457983077249, 114482464687422901807674961996100181946, 114482186506746637991981990509020308831, 114481907916561980113314748185264230544, 114481628916654535970006477506894117564, 114481349506785495842338143183975595112, 114477608321952103215316330260458922823, 114473794619846821899360953148103004069, 114469907893937847089375406924573460687, 114465947633019870903043830413601003999, 114461605841382732924060587536064995479, 114457177752281971916494028374556416668, 114452662711468522667525014120443887490, 114448060058057130253693059760372687053, 114443369124662968770367864864944842933, 114438589237092630790571460268974639843, 114433719714486670390703885381418750814, 114428759868999259577194710734347133136, 114423709005946686605126026765916207090, 114418566423475444033251617253939533520, 114413331412716711547131035546737245567, 114408003257442633050443955495634370662, 114402581234226811262898622442027638048, 114397064612088523700864776566950118422, 114391452652659254211946928733924550736, 114385744609814589825162641880826123762, 114379939729846812097233236756498785214, 114374037251084208605303146288990451618, 114368036404069744502459076981786803669, 114361936411167513866771106790414198965, 114355736486747509182212222771372485737, 114349435836778928827976206329140442604, 114343033659021059301820267283964821247, 114336529142603145813399937424993315396, 114329921468221398935098045318602802111, 114323209807746324025023659805620076475, 114316393324261707669786907180578185538, 114309471171861969054653074304635957884, 114302442495698555560454846883331562534, 114295306431558207526813953611179637604, 114288062106078373138650817522614072234, 114280708636270199790773550288113987256, 114275009434056021018933085436651606008, 114269245442396942366019676949937036438, 114263416254629458187777883427508535336, 114257521460644645789769416153955159979, 114255696806263347669369667294293162478, 114253865905782035855037000486539383241, 114252028747105790197309007313227148852, 114250185318060682229652224997602267812, 114242272543251039865547377847536427024, 114234245120709153323465568992952015999, 114226102097663689448496947916596290688, 114217842510577660294045849456614172554, 114209465385394379342771398531554606229, 114200969736981452849199563314465971864, 114192354569382777359810941266060585328, 114183618875245548403546083164066851633, 114174761636078262696654996663320890558, 114165781821660315769346366798663470522, 114156678390305965187296295878734178720, 114147450288256072603673845411129103017, 114138096449947976751268484643314620858, 114128615797388918510567421770288044209, 114119007240431764286838779799728087230, 114109269676129634938688903979537472221, 114099401989017411412831741818752211255, 114089403050447069732112000089537573784, 114079271718874891373732183363421373782, 114069006839176986915969330912993536214, 114058607242942123566629465283686688701, 114048071747766899454588985682185785021, 114037399157554089893914106986195246706, 114026588261786912616687432667171136334, 114015637835832782740381277750652825909, 114004546640196086404399141410568367155, 113993313420827221935514298101263354757, 113981936908353275299459192385155529171, 113970415818392211568537761590603730702, 113958748850760820253406891857648272610, 113946934689793906800370700944817270139, 113934972003528849143432578736612745790, 113930890622681812543557964943119000320, 113926792032157083504949708414097150030, 113922676179169347932747165449288279796, 113918543010641179587843494154117399191, 113910410097377703670950448904180349211, 113902210360457036850039446792866724132, 113893943395726796685544322887656197515, 113885608795429004904414361171257131537, 113872882927538068477487732501546120716, 113860000192749490868580332037185910523, 113846959139992916528450425118349461156, 113833758299713903270782801270364533360, 113820396184215277879562270363222298706, 113806871286713825033946457998472438600, 113793182081685374161960202532184066200, 113779327023893496938902787931863253126, 113765304548738039901773357575733361975, 113751113071254937687778171360846833057, 113736750986467880454569354250687534365, 113722216668358308382090495255713532452, 113707508470219875567046064142647083434, 113692624723597647180415145741851525875, 113677563738644992071168984827168848492, 113662323803030957176728084156183147875, 113646903182299189418692938502415602718, 113631300118742412313417119388044958580, 113615512831762943695388624004926900396, 113599539516713146763397467674572110078, 113583378345257073533968624181807295413, 113567027464175706561696713151252692578, 113550484995729218597901982463536127735, 113533749036425761699308640907207449564, 113518177891069420680381925835215782830, 113502439788336007882680944987879284034, 113486533187111084480642603997685728630, 113470456526433302832522301096237153450, 113469052167883629125704514540377939493, 113467646513596192801975389008282593046, 113466239562527320849243446037527210541, 113464831313632195129158884764333996726, 113447098432393485459361507212429277344, 113429160082630967226419927691887750218, 113411014170830828491484667178497766873, 113392658573854151483252387559947560478, 113374091139293004634971456178335423878, 113355309684035954018099478549665627211, 113336311994620698818753535267800661619, 113317095825754186796050001480722793336, 113297658900660907674588506571295698377, 113277998909555828736113656428053592499, 113258113509987388733102218519852892426, 113238000325261370348519431047333832811, 113217656944777559623074184369357103415, 113197080922402565738732229066890994772, 113176269776799027102133892054922164332, 113155220989745275160717509328322154395, 113133932006455877653291476333197990657, 113112400233977814133761232205701519264, 113090623040974980637064015571055173857, 113068597756721599994047805726899018784, 113046321670878315953290801703752788184, 113023792031768912565085427760670345407, 113001006046666591034036821360017332414, 112977960879877404375840667472663401677, 112963427670867865511198740124661588264, 112948791425107022713184366425943613781, 112934051424835722044373245119424446481, 112919206945259978184276775562595621868, 112910245022647772411065335462017300746, 112901245024144474899599339276227306879, 112892206789434387302476611682097099431, 112883130157124903143950367880763930676, 112858745007093877885642481530247840404, 112834082723710916142957756935138143429, 112809140150276034874513510195380191041, 112783914079749056719938695729228506014, 112758401254943664563701770420793486127, 112732598366250647978876428354634455726, 112706502051806865050890609995375882471, 112680108895135875971475263921984035142, 112653415425289157963939076022468281936, 112626418114400052702899970441087379394, 112599113377794359179424120002667597466, 112571497571453248526127790592699655998, 112543566992090119107773388784978549307, 112515317874517836943503173063560515421, 112486746391688475292731724957109188835, 112457848651959919075863203448025373345, 112428620699094825624974037694650988704, 112399058509421284974260135246581649969, 112369157991787026905396784774344689628, 112338914984608453118616762233795460498, 112322007135968136681613684367694290152, 112304992090856018367915544654054312182, 112287869112911379860842834319826014831, 112270637457982441669607608059971479542, 112256693423726265498469286786296527632, 112242678153277076197638441726785826437, 112228591249055515071748375228223262037, 112214432310396047234120343379298678601, 112182411887486112794316181267258550553, 112150022453859526857033332745923495755, 112117259314779697068024871721363665209, 112084117691307026371417158389538134379, 112050592719956653197209549784536488940, 112016679449088484506891236033505864282, 111982372838487968258584440373753156055, 111947667755600452934040828315990507901, 111912558975027848551995610999929595813, 111877041174815481606423304806519070818, 111841108934989029549691041379721779138, 111804756734746481325701157364213242101, 111767978950899694350278870006833885155, 111730769853797221058350443866309198044, 111693123606519014998573499376814288236, 111655034260386035861910273176881181244, 111624333192135278358447204497380745011, 111593343269890760129807468863338601491, 111562061317016749271583504115138391318, 111530484107601313783791885696981165348, 111522422780323411223902872670965488256, 111514342171067966027889428618682402659, 111506242225557414021782930517007789064, 111498122889055666772564107298872612248, 111457724749028564726214157104309943221, 111416845332304917596363477710175178040, 111375477832938711692093998679165375473, 111333615308472639482350041836348789400, 111291250678412113759017479324339814523, 111248376718527898450418941316983285910, 111204986059143370787355187045423450626, 111161071179143260035406849670991183723, 111116624404056636311254314387169068626, 111071637899750515346755597174319401435, 111026103670289314456424007481940923238, 110980013551290130250883135503789952720, 110933359207537470103992833651801531085, 110886132125974846202211596389726396352, 110838323613051440250267403965333358087, 110789924787322254811737368185572175241, 110768707677371020512061179669599116950, 110747376638940580761590944281730674464, 110725930909266220016574960334311956952, 110704369718072224076892391712315049210, 110676137392164879664424014780830927085, 110647706487635237627435204625242827122, 110619075250870678911181281249988032227, 110590241906051912668024759465106996306, 110538751389313600228213445664071141947, 110486613044112368181917720368934737864, 110433816524310490478069785923961309221, 110380351247856032550613897288224579907, 110326206392344608137109543417582440495, 110271370885140911193299279578841486613, 110215833398470877129372166927671510944, 110159582338916956446738605449492747901, 110102605841993227490352269358729813793, 110044891760959952250009520691057747365, 109986427660828851701509848263414983877, 109927200806436607892653061432921914121, 109895188346801614509436357591900252577, 109862951687955435938454760661335020968, 109830488768169636164913007361646676655, 109797797497260882162973308846283329431, 109769212558232044780035324004401445708, 109740452306135999024259556939413265800, 109711515320527195224838126820477057084, 109682400164205342033302247850636064464, 109619157382698746218207337855902972296, 109555068608450863030416209641909889600, 109490118728891308690045047400109738601, 109424292243739670568771875155456873875, 109357573255128981644333146704565533513, 109289945450804393263595088531188633509, 109221392093201668473689809273956031241, 109151896001368880329479194344306937359, 109081439538883676763945145240538920748, 109010004594368087344892821047000166629, 108937572568113531852571406068731407726, 108864124351042646507969228997826750523, 108852170113527705024904591432283323219, 108840188795456789671502177935453130117, 108828180312980084537513248785974672387, 108816144581422721041511618341632696475, 108792519892940936715966763173442466198, 108768789951823035300208539740206078868, 108744954111464570315128650352342916576, 108721011719119211646404152470728932341, 108692010539416298885926445055959610911, 108662852438053498309443234936449580927, 108633536239047633867865296451451906888, 108604060753801404056472425603912197813, 108593021389373328547386783141031023020, 108581959617157974738772729279789223067, 108570875374976832889492266107038882353, 108559768598497992107933146099317145560, 108541058310631906333035150977376351052, 108522283939732206191171211655114929286, 108503445181315487577281132700983450191, 108484541726895351724433996731120338022, 108454251527329789554481216845953278630, 108423794634830999698771618017378727864, 108393169767327665387114901009529491751, 108362375628615495677453957090378681353, 108331410908151733512763569999609804747, 108300274280845936055628749896502004144, 108268964406846946050481034879052127757, 108237479931325970891980982059114779016, 108205819484255683945990735616130019912, 108173981680185260474983469330766640300, 108141965118011258260514557105641535239, 108109768380744250689383873757469173017, 108077390035271117675121339077360812904, 108044828632112897320117419496183508047, 108012082705178098683699172756773449112, 107979150771511373405233028688629206183, 107946031331037441236336674631309149755, 107912722866300161759825460128088013507, 107879223842196641712323357103405221312, 107845532705706264379648560035450214683, 107825416925864914886110580235505264461, 107805232395217382877839037514169244264, 107784978779567144986712840238402265906, 107764655740192493315350530968330025024, 107750744659235996000142817216007018245, 107736800970237868441179450492122380227, 107722824565033065895905326674543086186, 107708815332728497259543279513226249775, 107674139692241641286816361367845160356, 107639262229127817968320898385750697078, 107604181256903334441878435010592684811, 107568895068801533341819595536791736148, 107533401937450478379972840869263476041, 107497700114544243093844375466294342355, 107461787830507650108997674950079933339, 107425663294154303998929493593428933183, 107389324692337756425411526300656157335, 107352770189595637700378544190417682091, 107315997927786584221850513759093153861, 107279006025719786395725070305383279892, 107241792578776976656996932198781060901, 107204355658526672042253858098396763096, 107166693312330480434127981855140096862, 107128803562941274091461405067492240784, 107090684408093028389730227162950457575, 107052333820082117817944139104398843703, 107013749745339855203697147538228702513, 106974930103996053859889114303725444913, 106935872789433385857156324461612977616, 106896575667832302917205032540987076287, 106857036577706279485656522492090262634, 106817253329427130369950133802808462304, 106777223704740147909202452984826374220, 106736945456268795969185268522632557126, 106696416307008690116850474274404094439, 106655633949810585114755551204310196735, 106653835556310619469006646732248276543, 106652036668258176962963467196588499500, 106650237286762898809016929184277385054, 106648437410314647881288297232750165318, 106609165510916786514627845227692687466, 106569657583086929339781759998766033767, 106529911527136120932180896663025108044, 106489925213672173087317330247060202311, 106447841116837897221555460857957193534, 106405489305715996048411942962240085230, 106362867246680834429705628877253599709, 106319972371393668663911920014284949774, 106276802076172644819886123352038691826, 106233353721348495079945977585278340158, 106189624630605541249767760604583196767, 106145612090307602079589039395125945139, 106101313348808388068295771714797892725, 106056725615745953969989447781699508440, 106011846061320765271581783380886711103, 105966671815556920438918349092827294806, 105921199967546055715976293359819284475, 105875427564673443683871719885613596222, 105829351611825780619721277374876060111, 105782969070580140914660605919429326217, 105736276858373559389158526313612476246, 105689271847652684254544486375218193411, 105641950865002924683420105882014993186, 105594310690256497437983106014180425704, 105564041288839833568143036643782766706, 105533642300499033489464009885940551288, 105503112882931323347463398401722081576, 105472452185891767435494683748508698426, 105454529827612870950742249667842515184, 105436562455093948141895703800442247340, 105418549896436355390410796111098348072, 105400491978789989517693083789148954018, 105351205839454397758237056065783307557, 105301580152430578389695558392178190144, 105251611343396417919947635449033528591, 105201295783302810404640954293611476789, 105150629787261372177854901101359093710, 105099609613403841923625323028250469821, 105048231461712297539230766456727220451, 104996491472819290001837451136321707156, 104944385726776961919758530362292002292, 104891910241794184567843103733952951880, 104839060972940711909859413358485102787, 104785833810817313332326632888112469663, 104732224580190808483703352200163672675, 104678229038592887656045561000371517829, 104623842874881559485135171457589550662, 104569061707764024297396171469356310620, 104513881084279726110966779247150142818, 104458296478242289012688215767881333972, 104402303288638994286125837787595464587, 104345896837986403156393735208489742002, 104319933674866020258347291869192970466, 104293882434394255368598816500159464830, 104267742652948813689304843631265342739, 104241513859677989326622413099631721915, 104210336159303301422853782302354968017, 104179032166268772104836290586685040836, 104147601083484834171597776796842636332, 104116042102793780493386483511483131392, 104057496387224738299299031429907755702, 103998507641832640839263368988487000222, 103939070603793711762174336405886851720, 103879179918893357007816444272255333508, 103818830139414598566107332051271110585, 103758015721965308681615102173745040821, 103696731025242104582200796888670285504, 103634970307728675985213157677284393458, 103572727725326225663652768874345570097, 103509997328913607016557491944577239493, 103446773061834641647727481717315525151, 103383048757309994165872239916694999257, 103318818135770870513329544526882684446, 103254074802111689829612407596128006398, 103188812242858757862968243549057273423, 103123023823251841942350648194158648799, 103082639713917708751893903025479655210, 103042055939533915507813848393033865889, 103001270926839364884534573860298839455, 102960283083350285959235766481854927473, 102933957465470538768059519188063028708, 102907547770523333251227353625999517211, 102881053569701460188964166863294691796, 102854474429908232302689154104183878979, 102785952726138449358472015388526045152, 102716862631184236680040303856420064875, 102647196571531135059392858936275607325, 102576946825475593087444767097977463644, 102506105519258592998077714921938020910, 102434664623072547268858230464379051061, 102362615946936448619154512113859385946, 102289951136434022643454974734869312557, 102216661668309386414796336632967432852, 102142738845914457231628131046152195490, 102068173794502082450904737460813307941, 101992957456358573185003103343851549262, 101917080585769020614875900290363943205, 101840533743808452797138212970043191869, 101763307292951551059898521951841548851, 101685391391493287257951943535521512697, 101672388501820314744229568755939761525, 101659366285096839655979392861211261930, 101646324695846601305255086158582226638, 101633263687175556862261358602721210458, 101567357085089255729035131275377196494, 101500953209708579645033996801738230789, 101434045921983007073933524245930787991, 101366628969949023924870556462815584852, 101285110627506798699224723676058437524, 101202839158083877288349089537225952812, 101119803116823219715059965052759308368, 101035990802194275212776430901294196726, 100951390248297975133270353664461272495, 100865989216881398111291774685891935526, 100779775189048857070102669952642538050, 100692735356655446147286785859321064712, 100604856613368330076233145955915394153, 100516125545380255882284070406783519572, 100426528421758913607083706838085633867, 100336051184414865558803820435314739682, 100318289685892411906176816206354668710, 100300494009969857043897838885627485064, 100282664047603897311546523749619106649, 100264799687773545496787352348879041143, 100190761760180846541060394928643297460, 100116129155358774124913700925183851323, 100040893906989973129993400233786289133, 99965047889450801727224906787862770062, 99869947007388946120109028307627418604, 99773874178089866230434252743975916502, 99676812736320906404748758088678053307, 99578745593281068331542991885002452216, 99479655222176383168452938059145295780, 99379523643176016940682764068577908345, 99278332407716902655472959756581374124, 99176062582122719246945177771125225231, 99097784058988579414047199898082619211, 99018865547014392124350982422430305405, 98939298197563486106957012679716710576, 98859072980622642775028210038428712571, 98833357376270150362286430017538937898, 98807573672580764433563045954277972338, 98781721564888400413887897121635185778, 98755800746514296309187882492092815129, 98647835745171698995256249319008516245, 98538667350886980098457929972552816545, 98428272709699782633561984301900415309, 98316628321930291292248558881865692543, 98203710017684661418928473223847958830, 98089492931187308138564804673781592873, 97973951473871900091070641257968498142, 97857059306158231525848169553411007480, 97749581636238478785167374017733813661, 97640943944481238248464889457650547298, 97531124688979205273634058812749729010, 97420101729701897839875682303136608565, 97408951876612967748661311204557496001, 97397789777318489335334714733617473253, 97386615410736491275934632009520904315, 97375428753756424803139817350286032627, 97251359496638994025899285224799790531, 97125763953455935542723622783702185892, 96998609609074837075791273597482197221, 96869862913648929944968235210531725326, 96739489238306100660130050245679671052, 96607452828437701938058309920753444890, 96473716754429198250199753577152927995, 96338242859662398928978500306137740191, 96242941963336896250679705009653603083, 96146767135459563017071929505772879671, 96049704392347585316476972594371838906, 95951739414023646567782776185064445727, 95908610674650770780066966114911610219, 95865305341011183726185012780658159100, 95821822152232110694132208595587688579, 95778159831751956674383460499285035786, 95633377514791419464095728872118968566, 95486599365120845734958690965188758483, 95337776909428391991611365957231739349, 95186859907719637113030495178685979427, 95033796266426126876128240346342734477, 94878531946096194624007994301289442647, 94721010863256791492235105866580653940, 94561174785998103677332777362211566332, 94535391502970477407050768754209312734, 94509547200761324996789043281062161751, 94483641627352766970803062650259537986, 94457674526569431144604140443637917605, 94320268073292744455294233696023768376, 94181119013811485486523595478313505980, 94040187979903391432708897263540361990, 93897434263977580060414715532947375117, 93725066332349667263856660292698606716, 93549982126164961316752851525540388381, 93372104808386038925058560343566304652, 93191354262727364872105179601439889557, 93129391867354104677936202779456456048, 93067086114930329772748185847867727474, 93004433605172242809854002668778422481, 92941430884409878486631406820000533531, 92817628579489713964573697129143397853, 92692456289174513313562923171453623273, 92565886703244452763445526357092674627, 92437891689239238338561807665091020267, 92241444404581454095674223479244313034, 92041562668961758340874529848176972587, 91838137229913136276503674818000950886, 91631053569505443886603465455104729287, 91575289841726200753911776739383183980, 91519256002649415749202319778899797389, 91462949691861635404378356232839945476, 91406368504350071111618897734838394082, 91248979664012755872862515620546282828, 91089432036968134894586978864713680699, 90927671518087274969626983562090763046, 90763641937175140123197591340226349077, 90543121434141239480238811082152974398, 90318388764091464886793285921804258662, 90089295447570187514173616490284484696, 89855685025090678310218541822445919009, 89848496935350124996208120188703306986, 89841304493892335726932562870318447645, 89834107703704480517421179724212680917, 89826906552187980741450166456335353675, 89580680418084576595538828808936803815, 89329268539951488953051227652829502312, 89072467622206922937438643251188899884, 88810062200345263648061135075239065208, 88682712012452268152887489598052975436, 88554005846797155589212273711635120484, 88423916914014674411345217026967225801, 88292417623684575479958432893524631618, 88146894771022797398952219569388356187, 87999611177710903950719767543915699511, 87850527125585522813598209079249443227, 87699601537524620791143885570274421365, 87461786738207178960543170973312110958, 87219274091822483968212910811496564439, 86971888619568888695540746630199795848, 86719445367765174224846377847056096189, 86659594731717944167852139825784008782, 86599453614142486001943185215932455775, 86539019384627688305808225627951927330, 86478289371641504107687952598817927630, 86156802156723954701084416625303700912, 85826800035818060573490052308298065825, 85487851668759532782987175283526587905, 85139491991841012172070371348601607434, 85135531354608580380281264564101060457, 85131569471078800777604584012960170071, 85127606340515108484261078132569836144, 85123641956458052434248082563170669223, 84760831532810065380370820283234441792, 84387295087770707126321430421256000029, 84002419314616898019630275049203484733, 83605536510989407406958807914280648852, 83592953281593643896833260744722083545, 83580357637927763338219905844306316629, 83567749556780957347602196053412886525, 83555129008401442792230608519619539182, 83176538154697667314776506626123368882, 82786417352075894706645082734224761199, 82384080794339345487853116846958797122, 81968779175029570173952770311806626741, 81590056142497129713920842008129056222, 81199932841920316039518043809758668245, 80797733563845393570224169748756639445, 80382720178692925480365590093048177442, 80004387679100699225060545761891826515, 79614792038154870807258876566846042871, 79213267921451349644152389292834993898, 78799088642461724022389375128147376200, 78421636309395073291281215899747742731, 78033064664454654985965240277203290615, 77632718976806878864954649359477292659, 77219884244014724493385622940376476171, 76843769661843540069362964449794317096, 76456685579616947480592667575989958642, 76057988075118093453524472732442921577, 75646974034358991038195889867707938659, 75272623764594305315937480202755419743, 74887459150549951563696243235595507859, 74490847220347344681856589344671811512, 74082096918569045310270933360665069540, 73709907622815039528412192199833264332, 73327063803736796213538483318409545947, 72932943596574073719001305006496933331, 72526868142431806636983003098821054621, 72157207619122273507971933561374864640, 71777056498287788666146459041117865373, 71385804132092693458456231505527000781, 70982783934135808299870757434378801401, 70615992268965602834603272021428301236, 70238877482201176060152430243352937110, 69850840173146161066272970838078577100, 69451226172366859768185072686395188162, 69087616859698269145034699076299201266, 68713854873041686292740619403059758216, 68329352164112485395003167202554314411, 67933467002570391786321675061807430314, 67573328001576479887455549684373449942, 67203209303648642275832272846911967855, 66822534252181102211620864252018615945, 66430673541029499557693255726946852457, 66074268450193466121309114696793966561, 65708058691113462959418218590603993618, 65331478965550090434490820882423058000, 64943912489891979887163691471754406625, 64591481580616600001104252206623039298, 64229422677878993836965445919415128246, 63857181831666215229325680344786165760, 63474154723143392620761648220139347869, 63125916094632777369552198567648957630, 62768227340570897327754101341675256473, 62400545858054427936220720684776203533, 62022279761316073174437367613066582458, 61678430403606961801190970404053597216, 61325309633143497055905460994840955733, 60962386153356523706857202675319473636, 60589080425858650978035404658104104086, 60249797226710817515720411482701448645, 59901421784670586139371741842997165442, 59543434090231964652032361082565211823, 59175266960565100921494592345393354991, 58840707714239602363495213090174367257, 58497235643264465606867753939649080491, 58144341882301684086364619531234072768, 57781471442014220138451295482371672005, 57451775978879554816532901527311008931, 57113346899243654178754449439275309976, 56765686531508859440459755872105206429, 56408251980200004163346937053031992987, 56083543018922241750400213541489303497, 55750279290517701375419651803271668920, 55407974084423483471048859536124517166, 55056096643036253134625496682462073237, 54736480737712944690828092135027265280, 54408488315514639398513532932439052724, 54071643516434732996317717965691294651, 53725427506686638086830068294522198374, 53410996122368700663082763274121233388, 53088365531623287164622441393746871587, 52757070662587362062484330623502832635, 52416604478671452706747892886132412905, 52107434778630804691069545210516130603, 51790242008334725151539885679326424855, 51464571907987205706086683762181058681, 51129928953121643684674820696533628542, 50826084595302455382916785731251423605, 50514392068932955823644684985388880422, 50194407667611164457843302557037803797, 49865647368199642746542231149512544282, 49567179456933905030438059559711206454, 49261036802193865877520981641182084632, 48946786116738837847052695391475768736, 48623954726210456057961155117462964144, 48330902475608069433339647204171978259, 48030347364290107569415338435643032770, 47721866184473278681043876076294529965, 47404997549476474726037372751379738381, 47117389254442133572400192511534537276, 46822448107459099796081677868612773956, 46519761012594287005679808309910959339, 46208877618443145786421325406428823384, 45926731219009656301191242570082523692, 45637420058171350277235511552676664284, 45340540999882002133916526044721930708, 45035654558998158872568166122868839785, 44758978476046498328368115226243496762, 44475303551302272598241900776779376480, 44184236583477724651198207249839531280, 43885348925354042771033259073603507300, 43614142565897142585478060657604463430, 43336101263095361236980836513316702302, 43050841474611118077150075960196993207, 42757945084941824869956435085699778208, 42492199479520205980303380554880734827, 42219780753577232932556410375590172424, 41940314702119408204962358804019304803, 41653393384588843767307511146295835806, 41393092118849635009621848105839468503, 41126277087538007804251765471505918236, 40852583403459410877346209770221116275, 40571613278869165203762215417937291341, 40316732825984334768805166966223354611, 40055495365517244765698541077974359417, 39787545571275941297027803862880247828, 39512495421224473848237521638759730736, 39263005682066426782904226284336287129, 39007313423724392937663853480076501221, 38745072111723134655623645184979599860, 38475903948561887943622213303205792422]
def wU : List ℤ := raw_ints% [-79228162984800397561, -264305151717294126262, -1141044003307095325664, -4988664506412018903099875, -7760965283411029218272540, -11154033533062428806004291, -22299018734543015497804812, -30102753757178129514692314, -34124620917591850576084234, -35953871643568486227110877, -19388833778690548704340909, -21931950456341797061486994, -42165429738501078944188162, -44093577652748795569872597, -45731024918955527938445574, -47170637006116161185498224, -29270136594185585747889258, -24487670354019852541874980, -44139043843271905065218126, -50450572668084022802340143, -51302913365338980688914239, -52047918916508650388889578, -52712401716510348052808509, -31844200743036652957927157, -26779957243598750578778238, -48470250393981436616449148, -54257705519971475771813323, -54660999132677908524306829, -55012811631955588720072429, -55323529592287334736829080, -54515251796332699560958926, -27865071709809985759791573, -29044060298759065570257379, -56023197936383234196506119, -56206128158811491773634624, -56352851586124673477880471, -56477517179809419888241959, -56580324911749104640922530, -56663782511758522638105764, -45606323910281927322306377, -28378707177386979873971248, -39520367727464235386688948, -56809640054478443458806674, -56830563578497425365399162, -56837430124926992046254915, -56833018463127509405717567, -56817903868790410079473801, -56793430923069709115070613, -56758031225250959403837900, -35594967352193873562959260, -28348030666504569038439090, -49442606150210259099648739, -56611800200970728234062891, -56548563054261965024744195, -56479890300975303614550081, -56405850948840703764626825, -56326955702596765498337100, -56243323325259803031476849, -56157428429272483619663468, -56057049357440934938369709, -28922460834981830935281473, -27967571402651985608526430, -54958101891657042562343543, -55773884733806738925473389, -55669860611880748532289074, -55565916114258557863504308, -55460577200967834707722480, -55355290340580192565801850, -55250327840291810196708831, -55158328018205696990261444, -55024657747656913090715243, -57722952606806103141732422, -368022422809588061536035452, -707710093751244132549863711, -773491994466874834110721485, -842150636583883347475626211, -913951730603141991160290888, -989337182378728655314962009, -1068705756762325398516608137, -1152688761186790966989076995, -1240487657849615424978172899, -929483366065332546751934317, -371637969524556678530545473, -168918920350172066729767668, -167993345575831086504511119, -166990765226161518487247055, -150643174125197796682806700, -82760792198146663941910468, -97658382656762859501569274, -164108532520807230167645198, -163167327772928934489558754, -162251360997913121008514339, -161350264239895272774886422, -160465136235039663000588368, -159594925863307972338745746, -158742903980180865288971433, -157887243543668681280939164, -82757783587885479131613514, -78342819479341469128894094, -152244156470934448698801767, -155466841941557656533167030, -154678650782536394817289934, -153906824359035969593129708, -153147144088290092178717857, -152399855815288504409688011, -151664280871587078485834669, -150942107133970042594827454, -150220429523109617523909761, -111978017531333458501095458, -74590024074614696740081665, -111795526866753440596572616, -148164764514363168536755246, -147487297486098869844482547, -146828777873012386167286388, -146179108917241097527302084, -145539272097268059631854613, -144908824448434024461921214, -144287619398637470136766402, -143675142994785114256211203, -143073293860574724576982751, -142468888508913793297727414, -92890535438774755695312023, -70802977146607150367397966, -119510939125574728978263900, -140747592810169638911610039, -140173287663733567029795006, -107361858335807489961595974, -69674440180336998617294170, -101665310475536003615196831, -138544540521332358577678520, -138002290455814633058313194, -121416641067423547772916330, -68607656021142089841060777, -84415224873303055728514802, -136453208736629738117151116, -135950591925819855118262136, -135057468610896634211844287, -67627483535125023965837492, -67737638728443593137787009, -134433748066925312474066937, -133995786111572642702810596, -133506868325511809601462172, -81510547938569455243489686, -66411011468442531208882740, -117712742828817941660665777, -132133126849969391344142724, -131673595661069413543053779, -95403745386375153537588646, -65502147815150957022681194, -101164977812664972411769514, -239518223756718279079947897, -445629225568991301494059407, -539255411852047622552005635, -532209983996865696373839867, -525575751654453655000618677, -519230881004128154757790177, -513167807420115569888195709, -507366025940781967185743096, -501809182526408513106769139, -496482093495699985579083400, -491370937970992664082133874, -486463048636675886789157035, -481746794164598181123387853, -477211471067624789505517129, -472847211081915140122026743, -468644898848861505717576590, -464596100213601502350644789, -460692998842487701553209633, -456928339891863748137666927, -453295379381268212909375940, -449787838954153528345632409, -446399866897629800073872927, -443126001459825344909090883, -439961138049427215146471866, -436900501109683338957252532, -433939617180827105556585437, -431074291290084795733020558, -428300585876984227891599547, -425614800352488707975353160, -423013454144170150718016176, -420493270850576482683947887, -418051162554055371277653382, -415684216906563658221318743, -413389685403899237804352205, -411164971184563957224122937, -409007619363927732440312533, -406915307606077152983667706, -404885837012576738703954569, -402917124595793456213920864, -401007195593764909363657401, -399154176973489974486965459, -397356290934219435647724182, -395611849203028249734261957, -393919247964213115432130974, -392276962234092901303278991, -390683541582687844606827872, -389137606409995891013454901, -387637843192302915517368926, -386183001075371714089893265, -384771888546859158317849008]
def eaU : List ℤ := raw_ints% [-30308374422026199349131954132341526722, -30301220640100753906299537885034325418, -30293097720455628336003090201546841577, -30284973032245097060704773350907249424, -30276846574685197753408118613608495443, -30274775855369227467965319641766021527, -30268718347162201002352538687797896780, -30260588348891298768279246139286065636, -30252456579257989649063000559722358452, -30244323037476618626507395415482716018, -30236746259932253050970273206777178971, -30236187722931911099040170836776493424, -30228050634837363800458926724237475617, -30219911772576927718334297796326291076, -30211771135363250066990998883143307096, -30203628722579506209399407790943908803, -30195484533437492566540488311401310335, -30193695822733303946987931944438177023, -30187338567319607660702784042349117757, -30179190823436795843243195369726357131, -30171041301170677577343054010902255731, -30162889999731343866039951687205593743, -30154736918499635892633441229380216851, -30146582056684790030726126451394909853, -30144954689038416213780166634996322656, -30138425413666866960606621576647270526, -30130266988697083552959018966400965303, -30122106781026209529397507700198772913, -30113944790033132517164139129006687030, -30105781014924946695460168675194677767, -30097615455079756120356877930093108540, -30089761668533819982530820954739715211, -30089448109703795838574975010293104333, -30081278978174385103601976652383101643, -30073108059696898537601941776119362378, -30064935353647869357686539582318832216, -30056760859231810466936124939335383562, -30048584575824467809909865751105974368, -30040406502629491273620807932776390216, -30032226639021838291508895044708334137, -30027251225998239324974193310133847068, -30024044984204294435074097078759064393, -30015861537551027385674827957504061554, -30007676298263957097384425707196950468, -29999489265716460256116359307326070301, -29991300439109589894130347671338073884, -29983109817815930456124846908643586562, -29974917401035666745679881460515758442, -29966723188140589718096616514445493090, -29958527178373048408353142094627324091, -29956438462760288324842658345485933463, -29950329370974937723467484284701102271, -29942129765316856039013718518065299952, -29933928360596811853014457618837145708, -29925725156184606920600767287372522436, -29917520151277376917479454400213230819, -29909313345244125721669580016412490909, -29901104737281114868469759540829051100, -29892894326756549099680650069555595760, -29884682112865814489589816183177629661, -29876468094976315382230067046500459079, -29876201734534226014484583563985533698, -29868252272282561067758827011987308688, -29860034644151154228442913272482627460, -29851815209775726044668518850283632142, -29843593968522076270483954188439968026, -29835370919582956648335301060458325162, -29827146062323362735139791693757793268, -29818919395935165504700925240558907656, -29810690919782555045426526274890153419, -29802460633056520229235630297506764245, -29794228535120444402176850155142059492, -29785262477619244386924147424747057830, -29682161722192255393550561514631807633, -29565232654547672378677358495210878432, -29432568441411300409866296137488308814, -29281984339161481611994967133680339512, -29110972865383220560744355505829590375, -28916650492052278522818837831437956349, -28695693899266760892846094125927735891, -28444263275911591615535573197265518282, -28157909409895245356796665963427525285, -28024191217761630473782943864076152251, -27984237315584032360968678731292311355, -27944241072281905216644487583887782895, -27904202406202992360295469654579924225, -27864121235600688021119467867789887671, -27831460309059133451782806170210474885, -27823997478360603652829604619756745586, -27783831052181366706835869903023180840, -27743621874528345248962457463230944412, -27703369862587078026295289814997510235, -27663074933445126116526386489582160414, -27622737003817166497959587158691943931, -27582355990226738148338844283216718818, -27541931808959704247001129891642612423, -27501464376017416886168769305053081577, -27460953607299526058873366710582249514, -27458881719448890134990022135443867471, -27420399418327585779282955987921775515, -27379801724427756336615623785705112248, -27339160440684001145961055697923179543, -27298475481890983122951735511473691074, -27257746762737839976493514326512602405, -27216974197530287953038533991243739968, -27176157700374289190362491170300914691, -27135297185128980227119321663172426396, -27094392565359297005740308635677843443, -27053443754520725553918838099883581034, -27033104008548469273796081619703474052, -27012450665679888200377337471362789919, -26971413211699185090447304875051135700, -26930331305189451309866124387305610415, -26889204858462307425256508797434411777, -26848033783715894757902718298419372090, -26806817992753928687778103367490268425, -26765557397171323511877927814441522811, -26724251908259683736721968963951791541, -26682901437193833734086802266272047427, -26641505894749633481546353698369548140, -26600065191490396786465318517671997316, -26558579237719052063648271141019424450, -26545805211280250875679847634135773065, -26517047943429990872263385306242515876, -26475471218496599037681073652660963674, -26433848972387511193374091859343034271, -26392181114354029179298588235316274853, -26369798579819095957929022406063494955, -26350467553382002606573713487640773946, -26308708198143393970308548209783343474, -26266902957184820786136106215205155766, -26225051738642232877915449693491004942, -26192973686371697862198444481798577544, -26183154450429340474772317619347761744, -26141211000189211297494796647853248468, -26099221295245548931976161428841160034, -26057185242792255656001320510532818109, -26015323583284724181412635694657881601, -26015102749606516167330330379095710240, -25972973722238245029979183323930800453, -25930798066961396955105816003777722156, -25888575689724955056798569941227647939, -25846306496343524173655129589641952791, -25836841235932630508953866442308971755, -25803990392208804476605187940658948833, -25761627282480068043312071311888860827, -25719217072035178942719683017302612569, -25676759665421287930210905514899813745, -25657519521465897631328567124196853321, -25634254967046466199547722276360476971, -25591702880889552049060620628531493122, -25477351227244009996750150925824706133, -25296329049527112602073006251984715543, -25114445591652613074625777911023541774, -24931693362662684428556251626584201084, -24748064775607976021000345482838316958, -24563552146112330704349657073352979332, -24378147690409841129740306473471147888, -24191843523788563740788356490175031042, -24004631659001963501712087090255056386, -23816504004191906765735959956102241224, -23627452361272751312110947748593767040, -23437468423975283856296616052041449960, -23246543776155217925351841667095908603, -23054669889550131391401153081026344091, -22861838122003160707807174982668652296, -22668039715336258298126213624056031288, -22473265793489656866638054610202169540, -22277507360094924693618524432525696783, -22080755296467331515003277303191310085, -21883000359554237743582230397028415437, -21684233179357160741382137717541859066, -21484444256830021049225945780933692029, -21283623961407011893107135584493037214, -21081762528798651067763744058969800390, -20878850058192994612174458206599891498, -20674876509938024542429951722050800464, -20469831702840977869430245332442107273, -20263705311736328217985423215871017189, -20056486864441079984983281408982411263, -19848165739139801670335994441502789121, -19638731161709066614720014189600631858, -19428172202469812688693835391769489666, -19216477773428617337056828240132912172, -19003636625111005747495249230995683666, -18789637343662704338208207226514044707, -18574468347303628897037107202186215409, -18358117883274447559198465420482833211, -18140574024359120353053901677043094761, -17921824665673875948349548709696404181, -17701857520786940700433336555281391630, -17480660118274258421835358082503046895, -17258219798190635332681709532881083302, -17034523707912127110715959730386689660, -16809558798475539336356518978367416213, -16583311820461899456887960150963566910, -16355769320141174483659674454212908650, -16126917634904558608798901255540074585, -15896742889195075006356523859551281311, -15665230989961200349910146602615879610]
def ebU : List ℤ := raw_ints% [67434166887571835030318748393242701190, 67441780983753587364683599448808154461, 67450424940173107365361313601426102933, 67459069037607880772995634686141772111, 67467713276431942480697464939245593394, 67469915654358113064938803179474885251, 67476357656837786234314870513642836229, 67485002179199422737192085173257940051, 67493646843709315733455659838950877717, 67502291650741452021294450572306400537, 67510343129715120980522301635150978335, 67510936600488265603819947192238643364, 67519581693323719658450262718835648137, 67528226929440218707764198639244818003, 67536872309211702592567758150016393334, 67545517832830546615165976613854981234, 67554163500670667563686031866596012874, 67556062118034421004613828634147538620, 67562809312924411780195293629487518891, 67571455269965673283850700796808106024, 67580101371986769716295863089174909723, 67588747619361572611202017572244964884, 67597394012282371169381349692688936025, 67606040551123014722280529259891829737, 67607765828324774547170140036447230513, 67614687236075764289251706235139701507, 67623334067469051032725403012914030279, 67631981045631296799234667904981658319, 67640628170754720821781194331300458177, 67649275443213118164057459520083922734, 67657922863198680525071020874769977315, 67666238467833060796612167116190915592, 67666570431085181755953755488265762662, 67675218147064786280322037056777881102, 67683866011511247019010916643260026541, 67692514024616701378630368900512053681, 67701162186754881631762512488246193953, 67709810498117898426178152311673065209, 67718458959079463668031121776689387205, 67727107569831661504203340307594741422, 67732367246314730671055519364187692014, 67735756330748183756026388774030791582, 67744405242021088327227248759172735796, 67753054304024047235703296973597165947, 67761703516949092399544794639821923717, 67770352881169876314385606485731131308, 67779002396878405169982365229147812206, 67787652064448312220659385780388316255, 67796301884071578184928241187991211322, 67804951856076404602906213916694541634, 67807155983018123396432301445133076128, 67813601980790985239640480905787701175, 67822252258407263088348333665033936749, 67830902689298824527837158020572465833, 67839553273657587721866006537169439122, 67848204011857120789573828526255320537, 67856854904089317321603893544198357940, 67865505950727727457413088410788649956, 67874157151964220470659520462920322147, 67882808508172328800891067312350867443, 67891460019543897660700051734687883316, 67891740537614827474082262397596071206, 67900111686452442069285688238468205916, 67908763509089783433883239663239292620, 67917415487829419632691507964896406415, 67926067622863148523087355819508308357, 67934719914564451121405937316879362195, 67943372363125101990454896154074047188, 67952024968918565563631625134892117347, 67960677732136593364254835924175928016, 67969330653152633521499774339958850087, 67977983732158414774068195161872675127, 67987406318538415610550822512546958031, 68095608161265555429374815435350308836, 68217992914710845735666820136300857078, 68356425128785760852303898554853935666, 68513016302395444860748779709796941088, 68690158231868903440101185242052151719, 68890561098282483758765588573395564449, 69117297058042234763441499936254333581, 69373850255960118484308400234943999032, 69664174383110147650823213380407596101, 69799073442532712410201455533254970354, 69839297588215537727537628797246317901, 69879526419570638408574950201059116794, 69919759964582714348503506505885528043, 69959998251101560595434761291221160949, 69992759161305050499987826474110782518, 70000241307116095627766116942838264461, 70040489160571898884515643732573883747, 70080741839416988039152361002299283496, 70120999371647628746439218329368399255, 70161261785125751861635535611255463853, 70201529107853144082806929586812529150, 70241801367788875847209667203314008504, 70282078592895104819820102337662115579, 70322360811182912811449910310486565679, 70362648050529609890407678234702922271, 70364707482273179932051080708407216323, 70402940338953092172604282130033207146, 70443237704429156937476944106891850468, 70483540174937333148836570195043137476, 70523847778506746362081799458742044562, 70564160543033306578931083148591534832, 70604478496554237969212643044733670239, 70644801667065278056494107956684342589, 70685130082566536087699739809655740696, 70725463771108386746188719166455275887, 70765802760608538596430476102959872336, 70785825387325939294747256679979408933, 70806147079126740522935492712716088151, 70846496754681861832045422142188929799, 70886851815297779285675168445184077258, 70927212289049300436027969303553337166, 70967578203879109502962036071055531319, 71007949587872655317606391416048330012, 71048326469075109182667588094905878231, 71088708875583103029403394244404707162, 71129096835361574964902044907338081304, 71169490376518805868209012553745435670, 71209889527123277180940688355274461001, 71250294315249611587892379066635235291, 71262727696289182224943177371409718073, 71290704769024551723520013321889242010, 71331120916443677457225756377401319603, 71371542785646632618645254950523188218, 71411970404733854851447247212652185766, 71433670826026433520887240553900172209, 71452403801812547235765331181068050687, 71492843005042688895726290198802666293, 71533288042453620851875905690246724880, 71573738942219467671725211537335956303, 71604717563006728199843385857957858701, 71614195732475736215541142796901850402, 71654658441365319012348752058312465849, 71695127097084537581052794532790892925, 71735601727699593673533110893114372219, 71775870034704194346541704216650915631, 71776082361422190650548167316425894826, 71816569026425997942736458650704235994, 71857061750892686991112892789764952545, 71897560563058008093604338512069330758, 71938065491028103856345876843587480843, 71947130371123126484679583627871878021, 71978576563055335099524730584406771293, 72019093807354607850831185652757468022, 72059617252149442660593477365168109611, 72100146925718085784864094306825123281, 72118500704781118183456247137327310721, 72140682856209681656054352477654673146, 72181225071920308128264018159700969885, 72289983170966751426998909903835746866, 72461579907720460486116793198188704532, 72633293056274642269941203323803093625, 72805124761032872909122274973621280403, 72977077169824420844692722804573440232, 73149152433881209797034661665249130601, 73321352708275309724142634910099966154, 73493680151940538550779122292041514078, 73666136927692619791516846304667928028, 73838725202664754161751694540209196609, 74011447148280035781744045592133342741, 74184304940500525780920591392388944107, 74357300759797305750005724881878666869, 74530436791583453939608328518554709547, 74703715226182403307065520763724922675, 74877138259073766765200253487861504914, 75050708090859179321473777138176970944, 75224426927692512307256779256971765244, 75398296981290544575349118670084464958, 75572320468941917159250144609533366288, 75746499613935073451779582615963865270, 75920836645518702822784486575015076633, 76095333799141107736668693008972972622, 76269993316407665702320617957780858338, 76444817445505323317816914222986005172, 76619808441157753819915581702055770140, 76794968564860281437723122018106660588, 76970300084831653005390457033443949588, 77145805276434420468869121344814132967, 77321486422171150682405299503987945452, 77497345811678296073614065256632975751, 77673385742142910116844024046161186308, 77849608518246428409048324355548289194, 78026016452389679495838962309182442520, 78202611864632259538102695130037502172, 78379397083103349252373111736928377186, 78556374443937301540980636048573502865, 78733546291491266643863020919156412318, 78910914978275565910637520373992850634, 79088482865357142516907115811720463717, 79266252322333014442785067116649327039, 79444225727300203544454736250234741767, 79622405467252454996663994539826540132, 79800793937997229285552557994368279661, 79979393544356036429314212622804033118, 80158206700074280145631433759998220550, 80337235828207004503677344356647200894, 80516483361022027126062004211153482113, 80695951740187059587500372900597343779]
def c1U : List ℤ := raw_ints% [-4221772992490775171312269730, -6211469052831138848109353578, -1746624628413275824298678440, 268998890762021283020816858, 15910223448422062271076558, -9774711137053710403874849, 565478501370610197580458, 278175668664747548401735, -51850994308349660237480, -4596132582308306399318, 2479896336770926294066, -92533172171188385688, -86360933456010763279, 12550043069879039592, 2114177335168437160, -693992301222154904, -18976819833906487, 28794818245058740, -1568723165519134, -1025318450947173, 131402599020695, 34601379694665, -7517111509122, -1183885155674, 417699226789, 36739744786, -23924031843, -363337340, 1324822240, -85878135, -65125896, 10419839, 2584055, -799719, -63737, 48509, -1165, -2447, 287, 101, -25, -4, 1, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1]

def pU : EPar := ⟨Int.ofNat (2 ^ 128 + 51), 32, 16, 5, 4, Int.ofNat (2 ^ 384 + 2),
  Int.ofNat ((2 ^ 384 + 2) ^ 32)⟩
def dPU : ℕ := 2 ^ 96
def EcU : List Ev := mergeA 6032 (cellEv 1 (sumP col0) col0) (cutsU.map fun k => (k, 0))
def GcU : List GS := chainQ 0 EcU
def qsU : List (ℚ × ℚ) := List.zipWith (fun a b => ((a : ℚ) / (2 ^ 128 + 51), (b : ℚ) / (2 ^ 128 + 51))) qaU qbU
def E1U : List Ent := List.zipWith (fun w ab => (w, ab.1, ab.2)) wU (List.zip eaU ebU)
def A1U : List QA := (colL 0 GcU qsU).take 200

theorem unit_sum : sumW EcU = 0 := by
  decide +kernel -- kcost: 1508 rational additions, 3 s measured

theorem unit_col : colB GcU qsU = true := by
  decide +kernel -- kcost: 1508 node checks, 38 to 72 s measured on the loaded host

theorem unit_ent : entB pU.D (2 ^ 96) (1 / 2 ^ 126) (1 / 2 ^ 96) A1U E1U = true := by
  decide +kernel -- kcost: 200 rational comparisons, 3 s measured

/-- The moment check with the radices forced to literals once. -/
def momChk : Bool :=
  forceI (Int.ofNat (2 ^ 128 + 51)) fun d => forceI (Int.ofNat (2 ^ 384 + 2)) fun b =>
    forceI (Int.ofNat ((2 ^ 384 + 2) ^ 32)) fun c =>
    forceI (Int.ofNat (2 ^ 96 * (2 ^ 128 + 51) ^ 2)) fun sc =>
      forceI (Int.ofNat (2 ^ 96)) fun dp =>
        grpList false dp sc (moments ⟨d, 32, 16, 5, 4, b, c⟩ E1U) == c1U

theorem momChk_true : momChk = true := by
  decide +kernel -- kcost: 200 entries, 9600 complex products, 512 digits, 11 to 15 s measured

theorem unit_mom :
    (grpList false ((dPU : ℕ) : ℤ) (Int.ofNat (2 ^ 96 * (2 ^ 128 + 51) ^ 2)) (moments pU E1U) ==
      c1U) = true := by
  have := momChk_true
  unfold momChk at this
  simp only [forceI_eq] at this
  exact this

theorem unit_mod : ∀ a ∈ A1U, a.2.1 ^ 2 + a.2.2 ^ 2 ≤ (9 / 10 : ℚ) ^ 2 := by
  decide +kernel -- kcost: 200 rational comparisons

theorem unit_wsum : (A1U.map fun a => |a.1|).sum ≤ 3 := by
  decide +kernel -- kcost: 200 rational additions

theorem unit_esum : (E1U.map fun e => |e.1|).sum ≤ 3 * 2 ^ 96 := by
  decide +kernel -- kcost: 200 additions

theorem unit_len : A1U.length ≤ 200 := by
  decide +kernel -- kcost: 200 list steps

theorem pU_ok : pU.OK where
  D_pos := by decide +kernel -- kcost: one literal
  B_pos := by decide +kernel -- kcost: one literal
  B_even := ⟨Int.ofNat (2 ^ 383 + 1), by decide +kernel⟩ -- kcost: one product
  C_eq := by decide +kernel -- kcost: one power
  lg := by decide +kernel -- kcost: one comparison
  lI := by decide +kernel -- kcost: one comparison

theorem unit_D : (pU.D : ℝ) = 2 ^ 128 + 51 := by
  have : pU.D = 2 ^ 128 + 51 := by decide +kernel -- kcost: one power
  rw [this]
  push_cast
  norm_num

theorem unit_bs : (pU.bs : ℝ) = 32 := by norm_num [pU]

theorem unit_I : (pU.I : ℝ) = 16 := by norm_num [pU]

theorem unit_eta : etaOf pU ((1 / 2 ^ 126 : ℚ) : ℝ) ≤ 1 / 2 ^ 100 := by
  unfold etaOf
  rw [unit_D, unit_bs, unit_I]
  norm_num

theorem unit_eta0 : 0 ≤ etaOf pU ((1 / 2 ^ 126 : ℚ) : ℝ) := by
  unfold etaOf
  rw [unit_D, unit_bs, unit_I]
  norm_num

set_option exponentiation.threshold 2000 in
/-- **The real unit.** The first 200 atoms of the positive column, polynomial `c1U` at scale `2^96`. -/
theorem unit_close : Close dPU (avQ false A1U) c1U (1 / 10 ^ 15) := by
  have hg : ((E1U.map fun e => |e.1|).sum) * (2 * pU.D ^ 2) < pU.B / 2 := by
    decide +kernel -- kcost: 200 additions and one comparison
  have h := group_ok false pU_ok (dP := dPU) (by norm_num [dPU]) (Dz := 2 ^ 96) (by norm_num)
    (ε := 1 / 2 ^ 126) (δ := 1 / 2 ^ 96) unit_ent
    (by rw [unit_D, unit_bs]; norm_num) (by rw [unit_D, unit_bs, unit_I]; norm_num)
    (unit_eta.trans (by norm_num)) unit_eta0 hg (M := 511) (by norm_num [pU])
  have e1 : (2 ^ 96 : ℤ) * pU.D ^ 2 = Int.ofNat (2 ^ 96 * (2 ^ 128 + 51) ^ 2) := by
    decide +kernel -- kcost: two powers
  have e2 : grpList false ((dPU : ℕ) : ℤ) (2 ^ 96 * pU.D ^ 2) (moments pU E1U) = c1U := by
    rw [e1]
    exact beq_iff_eq.1 unit_mom
  rw [e2] at h
  intro t ht
  refine (h t ht).trans ?_
  have ha := atail_le (ρ := 9 / 10) (by norm_num) (by norm_num) 511 A1U unit_mod
  have hw : (((A1U.map fun a => |a.1|).sum : ℚ) : ℝ) ≤ 3 := by exact_mod_cast unit_wsum
  have hE : (((E1U.map fun e => |e.1|).sum : ℤ) : ℝ) ≤ 3 * 2 ^ 96 := by exact_mod_cast unit_esum
  have hl : (A1U.length : ℝ) ≤ 200 := by exact_mod_cast unit_len
  have hk : (((511 : ℕ) : ℝ)) = 511 := by norm_num
  have hd : (dPU : ℝ) = 2 ^ 96 := by norm_num [dPU]
  have hη := unit_eta
  have hη0 := unit_eta0
  have hq : (0 : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) ^ (511 + 1) *
      (1 - ((9 / 10 : ℚ) : ℝ))⁻¹ / (((511 : ℕ) : ℝ) + 1) := by norm_num
  have b1 : atail (A1U.map aR) 511 ≤ 1 / 10 ^ 16 := by
    refine ha.trans ?_
    have : (((A1U.map fun a => |a.1|).sum : ℚ) : ℝ) *
        (4 * ((((9 / 10 : ℚ) : ℝ)) ^ (511 + 1) * (1 - ((9 / 10 : ℚ) : ℝ))⁻¹ /
          (((511 : ℕ) : ℝ) + 1))) ≤ 3 * (4 * ((((9 / 10 : ℚ) : ℝ)) ^ (511 + 1) *
          (1 - ((9 / 10 : ℚ) : ℝ))⁻¹ / (((511 : ℕ) : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right hw (by linarith)
    refine this.trans ?_
    norm_num
  have b2 : (A1U.length : ℝ) * ((1 / 2 ^ 96 : ℚ) : ℝ) +
      (((E1U.map fun e => |e.1|).sum : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) *
        etaOf pU ((1 / 2 ^ 126 : ℚ) : ℝ) ≤ 1 / 2 ^ 80 := by
    have c1 : (A1U.length : ℝ) * ((1 / 2 ^ 96 : ℚ) : ℝ) ≤ 200 * (1 / 2 ^ 96) := by
      push_cast
      exact mul_le_mul_of_nonneg_right hl (by norm_num)
    have c2 : (((E1U.map fun e => |e.1|).sum : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) ≤ 3 := by
      have e : ((2 ^ 96 : ℤ) : ℝ) = 2 ^ 96 := by norm_num
      rw [e, div_le_iff₀ (by norm_num)]
      exact hE
    have c0 : (0 : ℝ) ≤ (((E1U.map fun e => |e.1|).sum : ℤ) : ℝ) / ((2 ^ 96 : ℤ) : ℝ) := by
      refine div_nonneg ?_ (by norm_num)
      exact_mod_cast List.sum_nonneg (by
        intro x hx
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact abs_nonneg _)
    have c3 := mul_le_mul c2 hη hη0 (by norm_num)
    have : (200 : ℝ) * (1 / 2 ^ 96) + 3 * (1 / 2 ^ 100) ≤ 1 / 2 ^ 80 := by norm_num
    linarith
  rw [hk, hd]
  linarith [b1, b2]

end CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
