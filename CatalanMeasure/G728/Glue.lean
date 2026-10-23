module

public import CatalanMeasure.G728.FieldsS
public import CatalanMeasure.G728.Data
public import CatalanMeasure.Parametric.FlexibleSecondEnergy
public import CatalanMeasure.Parametric.StrongNearField
public import CatalanMeasure.Parametric.TwentyCorrectedFields
public import CatalanMeasure.Parametric.TwentyPhysicalCertifiedFields
public import CatalanMeasure.Parametric.TwentyGroupedPhysicalFields
public import CatalanMeasure.Parametric.TwentyTrialFields

@[expose] public section

/-!
# From the three field suprema to `SecondTrialBoundsOn`

Scaled (`trialSeqS`) version of `Parametric.gapSecondTrialOfFields`.  Generic in
`target residual cost normCap fieldCap` and in the residual domain `G`; the budget inequality is a
hypothesis (the 728 scalar stack is in `Budgets.lean`).
-/

open OAI.InternalCatalan Set Filter
open scoped Topology

namespace CatalanMeasure.G728
open CatalanMeasure.Cert CatalanMeasure.Parametric
set_option maxRecDepth 100000
noncomputable section

theorem near_finite_of_first (pp : ℕ → ℝ) (hp : (9 / 50 : ℝ) ≤ pp 1)
    {N : ℕ} (hN : 0 < N) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    -(9 / 10 : ℝ) * Real.log (1 + y ^ 2) + ((16 * N - 1 : ℕ) : ℝ) / (20 * N) * Real.log y -
      pp 1 * y ≤ -(3 / 4 : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (0 : ℝ) < 20 * N := by positivity
  have hc : (3 / 4 : ℝ) ≤ ((16 * N - 1 : ℕ) : ℝ) / (20 * N) := by
    rw [le_div_iff₀ hd, Nat.cast_sub (by omega : 1 ≤ 16 * N)]
    push_cast
    linarith only [hn]
  have hl : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2.le
  have hm := mul_le_mul_of_nonpos_right hc hl
  have hb := near_residual_field_le_three_fourths hp hy.1 hy.2.le
  linarith only [hm, hb]

/-- **The scaled second-energy contract from the three field suprema.**
Row weights `(2/5, 1/10, 27/20)`, column weights `(3/20, 1/20)`, residual `-(9/10) log (1+x²) - 2 T`. -/
def secondTrialOfFieldsS {target residual cost normCap fieldCap : ℝ} {G : ℝ → Prop}
    (Pc Vc : List ℤ) (P V : List TailQ) (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (R : RowWeights) (hR : R = ⟨2 / 5, 1 / 10, 27 / 20, 0, 1 / 5⟩)
    (C : ColumnWeights) (hC : C = ⟨3 / 20, 1 / 20, 0⟩) (MX MY : ℝ)
    (first_lower : (9 / 50 : ℝ) ≤ trialSeqS Pc P 1)
    (norm_le : 2 * barrierTrialNormSq (trialSeqS Pc P) + barrierTrialNormSq (trialSeqS Vc V) / 2 ≤
      normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldS Pc P x ≤ residual)
    (budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
      (-(1 / 5 : ℝ) + (8 / 5) * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
        (a - t) * residual + t * (-(3 / 4 : ℝ)) + (9 / 10) * a ≤
          -target + Real.log 2 / 2 + (cost + 9 / 10) * a) :
    SecondTrialBoundsOn target residual (-(3 / 4 : ℝ)) cost G where
  p := trialSeqS Pc P
  v := trialSeqS Vc V
  MX := MX
  MY := MY
  normCap := normCap
  fieldCap := fieldCap
  p_summable := (trialSeqS_summable hP).1
  v_summable := (trialSeqS_summable hV).1
  norm_le := norm_le
  field_sum := field_sum
  row := by
    intro ε hε
    subst hR
    have hrow : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
        rowFieldG (2 / 5) (1 / 10) (27 / 20) (trialSeqS Pc P) (trialSeqS Vc V) x ≤ MX := by
      intro x hx
      have := row_sup x hx
      simpa [rowFieldS] using this
    have hh := rowFieldG_corrected_eventually (α := 2 / 5) (β := 1 / 10) (γ := 27 / 20)
      (trialSeqS_summable hP).1 (trialSeqS_summable hV).1 (by norm_num) (by norm_num)
      (a := 2) (b := 1 / 2) (by norm_num) (by norm_num) hrow
      TwentyCertified.reciprocalScale TwentyCertified.reciprocalScale_nonneg
      TwentyCertified.reciprocalScale_tendsto hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN x hx
    rw [TwentyCertified.physicalTwo_row_identity, twenty_populationRowField hN]
    have hb := hc x hx
    rw [rowFieldG_eq] at hb
    push_cast
    linarith only [hb]
  column := by
    intro ε hε
    subst hC
    have hcol : ∀ s ∈ Ioo (0 : ℝ) 1,
        colFieldG (3 / 20) (1 / 20) (trialSeqS Vc V) s ≤ MY := by
      intro s hs
      have := column_sup s hs
      simpa [colFieldS] using this
    have hh := colFieldG_corrected_eventually (b := 3 / 20) (q := 1 / 20)
      (trialSeqS_summable hV).1 (by norm_num) (by norm_num) hcol
      TwentyCertified.reciprocalScale TwentyCertified.reciprocalScale_nonneg
      TwentyCertified.reciprocalScale_tendsto hε
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hc hN s hs
    rw [TwentyCertified.physical_column_identity hN]
    have hb := hc s hs
    unfold colFieldG colRegG at hb
    simp only [Rat.cast_zero, zero_mul, add_zero]
    linarith only [hb]
  marked := by
    intro N hN x hx hgap
    have hn : (0 : ℝ) < twenty.n N := by exact_mod_cast n_pos twenty_admissible hN
    have hsq : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
    have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb := residual_sup x hx hgap
    unfold resFieldS resFieldG at hb
    rw [twenty_grouped_marked_field_identity hN]
    linarith only [hb, hcorr]
  near := by
    intro N hN y hy
    have hn : (0 : ℝ) < twenty.n N := by exact_mod_cast n_pos twenty_admissible hN
    have hsq : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
    have hlog : Real.log (1 + y ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb := near_finite_of_first (trialSeqS Pc P) first_lower hN hy
    have he : twenty.n N - 1 - 2 * twenty.g N = 16 * N - 1 := by
      change 20 * N - 1 - 2 * (2 * N) = 16 * N - 1
      omega
    unfold groupedPhysicalNearField
    rw [twenty_grouped_marked_field_identity hN, he, abs_of_pos hy.1]
    have hnu : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
    rw [← hnu] at hb
    linarith only [hb, hcorr]
  budget := budget

/-! ### the first coefficient -/

/-- exact rational value of the first coefficient `trialSeqS cs tail 1` -/
def firstQ (cs : List ℤ) (tail : List TailQ) : ℚ :=
  (cs.getD 0 0 : ℚ) / 1099511627776 + (tail.map (fun t => t.rr * t.zr - t.ri * t.zi)).sum

theorem tailSum_one (tail : List TailQ) :
    (((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ 1)).sum).re =
      (((tail.map (fun t => t.rr * t.zr - t.ri * t.zi)).sum : ℚ) : ℝ) := by
  induction tail with
  | nil => simp
  | cons t tail ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re] at ih ⊢
    rw [ih]
    simp [TailQ.toC, barrierComplex, Complex.mul_re]

theorem trialSeqS_one (cs : List ℤ) (tail : List TailQ) :
    trialSeqS cs tail 1 = ((firstQ cs tail : ℚ) : ℝ) := by
  have h := trialSeqS_succ cs tail 0
  rw [zero_add] at h
  rw [h, tailSum_one]
  unfold firstQ
  push_cast
  rfl

theorem firstQ_data : (9 / 50 : ℚ) ≤ firstQ Pc P := by
  unfold firstQ; decide +kernel

/-- `p_1 ≥ 9/50` for the 728 witness -/
theorem first_lower : (9 / 50 : ℝ) ≤ trialSeqS Pc P 1 := by
  rw [trialSeqS_one]
  have h : (((9 / 50 : ℚ)) : ℝ) ≤ ((firstQ Pc P : ℚ) : ℝ) := Rat.cast_le.mpr firstQ_data
  push_cast at h
  exact h

end
end CatalanMeasure.G728
