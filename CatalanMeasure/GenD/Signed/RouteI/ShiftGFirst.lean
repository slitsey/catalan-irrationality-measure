module

public import CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond
public import CatalanMeasure.GenD.DesignInstance.FirstTrialCert

@[expose] public section
set_option Elab.async false

/-!
# G5 shiftG, first population: the unsigned record of the first sheet

`firstRec`: the `FirstTrialBoundsEnd P58 ∅ (colCell P58 (3/4) β) (nodeD P58 δc) Gd …` record of
`FirstData.R` over the K590 first record `Terminal295.first295` through `ShiftG.shiftFirstG`
(`p = firstP + τ du`, `v = firstV + τ dv`, `λ = λ₀ + τ dl`, K = 24 constrained trial; `du` is the
increment of the doubled trial, `dl = 213407 / 2^23`).

The marked cap is GP Lemma 7.3 on the 865 segments of the frozen table: `firstOK` is one kernel
decision on integers (`ChordTable.first_case_cap`, `pwl_le_max` at the table of
`ChordTableData`); `first_marked` is its real statement for any rational `λ` and cap.
-/

open Set Filter

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.ShiftG
  CatalanMeasure.GenD.Signed.RouteI.ShiftGNum CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond
  CatalanMeasure.GenD.Signed.RouteI.Family
  CatalanMeasure.GenD.Signed.RouteI.TerminalC CatalanMeasure.GenD.Signed.RouteI.ChordTable
  CatalanMeasure.GenD.Signed.RouteI.ChordTableData CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData
  CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.GenD.D58 CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.RouteI

noncomputable section

/-! ### Lemma 7.3 on the table -/

/-- One kernel decision on integers: on every segment `i ≠ 384` the cap
`λ (g - 1 + √(1 - t*²)) + m/58` is at most `sn/sd` (`λ = ln/ld`, `g = 5/29`, `t* = min(|k_i|, |k_{i+1}|)`,
`m = max(v_i, v_{i+1})`), the square root being compared through `1 - t*² ≤ ρ²`, `0 ≤ ρ`,
`ρ = Rn / Dn`. -/
def firstOK (ln ld sn sd : ℤ) : Bool :=
  (List.range 865).all fun i =>
    decide (i = 384) ||
    (decide (0 ≤ knotZ i * knotZ (i + 1)) &&
     decide (0 ≤ (sn * 58000000000 - (max (vZ i) (vZ (i + 1))) * sd) * ld * 29 + 24 * sd * 58000000000 * ln) &&
     decide ((2 ^ 80 - (min ((knotZ i).natAbs : ℤ) ((knotZ (i + 1)).natAbs : ℤ)) ^ 2) *
        (29 * sd * 58000000000 * ln) ^ 2 ≤
       ((sn * 58000000000 - (max (vZ i) (vZ (i + 1))) * sd) * ld * 29 + 24 * sd * 58000000000 * ln) ^ 2 * 2 ^ 80))

theorem seg_cap {ln ld sn sd : ℤ} (hln : 0 < ln) (hld : 0 < ld) (hsd : 0 < sd)
    (h : firstOK ln ld sn sd = true) {i : ℕ} (hi : i < 865) (hi384 : i ≠ 384) :
    0 ≤ kt i * kt (i + 1) ∧
    ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 1 + Real.sqrt (1 - (((min ((knotZ i).natAbs : ℤ)
        ((knotZ (i + 1)).natAbs : ℤ) : ℤ) : ℝ) / 2 ^ 40) ^ 2)) +
      max (vt i) (vt (i + 1)) / 58 ≤ (sn : ℝ) / sd := by
  unfold firstOK at h
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [hi384, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨hprod, hR⟩, hsq⟩ := h1
  set m : ℤ := max (vZ i) (vZ (i + 1)) with hm
  set a : ℤ := min ((knotZ i).natAbs : ℤ) ((knotZ (i + 1)).natAbs : ℤ) with ha
  set Rn : ℤ := (sn * 58000000000 - m * sd) * ld * 29 + 24 * sd * 58000000000 * ln with hRn
  set Dn : ℤ := 29 * sd * 58000000000 * ln with hDn
  have hDpos : (0 : ℝ) < Dn := by rw [hDn]; push_cast; positivity
  have hlnR : (0 : ℝ) < ln := by exact_mod_cast hln
  have hldR : (0 : ℝ) < ld := by exact_mod_cast hld
  have hsdR : (0 : ℝ) < sd := by exact_mod_cast hsd
  refine ⟨?_, ?_⟩
  · unfold kt
    have : (0 : ℝ) ≤ (knotZ i : ℝ) * (knotZ (i + 1) : ℝ) := by exact_mod_cast hprod
    have e : (knotZ i : ℝ) / 2 ^ 40 * ((knotZ (i + 1) : ℝ) / 2 ^ 40) =
        ((knotZ i : ℝ) * knotZ (i + 1)) / 2 ^ 80 := by ring
    rw [e]; positivity
  · -- the square root
    have hρ0 : (0 : ℝ) ≤ (Rn : ℝ) / Dn := div_nonneg (by exact_mod_cast hR) hDpos.le
    have hsq' : (2 ^ 80 - (a : ℝ) ^ 2) * (Dn : ℝ) ^ 2 ≤ (Rn : ℝ) ^ 2 * 2 ^ 80 := by exact_mod_cast hsq
    have hle : 1 - ((a : ℝ) / 2 ^ 40) ^ 2 ≤ ((Rn : ℝ) / Dn) ^ 2 := by
      rw [div_pow, div_pow, show ((2 : ℝ) ^ 40) ^ 2 = 2 ^ 80 by norm_num, le_div_iff₀ (by positivity)]
      have h80 : (0 : ℝ) < 2 ^ 80 := by positivity
      have : (1 - (a : ℝ) ^ 2 / 2 ^ 80) * (Dn : ℝ) ^ 2 = (2 ^ 80 - (a : ℝ) ^ 2) * (Dn : ℝ) ^ 2 / 2 ^ 80 := by
        field_simp
      rw [this, div_le_iff₀ h80]
      linarith
    have hsqrt : Real.sqrt (1 - ((a : ℝ) / 2 ^ 40) ^ 2) ≤ (Rn : ℝ) / Dn :=
      Real.sqrt_le_iff.mpr ⟨hρ0, hle⟩
    -- the values
    have hv : max (vt i) (vt (i + 1)) ≤ (m : ℝ) / 10 ^ 9 := by
      refine max_le ?_ ?_
      · unfold vt; rw [hm]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast le_max_left _ _
      · unfold vt; rw [hm]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast le_max_right _ _
    have hlam : (0 : ℝ) ≤ (ln : ℝ) / ld := by positivity
    have step : ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 1 + Real.sqrt (1 - ((a : ℝ) / 2 ^ 40) ^ 2)) ≤
        ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 1 + (Rn : ℝ) / Dn) :=
      mul_le_mul_of_nonneg_left (by linarith) hlam
    have key : ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 1 + (Rn : ℝ) / Dn) + (m : ℝ) / 10 ^ 9 / 58 =
        (sn : ℝ) / sd := by
      rw [hRn, hDn]
      push_cast
      field_simp
      ring
    calc ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 1 + Real.sqrt (1 - ((a : ℝ) / 2 ^ 40) ^ 2)) +
          max (vt i) (vt (i + 1)) / 58
        ≤ ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 1 + (Rn : ℝ) / Dn) + (m : ℝ) / 10 ^ 9 / 58 := by
          have := div_le_div_of_nonneg_right hv (by norm_num : (0 : ℝ) ≤ 58)
          linarith
      _ = (sn : ℝ) / sd := key

/-- **GP Lemma 7.3 on the window.**  For `λ = ln/ld ≥ 0` and a cap `sn/sd` passing `firstOK`,
`λ c(x) + nodeD x ≤ sn/sd` for every `x ∈ (-1, 1) \ {0}` of the window. -/
theorem first_marked {ln ld sn sd : ℤ} (hln : 0 < ln) (hld : 0 < ld) (hsd : 0 < sd)
    (h : firstOK ln ld sn sd = true) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hG : Gd x) :
    ((ln : ℝ) / ld) * ((5 : ℝ) / 29 - 2 * x ^ 2 / (1 + x ^ 2)) + nodeD P58 δc x ≤ (sn : ℝ) / sd := by
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hlt0, hlt865⟩ := G16.gd_hull hG
  set t : ℝ := 2 * x / (1 + x ^ 2) with ht
  have hrc : realCoordinateInv x = t := rfl
  -- a segment avoiding the gap
  obtain ⟨i, hi, hi384, hti⟩ : ∃ i, i < 865 ∧ i ≠ 384 ∧ t ∈ Icc (kt i) (kt (i + 1)) := by
    rcases Gd_gap hG with hg | hg
    · rw [hrc] at hg
      obtain ⟨i, hi, hti⟩ := exists_seg (K := 384) (by norm_num) (k := kt) hlt0.le hg
      exact ⟨i, by omega, by omega, hti⟩
    · rw [hrc] at hg
      obtain ⟨j, hj, hti⟩ := exists_seg (K := 480) (by norm_num) (k := fun j => kt (385 + j))
        (by simpa using hg) (by
          have : kt (385 + 480) = kt 865 := rfl
          simpa using hlt865.le)
      exact ⟨385 + j, by omega, by omega, by simpa [add_assoc] using hti⟩
  obtain ⟨hprod, hcap⟩ := seg_cap hln hld hsd h hi hi384
  have hts0 : (0 : ℝ) ≤ (((min ((knotZ i).natAbs : ℤ) ((knotZ (i + 1)).natAbs : ℤ) : ℤ) : ℝ) / 2 ^ 40) := by
    positivity
  have hu : (((min ((knotZ i).natAbs : ℤ) ((knotZ (i + 1)).natAbs : ℤ) : ℤ) : ℝ) / 2 ^ 40) ≤ |kt i| := by
    unfold kt
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 40)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : ((knotZ i).natAbs : ℤ) = |knotZ i| := Int.natCast_natAbs _
    have h2 : (|((knotZ i : ℤ) : ℝ)|) = (((knotZ i).natAbs : ℤ) : ℝ) := by
      rw [← Int.cast_abs, ← this]
    rw [h2]
    exact_mod_cast min_le_left _ _
  have hw : (((min ((knotZ i).natAbs : ℤ) ((knotZ (i + 1)).natAbs : ℤ) : ℤ) : ℝ) / 2 ^ 40) ≤ |kt (i + 1)| := by
    unfold kt
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 40)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : ((knotZ (i + 1)).natAbs : ℤ) = |knotZ (i + 1)| := Int.natCast_natAbs _
    have h2 : (|((knotZ (i + 1) : ℤ) : ℝ)|) = (((knotZ (i + 1)).natAbs : ℤ) : ℝ) := by
      rw [← Int.cast_abs, ← this]
    rw [h2]
    exact_mod_cast min_le_right _ _
  have hδ : pwl 865 kt vt t ≤ max (vt i) (vt (i + 1)) := pwl_le_max kt_lt hi hti
  have hlam : (0 : ℝ) ≤ (ln : ℝ) / ld := by positivity
  have hcc := first_case_cap (g := (5 : ℝ) / 29) (n₀ := 58) (m := max (vt i) (vt (i + 1)))
    (ts := (((min ((knotZ i).natAbs : ℤ) ((knotZ (i + 1)).natAbs : ℤ) : ℤ) : ℝ) / 2 ^ 40))
    (u := kt i) (w := kt (i + 1)) (x := x) (δt := pwl 865 kt vt t) hx1 hlam (by norm_num) hts0 hu hw
    hprod hti hδ
  have e : nodeD P58 δc x = pwl 865 kt vt t / 58 := hd_node x
  rw [e]
  linarith

/-! ### The record -/

/-- The K590 first record. -/
abbrev base1 : FirstTrialBounds P58 K590.target K590.firstCost :=
  firstTrial_D58 hrow_D58 hcol_D58 K590.first_budget_log2

theorem base1_p : base1.p = D58.firstP := rfl
theorem base1_v : base1.v = D58.firstV := rfl
theorem base1_lambda : base1.lambda = D58.lamFirst := rfl
theorem base1_normCap : base1.normCap = n1 := rfl

theorem duF_support : ∀ k, 25 ≤ k → duF k = 0 := fun k hk =>
  trialSeqOf_support du24 (2 ^ 23) (by rw [len_du24]; omega)
theorem dvF_support : ∀ k, 25 ≤ k → dvF k = 0 := fun k hk =>
  trialSeqOf_support dv24 (2 ^ 24) (by rw [len_dv24]; omega)

theorem paramCase58 {N : ℕ} (hN : 0 < N) (x : ℝ) :
    paramCaseField P58 N x = 5 / 29 - 2 * x ^ 2 / (1 + x ^ 2) := by
  unfold paramCaseField
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e1 : ((P58.g N : ℕ) : ℝ) = 5 * N := by simp [Parameters.g, P58]
  have e2 : ((P58.n N : ℕ) : ℝ) = 58 * N := by simp [Parameters.n, P58]
  rw [e1, e2]
  field_simp
  ring

theorem firstOK0 : firstOK 168493357 100000000 35072 100000 = true := by
  -- kcost: 1.3 s measured, 865 segments of integer arithmetic on 80-bit squares
  decide +kernel

theorem firstOK1 : firstOK (168493357 * 8388608 + 213407 * 100000000) (100000000 * 8388608) 35295 100000 = true := by
  -- kcost: 1.3 s measured, 865 segments of integer arithmetic on 80-bit squares
  decide +kernel

/-- The norm cap of the first record at `τ`. -/
def normCap1 (τ : ℝ) : ℝ := n1 + τ * (-82834152 / 1000000000) + τ ^ 2 * (4096781 / 1000000000)

/-- **The first-population shift record** at `(τ, β)` over the K590 first record: `p = p₀ + τ du`,
`v = v₀ + τ dv`, `λ = λ₀ + τ dl` (K = 24), node correction `nodeD P58 δc`, window `Gd`, column field of
the cell `β`.  The marked cap is `M₁ ≥ (1 - τ) 35072/10^5 + τ 35295/10^5`. -/
def firstRec (X1 : ℝ)
    (hX1 : ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT duF x) - barrierTrialS dvF x +
      (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤ X1)
    (target cost M1 β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvF s) ≤ ΔY)
    (hM : (1 - τ) * (35072 / 100000 : ℝ) + τ * (35295 / 100000) ≤ M1) :
    FirstTrialBoundsEnd P58 ∅ (colCell P58 (3 / 4) β) (nodeD P58 δc) Gd target cost :=
  shiftFirstG (D := base1) (du := duF) (dv := dvF) (K := 25) duF_support dvF_support τ (213407 / 2 ^ 23)
    (τ * X1) ΔY (normCap1 τ) M1
    (by rw [base1_lambda]; unfold D58.lamFirst; positivity)
    (by
      have h1 := mul_le_mul_of_nonneg_left cr1_real hτ0
      have h2 := mul_le_mul_of_nonneg_left qd1_real (sq_nonneg τ)
      rw [base1_normCap, base1_p, base1_v]
      unfold normCap1
      nlinarith only [h1, h2])
    (fun {N} hN x hx => by
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> constructor <;> linarith
      have := mul_le_mul_of_nonneg_left (hX1 x hx') hτ0
      rw [paramCase58 hN]
      nlinarith only [this])
    (Filter.Eventually.of_forall fun N s hs => by
      unfold colCell
      have := hY s ⟨hs.1.le, hs.2.le⟩
      linarith)
    (fun {N} hN {x} hx hx0 hG => by
      rw [base1_lambda, paramCase58 hN]
      have h0 := first_marked (by norm_num) (by norm_num) (by norm_num) firstOK0 hx hG
      have h1 := first_marked (by norm_num) (by norm_num) (by norm_num) firstOK1 hx hG
      have hl0 : ((168493357 : ℤ) : ℝ) / ((100000000 : ℤ) : ℝ) = D58.lamFirst := by
        unfold D58.lamFirst; norm_num
      have hl1 : (((168493357 * 8388608 + 213407 * 100000000 : ℤ) : ℤ) : ℝ) / ((100000000 * 8388608 : ℤ) : ℝ) =
          D58.lamFirst + 213407 / 2 ^ 23 := by
        unfold D58.lamFirst; norm_num
      rw [hl0] at h0
      rw [hl1] at h1
      have := lam_interp (lam := D58.lamFirst) (dl := 213407 / 2 ^ 23) (c := 5 / 29 - 2 * x ^ 2 / (1 + x ^ 2))
        (dd := nodeD P58 δc x) (S0 := (35072 : ℝ) / 100000) (S1 := (35295 : ℝ) / 100000) (τ := τ)
        (by simpa using h0) (by simpa using h1) hτ0 hτ1
      linarith)
    (fun a ha => (notMem_empty _ ha).elim)

theorem firstRec_normCap (X1 : ℝ)
    (hX1 : ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT duF x) - barrierTrialS dvF x +
      (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤ X1)
    (target cost M1 β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvF s) ≤ ΔY)
    (hM : (1 - τ) * (35072 / 100000 : ℝ) + τ * (35295 / 100000) ≤ M1) :
    (firstRec X1 hX1 target cost M1 β τ ΔY hτ0 hτ1 hY hM).normCap = normCap1 τ := rfl

theorem firstRec_fieldCap (X1 : ℝ)
    (hX1 : ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT duF x) - barrierTrialS dvF x +
      (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤ X1)
    (target cost M1 β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvF s) ≤ ΔY)
    (hM : (1 - τ) * (35072 / 100000 : ℝ) + τ * (35295 / 100000) ≤ M1) :
    (firstRec X1 hX1 target cost M1 β τ ΔY hτ0 hτ1 hY hM).fieldCap = F1 + τ * X1 + ΔY := rfl

theorem firstRec_M₁ (X1 : ℝ)
    (hX1 : ∀ x ∈ Icc (-1 : ℝ) 1, -(2 * barrierTrialT duF x) - barrierTrialS dvF x +
      (213407 / 2 ^ 23 : ℝ) * (5 / 29 - 2 * x ^ 2 / (1 + x ^ 2)) ≤ X1)
    (target cost M1 β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvF s) ≤ ΔY)
    (hM : (1 - τ) * (35072 / 100000 : ℝ) + τ * (35295 / 100000) ≤ M1) :
    (firstRec X1 hX1 target cost M1 β τ ΔY hτ0 hτ1 hY hM).M₁ = M1 := rfl

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst

#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst.first_marked
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst.firstRec
