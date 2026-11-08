module

public import CatalanMeasure.GenD.Signed.RouteI.TerminalC
public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Caps
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Near
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Norm
public import CatalanMeasure.GenD.DesignInstance.PositiveBudget
public import CatalanMeasure.GenD.Analytic.Instances
public import CatalanMeasure.GenD.Analytic.DeltaChain
public import CatalanMeasure.GenD.Signed.RouteI.ChordPair
public import CatalanMeasure.GenD.Signed.RouteI.NearDataCert
public import CatalanMeasure.GenD.Signed.RouteI.ShiftG
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGNum

@[expose] public section
set_option Elab.async false

/-!
# G5 shiftG, second population: the unsigned record of the design window

`secondRec`: the `SecondTrialBoundsEnd P58 ∅ (colCell P58 (3/4) β) (nodeD P58 δc) … Gd` record of
`LargeData.R` (`τ = 1`) and `NearData.Rp` (`τ = β / a₁`) over the K590 second record
`Terminal295.second295`, through `ShiftG.shiftSecondG` (`d = nodeD P58 δc`, window `Gd`).  Everything
that is a finite computation is a hypothesis in the shape of its leaf producer:

* `hX2`: `ShiftGLeafX.X2_leaf` (row sup of the shift);
* `hY`: `ShiftGLeafY2` knots interpolated by the assembly module;
* the marked field: `Cert590.residual_pair` through `ChordPair.residual_pair_Gd` for `|x| ≥ 401/2500`
  and `UnsignedInstance.ext_pair` on `[98749/10^6, 401/2500]`, interpolated in `τ` by `lin_interp`;
* the near field: `NearDataCert.Cover.near_N0`, `near_N1` (`p 1 ≥ 0.181506`, `p 1 + du 1 ≥ 0.16496`) by
  `lin_interp_near`;
* the norm: `ShiftGNum.cr2_real`, `qd2_real`.
-/

open Set Filter

namespace CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance CatalanMeasure.GenD.Signed.RouteI.ShiftG
  CatalanMeasure.GenD.Signed.RouteI.ShiftGNum CatalanMeasure.GenD.Signed.RouteI.Family
  CatalanMeasure.GenD.Signed.RouteI.TerminalC CatalanMeasure.GenD.Signed.RouteI.ChordTable
  CatalanMeasure.GenD.Signed.RouteI.ChordTableData CatalanMeasure.GenD.Signed.RouteI.IntervalNodesData
  CatalanMeasure.GenD.Signed.RouteI.CompletedGas CatalanMeasure.GenD.D58 CatalanMeasure.CellCert CatalanMeasure.Cert
  CatalanMeasure.GenD.Signed.RouteI

noncomputable section

/-! ### The window `Gd` -/

theorem Gd_ne_zero {y : ℝ} (h : Gd y) : y ≠ 0 := by
  intro h0
  obtain ⟨-, hU⟩ := h
  obtain ⟨c, hc⟩ := mem_iUnion.mp hU
  have e : realCoordinateInv y = 0 := by rw [h0]; unfold realCoordinateInv; simp
  rw [e] at hc
  exact ivl_zero c hc

/-- Every point of the window is at distance at least `98749/10^6` from `0` on the right and
`19501/100000` on the left; the part of the right branch below `401/2500` is the extension window. -/
theorem Gd_split {x : ℝ} (hG : Gd x) :
    (401 / 2500 : ℝ) ≤ |x| ∨ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500) := by
  rcases lt_trichotomy x 0 with hneg | hz | hpos
  · left
    have h1 : (19501 / 100000 : ℝ) ≤ -x := ((hG_d x hG).2 hneg).1
    rw [abs_of_neg hneg]
    linarith
  · exact absurd hz (Gd_ne_zero hG)
  · have h1 : (98749 / 1000000 : ℝ) ≤ x := ((hG_d x hG).1 hpos).1
    by_cases h : (401 / 2500 : ℝ) ≤ x
    · left
      rw [abs_of_pos hpos]
      exact h
    · right
      exact ⟨h1, (not_le.mp h).le⟩

theorem kt385 : kt 385 = (215054274947 : ℝ) / 2 ^ 40 := by
  have : knotZ 385 = 215054274947 := by decide +kernel -- kcost: 0.01 s (one packed-knot decode)
  unfold kt; rw [this]; push_cast; ring

theorem kt384 : kt 384 = -(413122735120 : ℝ) / 2 ^ 40 := by
  have : knotZ 384 = -413122735120 := by decide +kernel -- kcost: 0.01 s (one packed-knot decode)
  unfold kt; rw [this]; push_cast; ring

/-- On the right branch the window lies above `k₃₈₅` (the first knot after the gap). -/
theorem Gd_pos_hull {y : ℝ} (hy : 0 < y) (hG : Gd y) :
    kt 385 ≤ realCoordinateInv y ∧ realCoordinateInv y ≤ kt 865 := by
  obtain ⟨-, hU⟩ := hG
  obtain ⟨c, hc⟩ := mem_iUnion.mp hU
  have hz := ivl_zero c
  have ht0 : 0 < realCoordinateInv y := by unfold realCoordinateInv; positivity
  have hhi0 : 0 < ivlHi c := ht0.trans hc.2
  have hlo0 : 0 ≤ ivlLo c := by
    by_contra hn
    exact hz ⟨not_le.mp hn, hhi0⟩
  have h1 := ivl_P c hlo0
  have hh := hull_table c
  constructor
  · rw [kt385]; linarith [hc.1]
  · exact hc.2.le.trans hh.2

/-- Either branch of the window avoids the gap `(k₃₈₄, k₃₈₅)` of the knot table. -/
theorem Gd_gap {y : ℝ} (hG : Gd y) :
    realCoordinateInv y ≤ kt 384 ∨ kt 385 ≤ realCoordinateInv y := by
  obtain ⟨-, hU⟩ := hG
  obtain ⟨c, hc⟩ := mem_iUnion.mp hU
  have hz := ivl_zero c
  by_cases hhi : ivlHi c ≤ 0
  · left
    have := ivl_N c hhi
    rw [kt384]
    linarith [hc.2]
  · right
    have hhi' : 0 < ivlHi c := not_le.mp hhi
    have hlo0 : 0 ≤ ivlLo c := by
      by_contra hn
      exact hz ⟨not_le.mp hn, hhi'⟩
    have h1 := ivl_P c hlo0
    rw [kt385]
    linarith [hc.1]

theorem hd_node (u : ℝ) : nodeD P58 δc u = pwl 865 kt vt (realCoordinateInv u) / 58 := by
  unfold nodeD δc
  norm_num [P58]

/-! ### The K590 base record -/

/-! The K590 second record, assembled from its sources (not through `Terminal295`, whose closure
reaches the retired residual cover).  The residual field is vacuous (`G0 = False`): `shiftSecondG` never
reads the base `marked`, `near`, `budget` fields. -/

theorem row_sup_K590 : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Cert590.Pc Cert590.P)
      (trialSeqS Cert590.Vc Cert590.V) x ≤ ((Cert590.MX : ℚ) : ℝ) := by
  intro x hx
  have h := Cert590.row_sup_S' x hx
  have e : rowFieldS Cert590.R Cert590.Pc Cert590.Vc Cert590.P Cert590.V =
      rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Cert590.Pc Cert590.P)
        (trialSeqS Cert590.Vc Cert590.V) := by
    unfold rowFieldS
    norm_num [Cert590.R]
  rw [e] at h
  exact h

theorem column_sup_K590 : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) (trialSeqS Cert590.Vc Cert590.V) s ≤ ((Cert590.MY : ℚ) : ℝ) := by
  intro s hs
  have h := Cert590.column_sup_S' s hs
  have e : colFieldS Cert590.C Cert590.Vc Cert590.V =
      colFieldG (9 / 58) (3 / 58) (trialSeqS Cert590.Vc Cert590.V) := by
    unfold colFieldS
    norm_num [Cert590.C]
  rw [e] at h
  exact h

theorem near_K590 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes Odd.design * Real.log (1 + y ^ 2) +
      (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
        trialSeqS Cert590.Pc Cert590.P 1 * y ≤ D58.nearCap := by
  intro y hy
  have h := D58.Cert.near_residual_field_le_d58 Cert590.first_lower hy.1 hy.2.le
  rw [Instances.d58_gRes]
  have e : (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) = 47 / 58 := by
    norm_num [Odd.design]
  rw [e]
  have e2 : D58.nearCap = -(77 / 100 : ℝ) := by norm_num [D58.nearCap]
  rw [e2]
  exact h

theorem budget_K590 {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K590.normCap + (1 - a) * K590.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K590.residualCap + t * D58.nearCap ≤
        -K590.target + Real.log 2 / 2 + K590.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K590.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

/-- The K590 certificate (vacuous residual window). -/
def second295 : SecondFieldCert Odd.design K590.target K590.residualCap D58.nearCap
    K590.secondCost (fun _ => False) where
  u := trialSeqS Cert590.Pc Cert590.P
  v := trialSeqS Cert590.Vc Cert590.V
  hu := (trialSeqS_summable Cert590.tailsP).1
  hv := (trialSeqS_summable Cert590.tailsV).1
  MX := (Cert590.MX : ℚ)
  MY := (Cert590.MY : ℚ)
  normCap := K590.normCap
  fieldCap := K590.fieldCap
  near_sup := near_K590
  norm_le := by
    have h2 : (((2 * Cert590.NP + Cert590.NV / 2 : ℚ)) : ℝ) ≤ K590.normCap := by
      norm_num [Cert590.NP, Cert590.NV, K590.normCap]
    exact Cert590.weighted_norm_le.trans h2
  field_sum := by norm_num [Cert590.MX, Cert590.MY, K590.fieldCap]
  row_sup := by
    rw [(Instances.d58_row_weights).1, (Instances.d58_row_weights).2.1,
      (Instances.d58_row_weights).2.2]
    exact row_sup_K590
  column_sup := by
    rw [(Instances.d58_column_weights).1, (Instances.d58_column_weights).2]
    exact column_sup_K590
  residual_sup := fun _ _ h => h.elim
  budget := budget_K590

/-- The K590 second record. -/
abbrev base2 : SecondTrialBounds P58 K590.target K590.residualCap D58.nearCap K590.secondCost
    (fun _ => False) := second295.bounds Odd.design_admissible

theorem base2_p : base2.p = trialSeqS Cert590.Pc Cert590.P := rfl
theorem base2_v : base2.v = trialSeqS Cert590.Vc Cert590.V := rfl
theorem base2_normCap : base2.normCap = K590.normCap := rfl

theorem duS_support : ∀ k, 41 ≤ k → duS k = 0 := fun k hk =>
  trialSeqOf_support du40 (2 ^ 24) (by rw [len_du40]; omega)
theorem dvS_support : ∀ k, 41 ≤ k → dvS k = 0 := fun k hk =>
  trialSeqOf_support dv40 (2 ^ 24) (by rw [len_dv40]; omega)

/-! ### The marked field -/

/-- The two endpoint caps of the marked field of the window, for the trial `p₀ + τ du`, `τ ∈ {0, 1}`:
the residual field plus the node correction. -/
theorem pair_caps {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hG : Gd x) :
    (resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Cert590.Pc Cert590.P) x + nodeD P58 δc x ≤ 7 / 1000) ∧
    (resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Cert590.Pc Cert590.P) x - 2 * barrierTrialT duS x +
      nodeD P58 δc x ≤ -268 / 10000) := by
  rcases Gd_split hG with hA | hB
  · have h0 := ChordPair.residual_pair_Gd 0 x hx hA hG
    have h1 := ChordPair.residual_pair_Gd 1 x hx hA hG
    rw [← G16.nodeD_eq] at h0 h1
    constructor
    · simpa using h0
    · simpa [duS] using h1
  · have h0 := ext_pair Cert590.hZ_R (d := nodeD P58 δc) (τ := 0) (Or.inl rfl) hd_node x hB
    have h1 := ext_pair Cert590.hZ_R (d := nodeD P58 δc) (τ := 1) (Or.inr rfl) hd_node x hB
    constructor
    · simpa using h0
    · simp only [one_mul] at h1
      simp only [duS]
      linarith

theorem marked_second {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hG : Gd x) :
    groupedMarkedField P58 N x - 2 * barrierTrialT (fun k => base2.p k + τ * duS k) x +
        nodeD P58 δc x ≤ ((7 / 1000 : ℝ) + τ * (-268 / 10000 - 7 / 1000)) + Real.log 2 / (P58.n N : ℝ) := by
  have hx1 : |x| ≤ 1 := abs_le.mpr hx
  rw [barrierTrialT_shift base2.p duS τ base2.p_summable duS_support hx1]
  have hn : (0 : ℝ) < P58.n N := by exact_mod_cast n_pos P58_admissible hN
  have hsq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith)
  have hcorr := div_le_div_of_nonneg_right hlog hn.le
  have hgr : gRes P58 = 53 / 58 := Instances.d58_gRes
  rw [grouped_marked_field_identity P58_admissible hN, hgr]
  obtain ⟨h0, h1⟩ := pair_caps hx hG
  unfold resFieldW at h0 h1
  rw [base2_p]
  push_cast at h0 h1
  nlinarith only [mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hτ1), mul_le_mul_of_nonneg_left h1 hτ0, hcorr]

/-! ### The near field -/

theorem near_second {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) (hG : Gd y) :
    groupedNearField P58 N y - (base2.p 1 + τ * duS 1) * y + nodeD P58 δc y ≤
      ((7 / 1000 : ℝ) + τ * (233 / 10000 - 7 / 1000) - Real.log 2) + Real.log 2 / (P58.n N : ℝ) := by
  have hGn : ∀ y ∈ Ioo (0 : ℝ) 1, Gd y →
      kt 385 ≤ realCoordinateInv y ∧ realCoordinateInv y ≤ kt 865 := fun y hy hG =>
    Gd_pos_hull hy.1 hG
  have h0 := NearDataCert.Cover.near_N0 (P := P58) P58_admissible rfl rfl (G := Gd) (d := nodeD P58 δc) hd_node hGn
    (p1 := base2.p 1) (by rw [base2_p]; simpa using p1_lower) hN hy hG
  have h1 := NearDataCert.Cover.near_N1 (P := P58) P58_admissible rfl rfl (G := Gd) (d := nodeD P58 δc) hd_node hGn
    (p1 := base2.p 1 + duS 1) (by rw [base2_p]; simpa using p1_lower') hN hy hG
  push_cast at h0 h1
  have := lin_interp_near (A := groupedNearField P58 N y + nodeD P58 δc y) (p := base2.p 1) (dd := duS 1)
    (y := y) (r0 := 7 / 1000 - Real.log 2 + Real.log 2 / (P58.n N : ℝ))
    (r1 := 233 / 10000 - Real.log 2 + Real.log 2 / (P58.n N : ℝ)) (τ := τ)
    (by linarith) (by linarith) hτ0 hτ1
  nlinarith only [this]

/-! ### The record -/

/-- The norm cap of the second record at `τ`. -/
def normCap2 (τ : ℝ) : ℝ := K590.normCap + τ * (-117647903 / 1000000000) + τ ^ 2 * (5215061 / 1000000000)

/-- **The second-population shift record** at `(τ, β)` over the K590 base: `p = p₀ + τ du`,
`v = v₀ + τ dv` (K = 40), node correction `nodeD P58 δc`, window `Gd`, column field of the cell `β`.
`X2` is the row cap of the shift, `ΔY` the column cap at `(τ, β)`; `res` and `nearC` dominate the
marked and near caps at `τ`. -/
def secondRec (X2 : ℝ)
    (hX2 : ∀ x ∈ Icc (-1 : ℝ) 1, -(4 * barrierTrialT duS x) - barrierTrialS dvS x ≤ X2)
    (target cost res nearC β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvS s) ≤ ΔY)
    (hres : (7 / 1000 : ℝ) + τ * (-268 / 10000 - 7 / 1000) ≤ res)
    (hnear : (7 / 1000 : ℝ) + τ * (233 / 10000 - 7 / 1000) - Real.log 2 ≤ nearC) :
    SecondTrialBoundsEnd P58 ∅ (colCell P58 (3 / 4) β) (nodeD P58 δc) target res nearC cost Gd :=
  shiftSecondG (D := base2) (du := duS) (dv := dvS) (K := 41) duS_support dvS_support τ (τ * X2) ΔY
    (normCap2 τ)
    (by
      have h1 := mul_le_mul_of_nonneg_left cr2_real hτ0
      have h2 := mul_le_mul_of_nonneg_left qd2_real (sq_nonneg τ)
      rw [base2_normCap, base2_p, base2_v]
      unfold normCap2
      nlinarith only [h1, h2])
    (fun x hx => by
      have hx' : x ∈ Icc (-1 : ℝ) 1 := by
        rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> constructor <;> linarith
      have := mul_le_mul_of_nonneg_left (hX2 x hx') hτ0
      nlinarith only [this])
    (Filter.Eventually.of_forall fun N s hs => by
      unfold colCell
      have := hY s ⟨hs.1.le, hs.2.le⟩
      linarith)
    (fun {N} hN {x} hx hG => by
      have := marked_second hτ0 hτ1 hN hx hG
      linarith)
    (fun {N} hN {y} hy hG => by
      have := near_second hτ0 hτ1 hN hy hG
      linarith)
    (fun ha => (notMem_empty _ ha).elim)

theorem secondRec_normCap (X2 : ℝ)
    (hX2 : ∀ x ∈ Icc (-1 : ℝ) 1, -(4 * barrierTrialT duS x) - barrierTrialS dvS x ≤ X2)
    (target cost res nearC β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvS s) ≤ ΔY)
    (hres : (7 / 1000 : ℝ) + τ * (-268 / 10000 - 7 / 1000) ≤ res)
    (hnear : (7 / 1000 : ℝ) + τ * (233 / 10000 - 7 / 1000) - Real.log 2 ≤ nearC) :
    (secondRec X2 hX2 target cost res nearC β τ ΔY hτ0 hτ1 hY hres hnear).normCap = normCap2 τ := rfl

theorem secondRec_fieldCap (X2 : ℝ)
    (hX2 : ∀ x ∈ Icc (-1 : ℝ) 1, -(4 * barrierTrialT duS x) - barrierTrialS dvS x ≤ X2)
    (target cost res nearC β τ ΔY : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hY : ∀ s ∈ Icc (0 : ℝ) 1, β * Real.log (1 + 3 / 4 * s) + 2 * (τ * barrierTrialT dvS s) ≤ ΔY)
    (hres : (7 / 1000 : ℝ) + τ * (-268 / 10000 - 7 / 1000) ≤ res)
    (hnear : (7 / 1000 : ℝ) + τ * (233 / 10000 - 7 / 1000) - Real.log 2 ≤ nearC) :
    (secondRec X2 hX2 target cost res nearC β τ ΔY hτ0 hτ1 hY hres hnear).fieldCap =
      K590.fieldCap + τ * X2 + ΔY := rfl

end

end CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond

#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond.marked_second
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond.near_second
#print axioms CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond.secondRec
