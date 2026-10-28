import CatalanCore.Uniform.Decay.PolyWire.Link
import CatalanCore.Uniform.Decay.Cells.FarNu
set_option Elab.async false

/-!
# `FarHyp` for the node potential from a Boolean check (lane D, package D11)

For nonnegative constant-density pieces `(w, lo, hi)` with `0 ≤ lo ≤ hi ≤ Rn`, the potential
satisfies `|ppotC ps σ + pmass ps · log ‖σ‖| ≤ 2 Rn · pmass ps / ‖σ‖` for `‖σ‖ ≥ 2 Rn`
(`ppotC_far`).  Hence `|nodePot σ + Mq log ‖σ‖| ≤ 2 (Mq Rn) / ‖σ‖`, and D6's `farHyp_of_nu` gives
`FarHyp` from the Boolean test `farDataOk`.
-/

namespace CatalanCore.Uniform.Decay.PolyWire

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform
  CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.Cells

theorem elog_far {z p : ℂ} {R : ℝ} (hz0 : 0 < ‖z‖) (hp : ‖p‖ ≤ R) (hz : 2 * R ≤ ‖z‖) :
    |CatalanLambda.Decay.elog z p + Real.log ‖z‖| ≤ 2 * R / ‖z‖ := by
  have hζ : ‖p / z‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hz0]; linarith
  have hz' : z ≠ 0 := norm_pos_iff.1 hz0
  have e : ‖z - p‖ = ‖z‖ * ‖1 - p / z‖ := by
    rw [← norm_mul]; congr 1; field_simp
  have hpos : 0 < ‖1 - p / z‖ := by
    have h3 : 1 - ‖p / z‖ ≤ ‖1 - p / z‖ := by
      have := norm_sub_norm_le (1 : ℂ) (p / z); simpa using this
    linarith
  have hl : Real.log ‖z - p‖ = Real.log ‖z‖ + Real.log ‖1 - p / z‖ := by
    rw [e, Real.log_mul hz0.ne' hpos.ne']
  have := CatalanCore.Uniform.Decay.Polygon.abs_log_norm_one_sub_le hζ
  unfold CatalanLambda.Decay.elog
  rw [hl]
  have e2 : -(Real.log ‖z‖ + Real.log ‖1 - p / z‖) + Real.log ‖z‖ = -Real.log ‖1 - p / z‖ := by ring
  rw [e2, abs_neg]
  refine this.trans ?_
  rw [norm_div]
  calc 2 * (‖p‖ / ‖z‖) = 2 * ‖p‖ / ‖z‖ := by ring
    _ ≤ 2 * R / ‖z‖ := by gcongr

theorem piece_far (P : Piece) {Rn : ℝ} (hw : 0 ≤ P.w) (hlo : 0 ≤ P.lo) (hlh : P.lo ≤ P.hi)
    (hhi : P.hi ≤ Rn) {z : ℂ} (hz0 : 0 < ‖z‖) (hz : 2 * Rn ≤ ‖z‖) :
    |P.w * (∫ t in P.lo..P.hi, CatalanLambda.Decay.elog z (t : ℂ)) + P.mass * Real.log ‖z‖|
      ≤ 2 * Rn * P.mass / ‖z‖ := by
  have hint := intervalIntegrable_elog z P.lo P.hi
  have hsplit : P.w * (∫ t in P.lo..P.hi, CatalanLambda.Decay.elog z (t : ℂ)) +
      P.mass * Real.log ‖z‖ =
      P.w * ∫ t in P.lo..P.hi, (CatalanLambda.Decay.elog z (t : ℂ) + Real.log ‖z‖) := by
    rw [intervalIntegral.integral_add hint intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
    unfold Piece.mass
    ring
  rw [hsplit]
  have hb : ‖∫ t in P.lo..P.hi, (CatalanLambda.Decay.elog z (t : ℂ) + Real.log ‖z‖)‖ ≤
      (2 * Rn / ‖z‖) * |P.hi - P.lo| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le hlh] at ht
    rw [Real.norm_eq_abs]
    refine elog_far hz0 ?_ hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlo.trans ht.1.le)]
    exact ht.2.trans hhi
  rw [abs_mul, abs_of_nonneg hw]
  rw [Real.norm_eq_abs] at hb
  rw [abs_of_nonneg (sub_nonneg.2 hlh)] at hb
  unfold Piece.mass
  calc P.w * |∫ t in P.lo..P.hi, (CatalanLambda.Decay.elog z (t : ℂ) + Real.log ‖z‖)|
      ≤ P.w * ((2 * Rn / ‖z‖) * (P.hi - P.lo)) := mul_le_mul_of_nonneg_left hb hw
    _ = 2 * Rn * (P.w * (P.hi - P.lo)) / ‖z‖ := by ring

theorem ppotC_far {Rn : ℝ} :
    ∀ (ps : List Piece), (∀ P ∈ ps, 0 ≤ P.w ∧ 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ Rn) →
    ∀ {z : ℂ}, 0 < ‖z‖ → 2 * Rn ≤ ‖z‖ →
    |ppotC ps z + pmass ps * Real.log ‖z‖| ≤ 2 * Rn * pmass ps / ‖z‖
  | [], _, z, _, _ => by simp [ppotC, pmass]
  | P :: ps, h, z, hz0, hz => by
    have h1 := piece_far P (Rn := Rn) (h P List.mem_cons_self).1 (h P List.mem_cons_self).2.1
      (h P List.mem_cons_self).2.2.1 (h P List.mem_cons_self).2.2.2 hz0 hz
    have h2 := ppotC_far ps (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)) hz0 hz
    have e : ppotC (P :: ps) z + pmass (P :: ps) * Real.log ‖z‖ =
        (P.w * (∫ t in P.lo..P.hi, CatalanLambda.Decay.elog z (t : ℂ)) + P.mass * Real.log ‖z‖) +
        (ppotC ps z + pmass ps * Real.log ‖z‖) := by
      simp only [ppotC, pmass, List.map_cons, List.sum_cons]; ring
    have e2 : 2 * Rn * pmass (P :: ps) / ‖z‖ =
        2 * Rn * P.mass / ‖z‖ + 2 * Rn * pmass ps / ‖z‖ := by
      simp only [pmass, List.map_cons, List.sum_cons]; ring
    rw [e, e2]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Boolean check on a rational piece list: weights `≥ 0`, `0 ≤ lo ≤ hi ≤ Rn`. -/
def piecesOk (Rn : ℚ) (l : List (ℚ × ℚ × ℚ)) : Bool :=
  l.all fun p => decide (0 ≤ p.1) && decide (0 ≤ p.2.1) && decide (p.2.1 ≤ p.2.2) &&
    decide (p.2.2 ≤ Rn)

theorem piecesOk_sound {Rn : ℚ} {l : List (ℚ × ℚ × ℚ)} (h : piecesOk Rn l = true) :
    ∀ P ∈ l.map ratPiece, 0 ≤ P.w ∧ 0 ≤ P.lo ∧ P.lo ≤ P.hi ∧ P.hi ≤ (Rn : ℝ) := by
  intro P hP
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hP
  have := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ (p.1 : ℝ); exact_mod_cast h1
  · show (0 : ℝ) ≤ (p.2.1 : ℝ); exact_mod_cast h2
  · show (p.2.1 : ℝ) ≤ (p.2.2 : ℝ); exact_mod_cast h3
  · show (p.2.2 : ℝ) ≤ (Rn : ℝ); exact_mod_cast h4

/-- The far-field data test: pieces, `0 ≤ Rn`, `0 < T₀`, `2 Rc ≤ T₀`, `2 Rn ≤ T₀`,
`M₁ = Mq Rc + Mq Rn`. -/
def farDataOk (F : FarData) (Rn : ℚ) (RP CP : List (ℚ × ℚ × ℚ)) (D : SplineData) : Bool :=
  piecesOk Rn RP && piecesOk Rn CP && decide (0 ≤ Rn) && decide (0 < F.T0) &&
    decide (2 * D.Rc ≤ F.T0) && decide (2 * Rn ≤ F.T0) && decide (F.M1 = D.Mq * D.Rc + D.Mq * Rn)

/-- Far field of the node potential. -/
theorem nodePot_far (G₀ : BlockGeom) (RP CP : List (ℚ × ℚ × ℚ)) {Rn : ℚ}
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece)
    (hR : piecesOk Rn RP = true) (hC : piecesOk Rn CP = true) {z : ℂ} (hz0 : 0 < ‖z‖)
    (hz : 2 * (Rn : ℝ) ≤ ‖z‖) :
    |G₀.nodePot z + (G₀.totalMass : ℝ) * Real.log ‖z‖| ≤ 2 * ((G₀.totalMass : ℝ) * Rn) / ‖z‖ := by
  have h1 := ppotC_far (Rn := (Rn : ℝ)) G₀.rowPieces (hrow ▸ piecesOk_sound hR) hz0 hz
  have h2 := ppotC_far (Rn := (Rn : ℝ)) G₀.colPieces (hcol ▸ piecesOk_sound hC) hz0 hz
  rw [BlockGeom.pmass_rowPieces] at h1
  rw [BlockGeom.pmass_colPieces] at h2
  have e : G₀.nodePot z + (G₀.totalMass : ℝ) * Real.log ‖z‖ =
      ((ppotC G₀.rowPieces z + (G₀.totalMass : ℝ) * Real.log ‖z‖) +
        (ppotC G₀.colPieces z + (G₀.totalMass : ℝ) * Real.log ‖z‖)) / 2 := by
    unfold BlockGeom.nodePot; ring
  rw [e, abs_div, abs_two]
  have : |(ppotC G₀.rowPieces z + (G₀.totalMass : ℝ) * Real.log ‖z‖) +
      (ppotC G₀.colPieces z + (G₀.totalMass : ℝ) * Real.log ‖z‖)| ≤
      2 * (2 * (Rn : ℝ) * (G₀.totalMass : ℝ) / ‖z‖) := by
    have := abs_add_le (ppotC G₀.rowPieces z + (G₀.totalMass : ℝ) * Real.log ‖z‖)
      (ppotC G₀.colPieces z + (G₀.totalMass : ℝ) * Real.log ‖z‖)
    linarith
  calc _ ≤ 2 * (2 * (Rn : ℝ) * (G₀.totalMass : ℝ) / ‖z‖) / 2 := by gcongr
    _ = 2 * ((G₀.totalMass : ℝ) * Rn) / ‖z‖ := by ring

/-- **`FarHyp` from the Boolean test.** -/
theorem farHyp_of_tables (G₀ : BlockGeom) (RP CP : List (ℚ × ℚ × ℚ))
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece)
    {D : SplineData} (B : SplineData.BasicFacts D) (hMq : D.Mq = G₀.totalMass) {F : FarData}
    {Rn : ℚ} (h : farDataOk F Rn RP CP D = true) : FarHyp D G₀.nodePot F := by
  simp only [farDataOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hR, hC⟩, hRn⟩, hT0⟩, hTc⟩, hTn⟩, hM1⟩ := h
  have hMpos : 0 < D.Mq := B.hM
  refine farHyp_of_nu B F (N1 := D.Mq * Rn) (mul_nonneg hMpos.le hRn) (by rw [hM1]) hT0 hTc
    fun z hz => ?_
  have hT0R : (0 : ℝ) < F.T0 := by exact_mod_cast hT0
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hT0R hz
  have hTnR : 2 * (Rn : ℝ) ≤ F.T0 := by exact_mod_cast hTn
  have := nodePot_far G₀ RP CP hrow hcol hR hC hz0 (hTnR.trans hz)
  have hMR : (D.Mq : ℝ) = (G₀.totalMass : ℝ) := by rw [hMq]
  rw [hMR]
  push_cast
  rw [hMR]
  exact this

end CatalanCore.Uniform.Decay.PolyWire
