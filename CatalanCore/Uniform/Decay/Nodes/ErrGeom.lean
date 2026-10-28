module
public import CatalanCore.Uniform.Decay.Nodes.ErrBound
public import CatalanCore.Uniform.Decay.Nodes.ErrArith
@[expose] public section

/-!
# The error terms `E1, E3, E4` of a block geometry are `O(1 + log r)`, `O(1 + log r)`, `O(r log r)`
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

theorem log_one_add_mul_le {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Real.log (1 + c * r) ≤ Real.log (1 + c) + Real.log (1 + r) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  exact Real.log_le_log (by positivity) (by nlinarith [mul_nonneg hc hr])

theorem log_mul_add_one_le {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Real.log (c * r + 1) ≤ Real.log (1 + c) + Real.log (1 + r) := by
  rw [add_comm (c * r) 1]; exact log_one_add_mul_le hc hr

theorem log_one_add_sq_le' {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Real.log (1 + (c * r) ^ 2) ≤ 2 * (Real.log (1 + c) + Real.log (1 + r)) := by
  have h1 : Real.log (1 + (c * r) ^ 2) ≤ Real.log ((1 + c * r) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [mul_nonneg hc hr])
  rw [Real.log_pow] at h1
  have := log_one_add_mul_le hc hr
  push_cast at h1
  linarith

theorem pmass_pscale (ps : List Piece) (r : ℝ) :
    pmass (ps.map fun P : Piece => (⟨P.w, P.lo * r, P.hi * r⟩ : Piece)) = r * pmass ps := by
  induction ps with
  | nil => simp [pmass]
  | cons P ps ih =>
    simp only [List.map_cons, pmass_cons, ih]
    unfold Piece.mass; ring

theorem sum_w_affine (ps : List Piece) (X Y : ℝ) :
    (ps.map fun P' => P'.w * (X + Y * (P'.hi - P'.lo))).sum =
      X * (ps.map fun P' => P'.w).sum + Y * pmass ps := by
  induction ps with
  | nil => simp [pmass]
  | cons P ps ih =>
    simp only [List.map_cons, List.sum_cons, pmass_cons, ih]
    unfold Piece.mass; ring

theorem w_sum_scale (ps : List Piece) (r : ℝ) :
    ((ps.map fun P : Piece => (⟨P.w, P.lo * r, P.hi * r⟩ : Piece)).map fun P' => P'.w).sum =
      (ps.map fun P' => P'.w).sum := by
  induction ps with
  | nil => simp
  | cons P ps ih => simp only [List.map_cons, List.sum_cons, ih]

theorem w_sum_nonneg (ps : List Piece) (h : ∀ P ∈ ps, 0 ≤ P.w) : 0 ≤ (ps.map fun P' => P'.w).sum := by
  induction ps with
  | nil => simp
  | cons P ps ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (h P (List.mem_cons_self)) (ih (fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)))

namespace BlockGeom

theorem cols_card_eq_N (G : BlockGeom) {r N nc : ℕ} (E : NodeEnum G r N nc) :
    (G.geometry r).cols.card = N := by
  rw [← E.imgQ, Finset.card_image_of_injective _ E.injQ]
  simp

set_option maxHeartbeats 8000000 in
/-- A generic "half" of the self-energy error, bounded by `C r (1 + log (1+r))`. -/
theorem half_le {r : ℝ} (hr : 1 ≤ r) {card RR RK Mm W0 Nb Bd : ℝ} (ps : List Piece)
    (hRR : 0 ≤ RR) (hRK : 0 ≤ RK) (hM : 0 ≤ Mm) (hW : 0 ≤ W0) (hNb : 0 ≤ Nb) (hBd : 0 ≤ Bd)
    (hcard0 : 0 ≤ card) (hcard : card ≤ Nb * r) (hpm : pmass ps = r * Mm)
    (hws : (ps.map fun P' => P'.w).sum = W0) :
    (card * (RR * (3 * Real.log (Bd * r + 1))) +
        (ps.map fun P' => P'.w * (6 * pmass ps +
          RR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum)
      + (RK * (card + r * Mm) + card) * Real.log r ≤
    (3 * Nb * RR * (Real.log (1 + Bd) + 1) + 6 * Mm * W0 + 5 * RR * Mm * (Real.log (1 + Bd) + 1)
      + RK * (Nb + Mm) + Nb) * r * (1 + Real.log (1 + r)) := by
  set L := Real.log (1 + r) with hL
  set lB := Real.log (1 + Bd) with hlB
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hlB0 : 0 ≤ lB := Real.log_nonneg (by linarith)
  have hlogr : Real.log r ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have h1 : Real.log (Bd * r + 1) ≤ lB + L := log_mul_add_one_le hBd (by linarith)
  have h2 : Real.log (1 + (Bd * r) ^ 2) ≤ 2 * (lB + L) := log_one_add_sq_le' hBd (by linarith)
  have h1' : 0 ≤ Real.log (Bd * r + 1) := Real.log_nonneg (by nlinarith [mul_nonneg hBd (by linarith : (0:ℝ) ≤ r)])
  have h2' : 0 ≤ Real.log (1 + (Bd * r) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (Bd * r)])
  have hsum : (ps.map fun P' => P'.w * (6 * pmass ps +
          RR * (5 * ((P'.hi - P'.lo) * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))))).sum =
      6 * pmass ps * W0 + (RR * (5 * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) * pmass ps := by
    have := sum_w_affine ps (6 * pmass ps) (RR * (5 * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2))))
    rw [hws] at this
    rw [← this]
    refine congrArg List.sum (List.map_congr_left (fun P _ => ?_))
    ring
  rw [hsum, hpm]
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hu : 1 ≤ 1 + L := by linarith
  have a1 : card * (RR * (3 * Real.log (Bd * r + 1))) ≤ 3 * Nb * RR * (lB + 1) * r * (1 + L) := by
    have : card * (RR * (3 * Real.log (Bd * r + 1))) ≤ (Nb * r) * (RR * (3 * (lB + L))) := by
      apply mul_le_mul hcard (mul_le_mul_of_nonneg_left (by linarith) hRR) (by positivity)
        (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hNb hRR) hr0) (mul_nonneg hlB0 hL0),
      mul_nonneg (mul_nonneg hNb hRR) hr0, mul_nonneg (mul_nonneg (mul_nonneg hNb hRR) hr0) hlB0,
      mul_nonneg (mul_nonneg (mul_nonneg hNb hRR) hr0) hL0]
  have a2 : 6 * (r * Mm) * W0 ≤ 6 * Mm * W0 * r * (1 + L) := by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM hW) hr0) hL0, mul_nonneg (mul_nonneg hM hW) hr0]
  have a3 : (RR * (5 * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) * (r * Mm) ≤
      5 * RR * Mm * (lB + 1) * r * (1 + L) := by
    have : (RR * (5 * ((1 / 2) * Real.log (1 + (Bd * r) ^ 2)))) ≤ RR * (5 * (lB + L)) := by
      apply mul_le_mul_of_nonneg_left _ hRR
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ r * Mm)
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hRR hM) hr0) (mul_nonneg hlB0 hL0),
      mul_nonneg (mul_nonneg hRR hM) hr0, mul_nonneg (mul_nonneg (mul_nonneg hRR hM) hr0) hlB0,
      mul_nonneg (mul_nonneg (mul_nonneg hRR hM) hr0) hL0]
  have a4 : (RK * (card + r * Mm) + card) * Real.log r ≤ (RK * (Nb + Mm) + Nb) * r * (1 + L) := by
    have hc1 : RK * (card + r * Mm) + card ≤ (RK * (Nb + Mm) + Nb) * r := by
      nlinarith [mul_le_mul_of_nonneg_left hcard hRK]
    have := mul_le_mul hc1 (hlogr.trans (by linarith : L ≤ 1 + L)) hlogr0 (by positivity)
    nlinarith [this]
  nlinarith [a1, a2, a3, a4]

end BlockGeom

theorem pieces_w_nonneg (B : BlockCollection) : ∀ P ∈ B.pieces, 0 ≤ P.w := by
  intro P hP
  unfold BlockCollection.pieces at hP
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
  show (0 : ℝ) ≤ 1 / ((B.block i).d : ℝ)
  positivity

namespace BlockGeom

/-- Constants of the error bound (depending only on the block data and `Bd, a0, m0`). -/
noncomputable def C1 (G : BlockGeom) (Bd a0 m0 : ℝ) : ℝ :=
  ((G.rowConstR : ℝ) + G.colConstR) * (6 * |Real.log m0| + 3 * Real.log (1 + (a0 + Bd))) +
    3 * ((G.rowConstR : ℝ) + G.colConstR) + ((G.rowConst : ℝ) + G.colConst)

noncomputable def C3 (G : BlockGeom) (Bd : ℝ) : ℝ :=
  3 * ((G.rowConstR : ℝ) + G.colConstR) * Real.log (1 + Bd) + 4 +
    3 * ((G.rowConstR : ℝ) + G.colConstR) + ((G.rowConst : ℝ) + G.colConst)

theorem E1_nonneg (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd a0 m0 : ℝ} (hBd0 : 0 ≤ Bd)
    (ha1 : 1 ≤ a0) : 0 ≤ G.E1 r Bd a0 m0 := by
  unfold E1
  have : 0 ≤ Real.log (1 + (a0 + Bd) * r) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (a0 + Bd) * r := by positivity
    linarith)
  have : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  positivity

theorem E1_le (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd a0 m0 : ℝ} (hBd0 : 0 ≤ Bd)
    (ha1 : 1 ≤ a0) : G.E1 r Bd a0 m0 ≤ G.C1 Bd a0 m0 * (1 + Real.log (1 + r)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL0 : 0 ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
  have hlogr : Real.log r ≤ Real.log (1 + (r : ℝ)) := Real.log_le_log (by linarith) (by linarith)
  have hlogr0 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr1
  have h1 := log_one_add_mul_le (c := a0 + Bd) (r := r) (by linarith) hr0
  have hc0 : 0 ≤ Real.log (1 + (a0 + Bd)) := Real.log_nonneg (by linarith)
  have hD : (0 : ℝ) ≤ (G.rowConstR : ℝ) + G.colConstR := by positivity
  have hK : (0 : ℝ) ≤ (G.rowConst : ℝ) + G.colConst := by positivity
  unfold E1 C1
  nlinarith [mul_nonneg hD hL0, mul_nonneg hK hL0, mul_nonneg hD (abs_nonneg (Real.log m0)),
    mul_nonneg hD hc0, mul_nonneg (mul_nonneg hD hc0) hL0,
    mul_nonneg (mul_nonneg hD (abs_nonneg (Real.log m0))) hL0,
    mul_le_mul_of_nonneg_left h1 hD, mul_le_mul_of_nonneg_left hlogr hK]

theorem E3_nonneg (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ} (hBd0 : 0 ≤ Bd) :
    0 ≤ G.E3 r Bd := by
  unfold E3
  have : 0 ≤ Real.log (Bd * r + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ Bd * r := by positivity
    linarith)
  have : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  positivity

theorem E3_le (G : BlockGeom) {r : ℕ} (hr : 0 < r) {Bd : ℝ} (hBd0 : 0 ≤ Bd) :
    G.E3 r Bd ≤ G.C3 Bd * (1 + Real.log (1 + r)) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL0 : 0 ≤ Real.log (1 + (r : ℝ)) := Real.log_nonneg (by linarith)
  have hlogr : Real.log r ≤ Real.log (1 + (r : ℝ)) := Real.log_le_log (by linarith) (by linarith)
  have h1 := log_mul_add_one_le (c := Bd) (r := r) hBd0 hr0
  have hc0 : 0 ≤ Real.log (1 + Bd) := Real.log_nonneg (by linarith)
  have hD : (0 : ℝ) ≤ (G.rowConstR : ℝ) + G.colConstR := by positivity
  have hK : (0 : ℝ) ≤ (G.rowConst : ℝ) + G.colConst := by positivity
  unfold E3 C3
  nlinarith [mul_nonneg hD hL0, mul_nonneg hK hL0, mul_nonneg hD hc0,
    mul_nonneg (mul_nonneg hD hc0) hL0,
    mul_le_mul_of_nonneg_left h1 hD, mul_le_mul_of_nonneg_left hlogr hK]

end BlockGeom

namespace BlockGeom

theorem totalMass_nonneg' (G : BlockGeom) : (0 : ℝ) ≤ (G.totalMass : ℝ) := by
  have : 0 ≤ G.totalMass := by
    unfold BlockGeom.totalMass BlockGeom.gamma BlockGeom.beta
    have := G.common_pos
    have h2 : 0 ≤ G.row.mass := by
      unfold BlockCollection.mass
      exact Finset.sum_nonneg (fun i _ => (G.row.block i).mass_pos.le)
    linarith
  exact_mod_cast this

/-- Row/column weight sums of the limiting measures (independent of `r`). -/
noncomputable def Wrow (G : BlockGeom) : ℝ := (G.rowPieces.map fun P' => P'.w).sum
noncomputable def Wcol (G : BlockGeom) : ℝ := (G.colPieces.map fun P' => P'.w).sum

theorem Wrow_nonneg (G : BlockGeom) : 0 ≤ G.Wrow := by
  unfold Wrow rowPieces
  refine w_sum_nonneg _ (fun P hP => ?_)
  rcases List.mem_append.mp hP with h | h
  · exact pieces_w_nonneg G.common P h
  · exact pieces_w_nonneg G.row P h

theorem Wcol_nonneg (G : BlockGeom) : 0 ≤ G.Wcol := by
  unfold Wcol colPieces
  refine w_sum_nonneg _ (fun P hP => ?_)
  rcases List.mem_append.mp hP with h | h
  · exact pieces_w_nonneg G.common P h
  · exact pieces_w_nonneg G.column P h

/-- The `r log r` constant of the self-energy error. -/
noncomputable def C4 (G : BlockGeom) (Bd : ℝ) : ℝ :=
  (3 * ((G.totalMass : ℝ) + G.rowConst) * G.rowConstR * (Real.log (1 + Bd) + 1)
      + 6 * (G.totalMass : ℝ) * G.Wrow + 5 * G.rowConstR * (G.totalMass : ℝ) * (Real.log (1 + Bd) + 1)
      + G.rowConst * (((G.totalMass : ℝ) + G.rowConst) + G.totalMass) + ((G.totalMass : ℝ) + G.rowConst)) +
  (3 * ((G.totalMass : ℝ) + G.rowConst) * G.colConstR * (Real.log (1 + Bd) + 1)
      + 6 * (G.totalMass : ℝ) * G.Wcol + 5 * G.colConstR * (G.totalMass : ℝ) * (Real.log (1 + Bd) + 1)
      + G.colConst * (((G.totalMass : ℝ) + G.rowConst) + G.totalMass) + ((G.totalMass : ℝ) + G.rowConst))

theorem C4_nonneg (G : BlockGeom) (Bd : ℝ) (hBd0 : 0 ≤ Bd) : 0 ≤ G.C4 Bd := by
  have hM := G.totalMass_nonneg'
  have hl : 0 ≤ Real.log (1 + Bd) := Real.log_nonneg (by linarith)
  have := G.Wrow_nonneg
  have := G.Wcol_nonneg
  unfold C4
  positivity

theorem pmass_rowU (G : BlockGeom) (r : ℕ) : pmass (G.rowU r) = r * (G.totalMass : ℝ) := by
  rw [G.rowU_eq r, pmass_pscale, G.pmass_rowPieces]

theorem pmass_colU (G : BlockGeom) (r : ℕ) : pmass (G.colU r) = r * (G.totalMass : ℝ) := by
  rw [G.colU_eq r, pmass_pscale, G.pmass_colPieces]

set_option maxHeartbeats 8000000 in
theorem E4_le (G : BlockGeom) {r N nc : ℕ} (hr : 0 < r) (E : NodeEnum G r N nc) {Bd : ℝ}
    (hBd0 : 0 ≤ Bd) :
    G.E4 r Bd ≤ G.C4 Bd * r * (1 + Real.log (1 + r)) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM := G.totalMass_nonneg'
  have hNM : |(N : ℝ) - (G.totalMass : ℝ) * r| ≤ (G.rowConst : ℝ) := by
    have := G.card_rows_bound r
    rw [G.rows_card_eq_N E] at this
    exact this
  have hN : (N : ℝ) ≤ ((G.totalMass : ℝ) + G.rowConst) * r := by
    have := (abs_le.mp hNM).2
    have hK : (0 : ℝ) ≤ G.rowConst := Nat.cast_nonneg _
    nlinarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hrow := half_le (r := r) hr1 (card := (N : ℝ)) (RR := (G.rowConstR : ℝ))
    (RK := (G.rowConst : ℝ)) (Mm := (G.totalMass : ℝ)) (W0 := G.Wrow)
    (Nb := (G.totalMass : ℝ) + G.rowConst) (Bd := Bd) (G.rowU r) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hM G.Wrow_nonneg (by positivity) hBd0 hN0 hN (G.pmass_rowU r)
    (by rw [G.rowU_eq r, w_sum_scale]; rfl)
  have hcol := half_le (r := r) hr1 (card := (N : ℝ)) (RR := (G.colConstR : ℝ))
    (RK := (G.colConst : ℝ)) (Mm := (G.totalMass : ℝ)) (W0 := G.Wcol)
    (Nb := (G.totalMass : ℝ) + G.rowConst) (Bd := Bd) (G.colU r) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hM G.Wcol_nonneg (by positivity) hBd0 hN0 hN (G.pmass_colU r)
    (by rw [G.colU_eq r, w_sum_scale]; rfl)
  have e1 := G.rows_card_eq_N E
  have e2 := G.cols_card_eq_N E
  unfold E4 C4
  rw [e1, e2]
  linarith [hrow, hcol]

end BlockGeom

end CatalanCore.Uniform
