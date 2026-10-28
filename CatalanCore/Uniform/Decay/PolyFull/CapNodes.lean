import CatalanCore.Uniform.Decay.PolyFull.CapPair
set_option Elab.async false

/-!
# The cap integral of the node potential (lane D, package D10)

The node measure is a finite union of constant-density pieces `(w, lo, hi)` on the half line.
For rational pieces, the potential `Piece.pot` at a real point equals the potential `Wseg` of the
segment `pieceSeg p` (endpoints `lo, hi` on the real line, constant density `w (hi - lo)`), so the
cap integral of each piece is a collinear pair energy, bounded by `pairBound`.

Also: continuity of the node potential on the real line (from `Lam`).
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PairEnergy CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform

/-- A rational node piece `(w, lo, hi)`. -/
def ratPiece (p : ℚ × ℚ × ℚ) : Piece := ⟨(p.1 : ℝ), (p.2.1 : ℝ), (p.2.2 : ℝ)⟩

/-- The segment `[lo, hi]` on the real line with constant density `w (hi - lo)`. -/
def pieceSeg (p : ℚ × ℚ × ℚ) : Seg :=
  { ax := p.2.1, ay := 0, bx := p.2.2, byy := 0, coef := [p.1 * (p.2.2 - p.2.1)], M := 1, Lq := 1,
    tau := 0 }

theorem pot_param (w lo hi x : ℝ) :
    ∫ t in (0 : ℝ)..1, w * (hi - lo) * (-Real.log |x - (lo + t * (hi - lo))|) =
      (⟨w, lo, hi⟩ : Piece).pot x := by
  by_cases hc : hi - lo = 0
  · have : hi = lo := by linarith
    subst this
    simp [Piece.pot]
  · rw [intervalIntegral.integral_const_mul]
    have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => -Real.log |x - u|) hc lo
    have e : ∀ t : ℝ, lo + t * (hi - lo) = (hi - lo) * t + lo := fun t => by ring
    simp_rw [e]
    rw [h]
    have e1 : (hi - lo) * 0 + lo = lo := by ring
    have e2 : (hi - lo) * 1 + lo = hi := by ring
    rw [e1, e2, integral_neg_log_abs, smul_eq_mul]
    unfold Piece.pot
    field_simp

theorem Wseg_piece (p : ℚ × ℚ × ℚ) (x : ℝ) : Wseg (pieceSeg p) (x : ℂ) = (ratPiece p).pot x := by
  unfold Wseg
  unfold ratPiece
  rw [← pot_param (p.1 : ℝ) (p.2.1 : ℝ) (p.2.2 : ℝ) x]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hn : ‖(x : ℂ) - ((segA (pieceSeg p)).toC + (t : ℂ) * ((segB (pieceSeg p)).toC -
      (segA (pieceSeg p)).toC))‖ = |x - ((p.2.1 : ℝ) + t * ((p.2.2 : ℝ) - (p.2.1 : ℝ)))| := by
    have : (x : ℂ) - ((segA (pieceSeg p)).toC + (t : ℂ) * ((segB (pieceSeg p)).toC -
        (segA (pieceSeg p)).toC)) =
        ((x - ((p.2.1 : ℝ) + t * ((p.2.2 : ℝ) - (p.2.1 : ℝ))) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [segA, segB, pieceSeg, QC.toC]
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  simp [pieceSeg, evalL]

/-- Cap integral of the potential of a rational piece. -/
theorem cap_piece_le {r0 : ℚ} {p : ℚ × ℚ × ℚ} {u : ℚ}
    (h : pairBound (capSegOf r0) (pieceSeg p) = some u) :
    ∫ s in (0 : ℝ)..1, (ratPiece p).pot (capX r0 s) ≤ (u : ℝ) := by
  have := cap_pair_le h
  simp_rw [Wseg_piece] at this
  exact this

theorem elog_real (x t : ℝ) :
    CatalanLambda.Decay.elog (⟨x, 0⟩ : ℂ) (t : ℂ) = -Real.log |x - t| := by
  rw [← kern_eq_elog]
  unfold kern
  simp only [zero_pow two_ne_zero, add_zero]
  rw [Real.log_pow, Real.log_abs]
  push_cast
  ring

/-- On the real line, the complex potential of a node measure is the real one. -/
theorem ppotC_real (ps : List Piece) (x : ℝ) : ppotC ps (⟨x, 0⟩ : ℂ) = ppot ps x := by
  unfold ppotC ppot
  congr 1
  refine List.map_congr_left fun P _ => ?_
  simp_rw [elog_real]
  rw [integral_neg_log_abs]
  unfold Piece.pot
  ring

theorem pot_continuous (P : Piece) : Continuous P.pot := by
  unfold Piece.pot
  exact continuous_const.mul ((continuous_Lam.comp (continuous_id.sub continuous_const)).sub
    (continuous_Lam.comp (continuous_id.sub continuous_const)))

theorem ppot_continuous (ps : List Piece) : Continuous (ppot ps) := by
  induction ps with
  | nil =>
    have : ppot [] = fun _ => 0 := by funext x; simp [ppot]
    rw [this]; exact continuous_const
  | cons P ps ih =>
    have : ppot (P :: ps) = fun x => P.pot x + ppot ps x := by
      funext x; simp [ppot]
    rw [this]
    exact (pot_continuous P).add ih

/-- The node potential is continuous on the real line. -/
theorem nodePot_real_continuous (G : BlockGeom) :
    Continuous (fun x : ℝ => G.nodePot (⟨x, 0⟩ : ℂ)) := by
  have : (fun x : ℝ => G.nodePot (⟨x, 0⟩ : ℂ)) =
      fun x => (ppot G.rowPieces x + ppot G.colPieces x) / 2 := by
    funext x
    unfold BlockGeom.nodePot
    rw [ppotC_real, ppotC_real]
  rw [this]
  exact ((ppot_continuous _).add (ppot_continuous _)).div_const 2

end CatalanCore.Uniform.Decay.PolyFull
