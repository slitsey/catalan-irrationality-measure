module

public import CatalanCore.Uniform.Decay.PolyFull.CapNodes
public import CatalanCore.Uniform.Decay.NearCells.Link

@[expose] public section
set_option Elab.async false

/-!
# The node potential as a list of polynomial segments (lane D, package D11)

For rational node pieces `RP`, `CP` (`(w, lo, hi)`), `nodeSegs RP CP` lists the segments
`[lo, hi]` of the real line with the constant density `w (hi - lo) / 2`, and
`nodePot_eq_nuPot` shows `G₀.nodePot = nuPot (nodeSegs RP CP)` as soon as
`G₀.rowPieces = RP.map ratPiece`, `G₀.colPieces = CP.map ratPiece`.  This is the link `hV`
that D6b's cell rules need.
-/

namespace CatalanCore.Uniform.Decay.PolyWire

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull
  CatalanCore.Uniform.Decay.Tools

/-- Half of the piece `(w, lo, hi)` as a segment (density `w (hi - lo) / 2`, constant). -/
def nodeSegHalf (p : ℚ × ℚ × ℚ) : Seg :=
  { ax := p.2.1, ay := 0, bx := p.2.2, byy := 0, coef := [p.1 * (p.2.2 - p.2.1) / 2],
    M := |p.1 * (p.2.2 - p.2.1) / 2|, Lq := p.2.2 - p.2.1, tau := 0 }

/-- The node measure `(μ_R + μ_Q)/2` as segments. -/
def nodeSegs (RP CP : List (ℚ × ℚ × ℚ)) : List Seg := RP.map nodeSegHalf ++ CP.map nodeSegHalf

theorem piece_seg_int (p : ℚ × ℚ × ℚ) (z : ℂ) :
    ∫ t in (0 : ℝ)..1, ratPoly (nodeSegHalf p).coef t *
      (-Real.log ‖z - ((⟨((nodeSegHalf p).ax : ℝ), ((nodeSegHalf p).ay : ℝ)⟩ : ℂ) + (t : ℂ) *
        ((⟨((nodeSegHalf p).bx : ℝ), ((nodeSegHalf p).byy : ℝ)⟩ : ℂ) -
          ⟨((nodeSegHalf p).ax : ℝ), ((nodeSegHalf p).ay : ℝ)⟩))‖) =
    (p.1 : ℝ) / 2 * ∫ u in (p.2.1 : ℝ)..(p.2.2 : ℝ), CatalanLambda.Decay.elog z (u : ℂ) := by
  have hrp : ∀ t : ℝ, ratPoly (nodeSegHalf p).coef t =
      (p.1 : ℝ) * ((p.2.2 : ℝ) - p.2.1) / 2 := by
    intro t
    simp [ratPoly, coeffs, nodeSegHalf]
  have hpt : ∀ t : ℝ, -Real.log ‖z - ((⟨((nodeSegHalf p).ax : ℝ), ((nodeSegHalf p).ay : ℝ)⟩ : ℂ) +
      (t : ℂ) * ((⟨((nodeSegHalf p).bx : ℝ), ((nodeSegHalf p).byy : ℝ)⟩ : ℂ) -
          ⟨((nodeSegHalf p).ax : ℝ), ((nodeSegHalf p).ay : ℝ)⟩))‖ =
      CatalanLambda.Decay.elog z (((p.2.1 : ℝ) + t * ((p.2.2 : ℝ) - p.2.1) : ℝ) : ℂ) := by
    intro t
    unfold CatalanLambda.Decay.elog
    congr 3
    apply Complex.ext <;> simp [nodeSegHalf]
  simp_rw [hrp, hpt]
  set lo : ℝ := (p.2.1 : ℝ)
  set hi : ℝ := (p.2.2 : ℝ)
  set w : ℝ := (p.1 : ℝ)
  by_cases hc : hi - lo = 0
  · have : hi = lo := by linarith
    rw [this]
    simp
  · rw [intervalIntegral.integral_const_mul]
    have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => CatalanLambda.Decay.elog z (u : ℂ)) hc lo
    have e : ∀ t : ℝ, lo + t * (hi - lo) = (hi - lo) * t + lo := fun t => by ring
    simp_rw [e]
    rw [h]
    have e1 : (hi - lo) * 0 + lo = lo := by ring
    have e2 : (hi - lo) * 1 + lo = hi := by ring
    rw [e1, e2, smul_eq_mul]
    field_simp

/-- **`hV`**: the node potential is the potential of the segment list `nodeSegs RP CP`. -/
theorem nodePot_eq_nuPot (G₀ : BlockGeom) (RP CP : List (ℚ × ℚ × ℚ))
    (hrow : G₀.rowPieces = RP.map ratPiece) (hcol : G₀.colPieces = CP.map ratPiece) (z : ℂ) :
    G₀.nodePot z = nuPot (nodeSegs RP CP) z := by
  have key : ∀ l : List (ℚ × ℚ × ℚ), ppotC (l.map ratPiece) z =
      (l.map fun p => (p.1 : ℝ) * ∫ u in (p.2.1 : ℝ)..(p.2.2 : ℝ),
        CatalanLambda.Decay.elog z (u : ℂ)).sum := by
    intro l
    unfold ppotC
    rw [List.map_map]
    rfl
  have key2 : ∀ l : List (ℚ × ℚ × ℚ), (l.map nodeSegHalf).map (fun sg =>
      ∫ t in (0 : ℝ)..1, ratPoly sg.coef t *
        (-Real.log ‖z - ((⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩ : ℂ) + (t : ℂ) *
          ((⟨(sg.bx : ℝ), (sg.byy : ℝ)⟩ : ℂ) - ⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩))‖)) =
      l.map fun p => (p.1 : ℝ) / 2 * ∫ u in (p.2.1 : ℝ)..(p.2.2 : ℝ),
        CatalanLambda.Decay.elog z (u : ℂ) := by
    intro l
    rw [List.map_map]
    exact List.map_congr_left fun p _ => piece_seg_int p z
  unfold BlockGeom.nodePot
  rw [hrow, hcol, key, key]
  unfold nuPot nodeSegs
  rw [List.map_append, List.sum_append, key2, key2]
  have h1 : ∀ l : List (ℚ × ℚ × ℚ), (l.map fun p => (p.1 : ℝ) / 2 * ∫ u in (p.2.1 : ℝ)..(p.2.2 : ℝ),
        CatalanLambda.Decay.elog z (u : ℂ)).sum =
      (l.map fun p => (p.1 : ℝ) * ∫ u in (p.2.1 : ℝ)..(p.2.2 : ℝ),
        CatalanLambda.Decay.elog z (u : ℂ)).sum / 2 := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; ring
  rw [h1, h1]
  ring

end CatalanCore.Uniform.Decay.PolyWire
