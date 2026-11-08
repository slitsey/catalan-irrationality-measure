module

public import CatalanCore.Uniform.Decay.PolyWire.Link

@[expose] public section
set_option Elab.async false

/-!
# Merged node pieces (ledger B05b)

For banks with `CP = RP` the node measure `nodeSegs RP RP` lists every node piece twice.  `nuMerge RP`
lists it once, with the doubled weight, and `nuPot_nuMerge` shows the same potential (linearity of the
segment integral in the weight, `PolyWire.piece_seg_int`).  A cell list `cellPieces D (nuMerge RP)` is
`|RP|` pieces shorter than `cellPieces D (nodeSegs RP RP)`, and a cell costs time linear in its list.
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset Set intervalIntegral CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.Tools

/-- The node pieces of `RP` once, with doubled weight (the segments of `nodeSegs RP RP`, merged). -/
def nuMerge (RP : List (ℚ × ℚ × ℚ)) : List Seg :=
  RP.map fun p => nodeSegHalf (2 * p.1, p.2)

/-- **B05b.** The merged node list has the potential of `nodeSegs RP RP`. -/
theorem nuPot_nuMerge (RP : List (ℚ × ℚ × ℚ)) (z : ℂ) :
    nuPot (nuMerge RP) z = nuPot (nodeSegs RP RP) z := by
  have key : ∀ (c : ℚ) (l : List (ℚ × ℚ × ℚ)),
      ((l.map fun p => nodeSegHalf (c * p.1, p.2)).map (fun sg =>
        ∫ t in (0 : ℝ)..1, ratPoly sg.coef t *
          (-Real.log ‖z - ((⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩ : ℂ) + (t : ℂ) *
            ((⟨(sg.bx : ℝ), (sg.byy : ℝ)⟩ : ℂ) - ⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩))‖))).sum
      = (l.map fun p => ((c * p.1 : ℚ) : ℝ) / 2 * ∫ u in (p.2.1 : ℝ)..(p.2.2 : ℝ),
          CatalanLambda.Decay.elog z (u : ℂ)).sum := by
    intro c l
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun p _ => piece_seg_int (c * p.1, p.2) z
  unfold nuPot nuMerge nodeSegs
  have h1 := key 2 RP
  have h2 := key 1 RP
  have e1 : (RP.map nodeSegHalf) = RP.map fun p => nodeSegHalf (1 * p.1, p.2) := by
    refine List.map_congr_left fun p _ => ?_
    simp
  rw [h1, List.map_append, List.sum_append, e1, h2]
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  push_cast
  ring

end CatalanCore.Uniform.Decay.PolyWire3
