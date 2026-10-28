import CatalanCore.Uniform.Decay.Breakpoint.Cell
import CatalanCore.Uniform.Decay.PolyWire2.Kinds
set_option Elab.async false

/-!
# The breakpoint cell as a new cell kind (lane D, package D14)

`CellKind3` extends PolyWire2's `CellKind2` by `bp`, the breakpoint cell of `Breakpoint.Cell`.
`kindOk3` / `kindOk3_sound` have exactly the shape of `kindOk2` / `kindOk2_sound`, so every
statement built on `kindOk2_sound` (`nearCellT2_sound`, `lineCellOk2_sound`, ...) transfers by
replacing `kindOk2` with `kindOk3` (see `Breakpoint.Tables`).
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyWire2

/-- Cell kinds with the breakpoint expansion: `bp n side lo C Fs eS` is `bpOk` (order `n`, the
breakpoint at the left (`false`) or right (`true`) end, Bernstein bound `lo`, model `C` about the
breakpoint, error `Fs`, checked exponent `eS` with `1 ≤ (uhi - ulo) 2^eS`). -/
inductive CellKind3 where
  | base (k : CellKind2)
  | bp (n : ℕ) (side : Bool) (lo : ℚ) (C : List ℚ) (Fs : ℚ) (eS : ℕ)

/-- A cell `[ulo, uhi]` with its kind. -/
structure TCell3 where
  ulo : ℚ
  uhi : ℚ
  kind : CellKind3

/-- The Boolean test of one cell of centre `zc`, direction `dd`, half-width `h`
(the shape of `kindOk2`). -/
def kindOk3 (ps : List WP) (zc dd : CQ) (h W Rtwo cpi m' : ℚ) (eW eP : ℕ) : CellKind3 → Bool
  | .base k => kindOk2 ps zc dd h W Rtwo cpi m' eW eP k
  | .bp n side lo C Fs eS => bpOk n side ps zc dd h W Rtwo cpi lo m' C Fs eW eP eS

theorem kindOk3_sound {ps : List WP} {zc dd : CQ} {h W Rtwo cpi m' : ℚ} {eW eP : ℕ}
    {k : CellKind3} (hc : kindOk3 ps zc dd h W Rtwo cpi m' eW eP k = true) (s δ : ℝ)
    (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) *
        PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  cases k with
  | base k => exact kindOk2_sound hc s δ hs hδ
  | bp n side lo C Fs eS => (simp only [kindOk3] at hc; exact bpOk_sound hc s δ hs hδ)

end CatalanCore.Uniform.Decay.Breakpoint
