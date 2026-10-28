module
public import CatalanCore.Uniform.Frame.Deletion
public import CatalanCore.Uniform.Frame.Block
@[expose] public section

/-!
# The bounded-selector window for a block geometry (Part 1, Theorem `part1`, window statement)

The all-common-deletion minor estimate `HasAllMinorDecay` (for the actual unscaled pencil and
every common principal deletion) gives, by the determinant expansion in `Deletion`, the
epsilon-window `exp (-(c+ε) r)` contract `HasScaledDecay` for the `BlockGeom` family, with degree
budget `γ r + n_C` (common mass `γ`).  No new analysis: the window cost is the single constant
`c` (no `r |J| log r` penalty), because the deleted nodes were restored before discrepancy.
-/

namespace CatalanCore.Uniform
open Finset

/-- **Bounded-selector window** for a block geometry from the all-minor estimate. -/
theorem BlockGeom.hasScaledDecay_of_allMinor (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {D c : ℝ} (hc : 0 ≤ c)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c) :
    HasScaledDecay (G.family Fr depth) G.scale D c := by
  have hγ : (0 : ℝ) ≤ (G.common.mass : ℝ) := by
    exact_mod_cast G.common_pos.le
  have hcount : ∀ r, (((G.geometry r).C.card : ℕ) : ℝ) ≤ (G.common.mass : ℝ) * r + G.common.n := by
    intro r
    have := (G.card_common r).2
    exact_mod_cast this
  exact NodeFamily.scaledDecay_of_all_minors G.geometry Fr depth hc hγ
    (Nat.cast_nonneg _) hcount hminor

end CatalanCore.Uniform
