module

public import CatalanCore.Uniform.Decay.Cells.Assemble
public import CatalanCore.Uniform.Decay.PolyChain.Check

@[expose] public section

/-!
# `noRay`: reusing D6's `basicOk`-based oracles for the polygon chain (lane D, package D9)

The polygon chain checks `basicOkP` (no straight-ray cover).  D6's cell rules and oracles state
soundness under `D.basicOk = true`, which contains the ray cover `coverOk 0 umax rayBoxes`.
`D.noRay` is `D` with the ray data replaced by the trivially covered `umax = 0`,
`rayBoxes = [(0,0)]`; every other field is unchanged, so `D.noRay.basicOk = D.basicOkP` (`rfl`)
and `gNu D.noRay.Mq ... = gNu D.Mq ...` etc. are definitional.  All polygon rules below are
evaluated at `D.noRay`, so D6/D6b/D6c oracles are used verbatim.
-/

namespace CatalanCore.Uniform.Decay.PolyCells

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline

/-- `D` with the straight-ray data replaced by a trivially covered dummy. -/
def _root_.CatalanCore.Uniform.Decay.Cert.SplineData.noRay (D : SplineData) : SplineData :=
  { D with umax := 0, rayBoxes := [(0, 0)] }

theorem coverOk_zero : coverOk 0 0 [((0 : ℚ), (0 : ℚ))] = true := by decide

theorem basicOk_noRay {D : SplineData} (h : D.basicOkP = true) : D.noRay.basicOk = true := by
  have hc : coverOk 0 D.noRay.umax D.noRay.rayBoxes = true := coverOk_zero
  have e : D.noRay.basicOk = D.basicOkP := by
    unfold SplineData.basicOk
    rw [hc, Bool.and_true]
    rfl
  rw [e]; exact h

end CatalanCore.Uniform.Decay.PolyCells
