import CatalanCore.Uniform.Decay.PolyFull.CapG
import CatalanCore.Uniform.Decay.Cert.PilotSevenths
set_option Elab.async false
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 50

/-!
# Pilot (lane D, package D10): the cap lower bound on the sevenths trial

`capGokOf` on the 27 pieces of the sevenths trial and illustrative rational node pieces (the real
node pieces are not instantiated here; this measures the kernel cost of the 27 + #pieces pair
bounds).  `G = -1000` only tests that the evaluation succeeds; the printed bound is in `PilotEval`.
-/

namespace CatalanCore.Uniform.Decay.PolyFull.Pilot

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cert.Pilot

def RPp : List (ℚ × ℚ × ℚ) := [(1 / 2, 0, 1), (1 / 4, 1, 3), (1 / 8, 3, 7)]
def CPp : List (ℚ × ℚ × ℚ) := [(1 / 2, 0, 1), (1 / 3, 1, 4)]

theorem cap_pilot : capGokOf RPp CPp sevData (-1000) = true := by decide +kernel

end CatalanCore.Uniform.Decay.PolyFull.Pilot
