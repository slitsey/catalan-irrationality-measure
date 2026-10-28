module

public import CatalanCore.Uniform.Decay.Cells.Far
public import CatalanCore.Uniform.Decay.Cert.PilotSevenths

/-!
# Pilot (lane D6): far ray cells of the sevenths trial

`rayFarOk` on real cells of `sevRay` with the far constants `M1 = 2`, `T0 = 3/2` (illustrative
mass-cancellation constants; the hypothesis `FarHyp` is not instantiated here).  Kernel times are
recorded in NOTES.
-/

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000

namespace CatalanCore.Uniform.Decay.Cells.Pilot

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cert.Pilot

def farD : FarData := ⟨2, 3 / 2⟩

theorem far_220 : rayFarOk sevData farD (sevRay[220]!) = true := by decide +kernel
theorem far_230 : rayFarOk sevData farD (sevRay[230]!) = true := by decide +kernel
theorem far_240 : rayFarOk sevData farD (sevRay[240]!) = true := by decide +kernel
theorem far_250 : rayFarOk sevData farD (sevRay[250]!) = true := by decide +kernel
theorem far_259 : rayFarOk sevData farD (sevRay[259]!) = true := by decide +kernel
theorem far_tail : tailFarOk sevData farD = true := by decide +kernel

/-- All cells from index 213 on, in one declaration. -/
theorem far_all : ((sevRay.drop 213).all (rayFarOk sevData farD)) = true := by decide +kernel

end CatalanCore.Uniform.Decay.Cells.Pilot
