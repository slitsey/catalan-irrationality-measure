module
public import CatalanFrames.Thirds.Window
public import CatalanCore.Measure.Pinned
@[expose] public section
open CatalanCore
namespace CatalanFrames.HybGen
/-- Prime-class and window data are parameters; no modulus-six wrapper is used. -/
theorem measure_of_class_window (Fam : PolyFamily) (M : ℕ) (S : Finset (ZMod M))
    {Λ D c E : ℚ} (hC : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ))
    (hΛD : Λ < D) (hc : 0 < c) (hs : D-Λ < 1)
    (hNV : HasNVPinC Fam (Thirds.ClsIn M S) (Thirds.PowBad 2) 1 2)
    (hw : HasWindowC (Thirds.ClsIn M S) (Thirds.PowBad 2) 1)
    (hE : c/(D-Λ) ≤ E) : Fam.MeasureLB (E : ℝ) := by
  have hNV' : HasNVPinC Fam (Thirds.ClsIn M S) (Thirds.PowBad 2)
      ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) := by simpa using hNV
  have hw' : HasWindowC (Thirds.ClsIn M S) (Thirds.PowBad 2) ((1 : ℚ) : ℝ) := by simpa using hw
  exact Measure.measure_of_family_pin_leC Fam (α := 1) (β := 2) (s := 1) hC hD hΛD hc
    (by norm_num) (by norm_num) (by linarith) hNV' hw' hE
end CatalanFrames.HybGen
#print axioms CatalanFrames.HybGen.measure_of_class_window
