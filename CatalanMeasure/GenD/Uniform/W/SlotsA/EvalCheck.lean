module
public import CatalanMeasure.GenD.Uniform.W.SlotsA.LB
@[expose] public section

/-! Regression: `aVal` reproduces `proof13/fam13.py: bA` (exact finite-field nullity at the first four
points, `proof13/chk.log`) at D58 points. -/
open CatalanMeasure.GenD.Uniform.W.SlotsA CatalanMeasure.GenD CatalanMeasure.Parametric

def D58A : Parameters := ⟨58, 9, 3, 5, 3⟩
example : aApp D58A 14 167 := by unfold aApp uM0; constructor <;> decide +kernel
example : aVal D58A 14 167 = 10 := by decide +kernel
example : aVal D58A 16 191 = 12 := by decide +kernel
example : aVal D58A 20 239 = 16 := by decide +kernel
example : aVal D58A 20 241 = 20 := by decide +kernel
example : aVal D58A 12 157 = 12 := by decide +kernel
example : aVal D58A 24 293 = 26 := by decide +kernel
example : aVal D58A 30 359 = 26 := by decide +kernel
example : aVal D58A 20 251 = 25 := by decide +kernel
example : aVal D58A 20 247 = 23 := by decide +kernel
