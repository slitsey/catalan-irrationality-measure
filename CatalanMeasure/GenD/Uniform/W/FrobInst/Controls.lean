module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.All
@[expose] public section
set_option Elab.async false

/-!
# Controls (non-vacuity) for the instances

Design D58 = `(58, 9, 3, 5, 3)`.

* Theorem M window holds at `N = 4`, `p = 97`, with `mCount = 8` (17 free coordinates, 9 holes);
* Frobenius product, leading cell `N = 4`, `p = 89`: `K = 3`, `lo = 9`, `dP + 1 = 11`; the closed
  seen set has exactly two elements, so the bound is `11 * (3 - 2) = 11`, the true nullity there
  (KERNEL-FAMILY-THEOREM, example).
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open CatalanMeasure.Parametric

def d58 : Parameters := ⟨58, 9, 3, 5, 3⟩

theorem d58_mwin : MWin d58 4 97 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem d58_app : MApp d58 4 97 := ⟨by decide, by decide, d58_mwin⟩

theorem d58_mcount : mCount d58 4 97 = 8 := by decide

theorem d58_seen : (seenSet d58 4 89 9 (9 + 11)).card = 2 := by decide +kernel

theorem d58_good : FrobGood d58 4 89 3 9 11 0 := by
  intro k hk
  refine ⟨?_, ?_⟩ <;> (have : k = 0 ∨ k = 1 ∨ k = 2 := by omega) <;>
    rcases this with rfl | rfl | rfl <;> decide

end CatalanMeasure.GenD.Uniform.W.FrobInst
