module

public import CatalanCore.Frame.Spec

/-!
# Template for a per-constant instance (copy to `CatalanFrames/<Name>/Frame.lean`)

Checklist for an instance (design 2.8), each item one file under `CatalanFrames/<Name>/`:
1. `Frame.lean`    : the `Frame` value (this file shows the shape; the numbers below are a dummy).
2. `Const.lean`    : `Frame.const = <closed form>`.
3. `Content.lean`  : `HasContent (PolyFamily.ofFrame frame) Λ`.
4. `NV*.lean`      : `HasNV (PolyFamily.ofFrame frame) rule g₁ g₂`.
5. `Instance.lean` : `HasDecay` from a `CertCore`, assembled with the above.
6. `Final.lean`    : the final statements via `measureExp` and `norm_num`.
A hybrid instance uses `PolyFamily.hybrid frame α den` in place of `ofFrame`.
Design notes (a)-(c) of `CatalanCore/Frame/Spec.lean` apply: own sigma per constant, existing
Challenge statements stay fixed, Palomar rules only.
-/

@[expose] public section

namespace CatalanFrames.Template

open CatalanCore

/-- Dummy frame showing the field syntax; not a real constant. -/
def templateFrame : Frame where
  d := 2
  μ := ![1 / 2, 1]
  w := ![-1, 1]
  norm := 1
  xs := 1 / 2
  δ0 := 1 / 4
  n0off := 0
  hμ := by intro i; fin_cases i <;> norm_num
  hμinj := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  hw := by simp [Fin.sum_univ_two]
  hnorm := by norm_num

/-- The square polynomial family of the frame (members `P_n`, degree `n`). -/
noncomputable def templateFamily : PolyFamily := PolyFamily.ofFrame templateFrame

end CatalanFrames.Template
