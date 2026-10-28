module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.MFinal
@[expose] public section
set_option Elab.async false

/-!
# Banked Theorem M

`mInstLB P hP` is the `NullityLB` of Theorem M on its natural window `MApp`
(`p ∉ {3, 1291}` and `MWin`), for any admissible design.  It can be added to a family list
(`NullityLB.supList`) next to `Thin.thinLB`.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
noncomputable section

/-- The window of Theorem M. -/
def MApp (P : Parameters) (N p : ℕ) : Prop := p ≠ 3 ∧ p ≠ 1291 ∧ MWin P N p

/-- Theorem M as a banked nullity lower bound (any admissible design). -/
def mInstLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  theoremMInstLB P hP (MApp P) (fun _ _ _ _ _ _ hA => hA)

theorem mCount_le_mInstLB (P : Parameters) (hP : Admissible P) {N p : ℕ} (hA : MApp P N p) :
    mCount P N p ≤ (mInstLB P hP).kap N p := by
  classical
  simp [mInstLB, theoremMInstLB, theoremMLB, NullityLB.ofWindow, hA]

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
