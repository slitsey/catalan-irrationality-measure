module

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
public import CatalanCore.Uniform.Bank.Fourths.Final
public import CatalanCore.Uniform.Bank.Fourths.Frame

@[expose] public section
set_option Elab.async false

/-! # The λ± measures from the automatic content (lane C1L)

With the automatic content `Auto.lamMinus_content_auto` / `Auto.lamPlus_content_auto` at `Λ_fin = bankData.Λ`
(selection depth `≤ 64`, `depth_le`) and the decay
`HasScaledDecay (FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)) FL.scale DL cL`, the target
bound `78219 / 2500` follows by `Auto.lambda_mu_le`.  The theorems are conditional only on the decay. -/

namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Measure
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Bank.Fourths
  CatalanCore.Uniform.Bank.FourthsContent.Level3Auto

/-- The selection depth of the λ geometry is at most `64` for a two-family frame. -/
theorem depth_le {Fr : Frame} (hd : Fr.d = 2) : FL.selectionDepth Fr 2 ≤ 64 := by
  unfold BlockGeom.selectionDepth
  rw [hd]
  decide +kernel

theorem lam_lt_DL : ((bankData.Λ : ℚ) : ℝ) < (DL : ℝ) := by
  have h : bankData.Λ < DL := by rw [bankData_Λ]; unfold DL; norm_num
  exact_mod_cast h

theorem content_auto (sgn : Bool) :
    HasScaledContent ((FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)).restrictAdm
      (fun i => i.1 % 2 = 0)) FL.scale ((bankData.Λ : ℚ) : ℝ) := by
  cases sgn
  · exact lamMinus_content_auto _ (depth_le (lambdaFrame_d false))
  · exact lamPlus_content_auto _ (depth_le (lambdaFrame_d true))


end CatalanCore.Uniform.Bank.FourthsContent.Level3Measure
