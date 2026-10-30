import CatalanCore.Uniform.Bank.Chi3New.Geom
set_option Elab.async false
set_option maxRecDepth 100000

/-! Node energy of the chi3 geometry: `nodeEnergy G12 = 75/32 - 9/8 log(3/2) - 1/16 log 2`, and
the certified lower bound `Inu ≤ nodeEnergy`. -/

namespace CatalanCore.Uniform.Bank.Chi3New
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem selfEnergy_RP :
    selfEnergy ([(1, 0, 1), (1 / 2, 1, 3 / 2)].map ratPiece) =
      75 / 32 - 9 / 8 * Real.log (3 / 2) - 1 / 16 * Real.log 2 := by
  have l1 : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [one_div, Real.log_inv]
  have l2 : Real.log (-1 / 2 : ℝ) = - Real.log 2 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.log_neg_eq_log, l1]
  have l3 : Real.log (-3 / 2 : ℝ) = Real.log (3 / 2) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.log_neg_eq_log]
  have l4 : Real.log (-1 : ℝ) = 0 := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.log_neg_eq_log, Real.log_one]
  simp only [selfEnergy, mutE, pairInteraction, pairEnergy, Hfun, ratPiece, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  norm_num [l1, l2, l3, l4]
  ring

theorem nodeEnergy_G12 :
    G12.nodeEnergy = 75 / 32 - 9 / 8 * Real.log (3 / 2) - 1 / 16 * Real.log 2 := by
  unfold BlockGeom.nodeEnergy
  rw [G12_rowPieces, G12_colPieces]
  unfold Decay.Nodes.nodeEnergy
  rw [selfEnergy_RP]
  ring

end CatalanCore.Uniform.Bank.Chi3New

namespace CatalanCore.Uniform.Bank.Chi3New
open CatalanLambda.Cert

theorem log32_le : Real.log (3 / 2) ≤ atS ((1 : ℝ) / 5) 14 + atT ((1 : ℝ) / 5) 14 := by
  have h := (log_atanh_bounds (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 14).2
  have e : Real.log (1 + 1 / 5) - Real.log (1 - 1 / 5) = Real.log (3 / 2) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rwa [e] at h

theorem log2_le : Real.log 2 ≤ atS ((1 : ℝ) / 3) 14 + atT ((1 : ℝ) / 3) 14 := by
  have h := (log_atanh_bounds (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 14).2
  have e : Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rwa [e] at h

/-- The node energy dominates the certified `Inu` of the chi3 tables. -/
theorem Inu_le_nodeEnergy : ((28816875853 / 15625000000 : ℚ) : ℝ) ≤ G12.nodeEnergy := by
  rw [nodeEnergy_G12]
  have h1 := log32_le
  have h2 := log2_le
  simp only [atS, atT] at h1 h2
  norm_num at h1 h2 ⊢
  linarith

end CatalanCore.Uniform.Bank.Chi3New
