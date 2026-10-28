import CatalanCore.Uniform.Bank.Thirds.Geom
set_option Elab.async false
set_option maxRecDepth 100000

/-! Node energy of the thirds geometry:
`nodeEnergy G310 = 1587/800 - 169/200 log(13/10) + 9/400 log(3/10)` and the certified lower bound
`Inu ≤ nodeEnergy` (`Inu = 867481404213/500000000000`, the bank's `s_Inu`). -/

namespace CatalanCore.Uniform.Bank.Thirds
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem selfEnergy_RP310 :
    selfEnergy ([(1, 0, 1), (1 / 2, 1, 13 / 10)].map ratPiece) =
      1587 / 800 - 169 / 200 * Real.log (13 / 10) + 9 / 400 * Real.log (3 / 10) := by
  have l1 : Real.log (-3 / 10 : ℝ) = Real.log (3 / 10) := by
    rw [show (-3 / 10 : ℝ) = -(3 / 10) by norm_num, Real.log_neg_eq_log]
  have l2 : Real.log (-13 / 10 : ℝ) = Real.log (13 / 10) := by
    rw [show (-13 / 10 : ℝ) = -(13 / 10) by norm_num, Real.log_neg_eq_log]
  have l3 : Real.log (-1 : ℝ) = 0 := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.log_neg_eq_log, Real.log_one]
  simp only [selfEnergy, mutE, pairInteraction, pairEnergy, Hfun, ratPiece, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  norm_num [l1, l2, l3]
  ring

theorem nodeEnergy_G310 :
    G310.nodeEnergy = 1587 / 800 - 169 / 200 * Real.log (13 / 10) + 9 / 400 * Real.log (3 / 10) := by
  unfold BlockGeom.nodeEnergy
  rw [G310_rowPieces, G310_colPieces]
  unfold Decay.Nodes.nodeEnergy
  rw [selfEnergy_RP310]
  ring

end CatalanCore.Uniform.Bank.Thirds

namespace CatalanCore.Uniform.Bank.Thirds
open CatalanLambda.Cert

theorem log1310_le : Real.log (13 / 10) ≤ atS ((3 : ℝ) / 23) 10 + atT ((3 : ℝ) / 23) 10 := by
  have h := (log_atanh_bounds (x := (3 / 23 : ℝ)) (by norm_num) (by norm_num) 10).2
  have e : Real.log (1 + 3 / 23) - Real.log (1 - 3 / 23) = Real.log (13 / 10) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rwa [e] at h

/-- A lower bound of `log (3/10) = - log (10/3)`. -/
theorem log310_ge : -(atS ((7 : ℝ) / 13) 30 + atT ((7 : ℝ) / 13) 30) ≤ Real.log (3 / 10) := by
  have h := (log_atanh_bounds (x := (7 / 13 : ℝ)) (by norm_num) (by norm_num) 30).2
  have e : Real.log (1 + 7 / 13) - Real.log (1 - 7 / 13) = Real.log (10 / 3) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log (3 / 10) = - Real.log (10 / 3) := by
    rw [← Real.log_inv]; norm_num
  rw [e] at h
  rw [e2]; linarith

/-- The node energy dominates the certified `Inu` of the thirds tables. -/
theorem Inu_le_nodeEnergy : ((867481404213 / 500000000000 : ℚ) : ℝ) ≤ G310.nodeEnergy := by
  rw [nodeEnergy_G310]
  have h1 := log1310_le
  have h2 := log310_ge
  simp only [atS, atT] at h1 h2
  norm_num at h1 h2 ⊢
  linarith

end CatalanCore.Uniform.Bank.Thirds
