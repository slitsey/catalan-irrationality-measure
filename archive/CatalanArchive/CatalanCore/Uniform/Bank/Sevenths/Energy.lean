import CatalanCore.Uniform.Bank.Sevenths.Geom
import CatalanLambda.Cert.LogBounds
set_option Elab.async false
set_option maxRecDepth 100000

/-! Exact node energy and certified lower bound for the sevenths geometry
`altGeom (1/6)`, with `Inu = 102691611939/62500000000`. -/

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem selfEnergy_RP7 :
    selfEnergy ([(1, 0, 1), (1 / 2, 1, 7 / 6)].map ratPiece) =
      169 / 96 - 49 / 72 * Real.log (7 / 6) + 1 / 144 * Real.log (1 / 6) := by
  have l1 : Real.log (-1 / 6 : ℝ) = Real.log (1 / 6) := by
    rw [show (-1 / 6 : ℝ) = -(1 / 6) by norm_num, Real.log_neg_eq_log]
  have l2 : Real.log (-7 / 6 : ℝ) = Real.log (7 / 6) := by
    rw [show (-7 / 6 : ℝ) = -(7 / 6) by norm_num, Real.log_neg_eq_log]
  have l3 : Real.log (-1 : ℝ) = 0 := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.log_neg_eq_log, Real.log_one]
  simp only [selfEnergy, mutE, pairInteraction, pairEnergy, Hfun, ratPiece, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  norm_num [l1, l2, l3]
  ring

theorem nodeEnergy_F7 :
    F7.nodeEnergy = 169 / 96 - 49 / 72 * Real.log (7 / 6) + 1 / 144 * Real.log (1 / 6) := by
  unfold BlockGeom.nodeEnergy
  rw [F7_rowPieces, F7_colPieces]
  unfold Decay.Nodes.nodeEnergy
  rw [selfEnergy_RP7]
  ring

end CatalanCore.Uniform.Bank.Sevenths

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanLambda.Cert

theorem log76_le : Real.log (7 / 6) ≤ atS ((1 : ℝ) / 13) 10 + atT ((1 : ℝ) / 13) 10 := by
  have h := (log_atanh_bounds (x := (1 / 13 : ℝ)) (by norm_num) (by norm_num) 10).2
  have e : Real.log (1 + 1 / 13) - Real.log (1 - 1 / 13) = Real.log (7 / 6) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rwa [e] at h

/-- A lower bound of `log (1/6) = - log 6`. -/
theorem log16_ge : -(atS ((5 : ℝ) / 7) 60 + atT ((5 : ℝ) / 7) 60) ≤ Real.log (1 / 6) := by
  have h := (log_atanh_bounds (x := (5 / 7 : ℝ)) (by norm_num) (by norm_num) 60).2
  have e : Real.log (1 + 5 / 7) - Real.log (1 - 5 / 7) = Real.log (6) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log (1 / 6) = - Real.log (6) := by
    rw [← Real.log_inv]; norm_num
  rw [e] at h
  rw [e2]; linarith

/-- The node energy dominates the certified `Inu` of the sevenths tables. -/
theorem Inu_le_nodeEnergy : ((102691611939 / 62500000000 : ℚ) : ℝ) ≤ F7.nodeEnergy := by
  rw [nodeEnergy_F7]
  have h1 := log76_le
  have h2 := log16_ge
  simp only [atS, atT] at h1 h2
  norm_num at h1 h2 ⊢
  linarith

end CatalanCore.Uniform.Bank.Sevenths

#print axioms CatalanCore.Uniform.Bank.Sevenths.Inu_le_nodeEnergy
