module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup51_0 : ([1632,1633,1634,1635,1636,1637,1638,1639] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup51_1 : ([1640,1641,1642,1643,1644,1645,1646,1647] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup51_2 : ([1648,1649,1650,1651,1652,1653,1654,1655] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup51_3 : ([1656,1657,1658,1659,1660,1661,1662,1663] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_51 : (checkChunk 51).all pointOK = true := by
  have h : checkChunk 51 = [1632,1633,1634,1635,1636,1637,1638,1639] ++ [1640,1641,1642,1643,1644,1645,1646,1647] ++ [1648,1649,1650,1651,1652,1653,1654,1655] ++ [1656,1657,1658,1659,1660,1661,1662,1663] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup51_0, pointGroup51_1, pointGroup51_2, pointGroup51_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
