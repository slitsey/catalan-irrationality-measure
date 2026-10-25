module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup55_0 : ([1760,1761,1762,1763,1764,1765,1766,1767] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup55_1 : ([1768,1769,1770,1771,1772,1773,1774,1775] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup55_2 : ([1776,1777,1778,1779,1780,1781,1782,1783] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup55_3 : ([1784,1785,1786,1787,1788,1789,1790,1791] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_55 : (checkChunk 55).all pointOK = true := by
  have h : checkChunk 55 = [1760,1761,1762,1763,1764,1765,1766,1767] ++ [1768,1769,1770,1771,1772,1773,1774,1775] ++ [1776,1777,1778,1779,1780,1781,1782,1783] ++ [1784,1785,1786,1787,1788,1789,1790,1791] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup55_0, pointGroup55_1, pointGroup55_2, pointGroup55_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
