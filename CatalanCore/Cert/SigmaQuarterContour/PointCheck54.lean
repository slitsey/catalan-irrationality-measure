module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup54_0 : ([1728,1729,1730,1731,1732,1733,1734,1735] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup54_1 : ([1736,1737,1738,1739,1740,1741,1742,1743] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup54_2 : ([1744,1745,1746,1747,1748,1749,1750,1751] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup54_3 : ([1752,1753,1754,1755,1756,1757,1758,1759] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_54 : (checkChunk 54).all pointOK = true := by
  have h : checkChunk 54 = [1728,1729,1730,1731,1732,1733,1734,1735] ++ [1736,1737,1738,1739,1740,1741,1742,1743] ++ [1744,1745,1746,1747,1748,1749,1750,1751] ++ [1752,1753,1754,1755,1756,1757,1758,1759] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup54_0, pointGroup54_1, pointGroup54_2, pointGroup54_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
