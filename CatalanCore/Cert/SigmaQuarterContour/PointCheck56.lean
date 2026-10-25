module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup56_0 : ([1792,1793,1794,1795,1796,1797,1798,1799] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup56_1 : ([1800,1801,1802,1803,1804,1805,1806,1807] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup56_2 : ([1808,1809,1810,1811,1812,1813,1814,1815] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup56_3 : ([1816,1817,1818,1819,1820,1821,1822,1823] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_56 : (checkChunk 56).all pointOK = true := by
  have h : checkChunk 56 = [1792,1793,1794,1795,1796,1797,1798,1799] ++ [1800,1801,1802,1803,1804,1805,1806,1807] ++ [1808,1809,1810,1811,1812,1813,1814,1815] ++ [1816,1817,1818,1819,1820,1821,1822,1823] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup56_0, pointGroup56_1, pointGroup56_2, pointGroup56_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
