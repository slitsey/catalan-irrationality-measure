module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup48_0 : ([1536,1537,1538,1539,1540,1541,1542,1543] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup48_1 : ([1544,1545,1546,1547,1548,1549,1550,1551] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup48_2 : ([1552,1553,1554,1555,1556,1557,1558,1559] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup48_3 : ([1560,1561,1562,1563,1564,1565,1566,1567] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_48 : (checkChunk 48).all pointOK = true := by
  have h : checkChunk 48 = [1536,1537,1538,1539,1540,1541,1542,1543] ++ [1544,1545,1546,1547,1548,1549,1550,1551] ++ [1552,1553,1554,1555,1556,1557,1558,1559] ++ [1560,1561,1562,1563,1564,1565,1566,1567] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup48_0, pointGroup48_1, pointGroup48_2, pointGroup48_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
