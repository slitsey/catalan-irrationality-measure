module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup49_0 : ([1568,1569,1570,1571,1572,1573,1574,1575] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup49_1 : ([1576,1577,1578,1579,1580,1581,1582,1583] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup49_2 : ([1584,1585,1586,1587,1588,1589,1590,1591] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup49_3 : ([1592,1593,1594,1595,1596,1597,1598,1599] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_49 : (checkChunk 49).all pointOK = true := by
  have h : checkChunk 49 = [1568,1569,1570,1571,1572,1573,1574,1575] ++ [1576,1577,1578,1579,1580,1581,1582,1583] ++ [1584,1585,1586,1587,1588,1589,1590,1591] ++ [1592,1593,1594,1595,1596,1597,1598,1599] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup49_0, pointGroup49_1, pointGroup49_2, pointGroup49_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
