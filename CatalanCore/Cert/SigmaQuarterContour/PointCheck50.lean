module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup50_0 : ([1600,1601,1602,1603,1604,1605,1606,1607] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup50_1 : ([1608,1609,1610,1611,1612,1613,1614,1615] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup50_2 : ([1616,1617,1618,1619,1620,1621,1622,1623] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup50_3 : ([1624,1625,1626,1627,1628,1629,1630,1631] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_50 : (checkChunk 50).all pointOK = true := by
  have h : checkChunk 50 = [1600,1601,1602,1603,1604,1605,1606,1607] ++ [1608,1609,1610,1611,1612,1613,1614,1615] ++ [1616,1617,1618,1619,1620,1621,1622,1623] ++ [1624,1625,1626,1627,1628,1629,1630,1631] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup50_0, pointGroup50_1, pointGroup50_2, pointGroup50_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
