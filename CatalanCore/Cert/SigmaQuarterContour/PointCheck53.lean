module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup53_0 : ([1696,1697,1698,1699,1700,1701,1702,1703] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup53_1 : ([1704,1705,1706,1707,1708,1709,1710,1711] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup53_2 : ([1712,1713,1714,1715,1716,1717,1718,1719] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup53_3 : ([1720,1721,1722,1723,1724,1725,1726,1727] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_53 : (checkChunk 53).all pointOK = true := by
  have h : checkChunk 53 = [1696,1697,1698,1699,1700,1701,1702,1703] ++ [1704,1705,1706,1707,1708,1709,1710,1711] ++ [1712,1713,1714,1715,1716,1717,1718,1719] ++ [1720,1721,1722,1723,1724,1725,1726,1727] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup53_0, pointGroup53_1, pointGroup53_2, pointGroup53_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
