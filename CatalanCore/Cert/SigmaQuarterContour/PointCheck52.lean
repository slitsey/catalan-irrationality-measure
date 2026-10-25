module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup52_0 : ([1664,1665,1666,1667,1668,1669,1670,1671] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup52_1 : ([1672,1673,1674,1675,1676,1677,1678,1679] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup52_2 : ([1680,1681,1682,1683,1684,1685,1686,1687] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup52_3 : ([1688,1689,1690,1691,1692,1693,1694,1695] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_52 : (checkChunk 52).all pointOK = true := by
  have h : checkChunk 52 = [1664,1665,1666,1667,1668,1669,1670,1671] ++ [1672,1673,1674,1675,1676,1677,1678,1679] ++ [1680,1681,1682,1683,1684,1685,1686,1687] ++ [1688,1689,1690,1691,1692,1693,1694,1695] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup52_0, pointGroup52_1, pointGroup52_2, pointGroup52_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
