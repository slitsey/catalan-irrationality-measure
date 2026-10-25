module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup57_0 : ([1824,1825,1826,1827,1828,1829,1830,1831] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup57_1 : ([1832,1833,1834,1835,1836,1837,1838,1839] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup57_2 : ([1840,1841,1842,1843,1844,1845,1846,1847] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup57_3 : ([1848,1849,1850,1851,1852,1853,1854,1855] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_57 : (checkChunk 57).all pointOK = true := by
  have h : checkChunk 57 = [1824,1825,1826,1827,1828,1829,1830,1831] ++ [1832,1833,1834,1835,1836,1837,1838,1839] ++ [1840,1841,1842,1843,1844,1845,1846,1847] ++ [1848,1849,1850,1851,1852,1853,1854,1855] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup57_0, pointGroup57_1, pointGroup57_2, pointGroup57_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
