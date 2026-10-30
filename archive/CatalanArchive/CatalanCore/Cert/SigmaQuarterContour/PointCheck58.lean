module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup58_0 : ([1856,1857,1858,1859,1860,1861,1862,1863] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup58_1 : ([1864,1865,1866,1867,1868,1869,1870,1871] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup58_2 : ([1872,1873,1874,1875,1876,1877,1878,1879] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup58_3 : ([1880,1881,1882,1883,1884,1885,1886,1887] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_58 : (checkChunk 58).all pointOK = true := by
  have h : checkChunk 58 = [1856,1857,1858,1859,1860,1861,1862,1863] ++ [1864,1865,1866,1867,1868,1869,1870,1871] ++ [1872,1873,1874,1875,1876,1877,1878,1879] ++ [1880,1881,1882,1883,1884,1885,1886,1887] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup58_0, pointGroup58_1, pointGroup58_2, pointGroup58_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
