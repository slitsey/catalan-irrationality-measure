module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup59_0 : ([1888,1889,1890,1891,1892,1893,1894,1895] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup59_1 : ([1896,1897,1898,1899,1900,1901,1902,1903] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup59_2 : ([1904,1905,1906,1907,1908,1909,1910,1911] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup59_3 : ([1912,1913,1914,1915,1916,1917,1918,1919] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_59 : (checkChunk 59).all pointOK = true := by
  have h : checkChunk 59 = [1888,1889,1890,1891,1892,1893,1894,1895] ++ [1896,1897,1898,1899,1900,1901,1902,1903] ++ [1904,1905,1906,1907,1908,1909,1910,1911] ++ [1912,1913,1914,1915,1916,1917,1918,1919] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup59_0, pointGroup59_1, pointGroup59_2, pointGroup59_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
