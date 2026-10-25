module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup60_0 : ([1920,1921,1922,1923,1924,1925,1926,1927] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup60_1 : ([1928,1929,1930,1931,1932,1933,1934,1935] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup60_2 : ([1936,1937,1938,1939,1940,1941,1942,1943] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup60_3 : ([1944,1945,1946,1947,1948,1949,1950,1951] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_60 : (checkChunk 60).all pointOK = true := by
  have h : checkChunk 60 = [1920,1921,1922,1923,1924,1925,1926,1927] ++ [1928,1929,1930,1931,1932,1933,1934,1935] ++ [1936,1937,1938,1939,1940,1941,1942,1943] ++ [1944,1945,1946,1947,1948,1949,1950,1951] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup60_0, pointGroup60_1, pointGroup60_2, pointGroup60_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
