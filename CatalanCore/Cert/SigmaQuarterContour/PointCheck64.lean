module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup64_0 : ([2048,2049,2050,2051,2052,2053,2054,2055] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup64_1 : ([2056,2057,2058,2059,2060,2061,2062,2063] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup64_2 : ([2064,2065,2066,2067,2068,2069,2070,2071] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup64_3 : ([2072,2073,2074,2075,2076,2077,2078,2079] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_64 : (checkChunk 64).all pointOK = true := by
  have h : checkChunk 64 = [2048,2049,2050,2051,2052,2053,2054,2055] ++ [2056,2057,2058,2059,2060,2061,2062,2063] ++ [2064,2065,2066,2067,2068,2069,2070,2071] ++ [2072,2073,2074,2075,2076,2077,2078,2079] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup64_0, pointGroup64_1, pointGroup64_2, pointGroup64_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
