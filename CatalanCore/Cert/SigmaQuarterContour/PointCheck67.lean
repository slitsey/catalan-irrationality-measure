module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup67_0 : ([2144,2145,2146,2147,2148,2149,2150,2151] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup67_1 : ([2152,2153,2154,2155,2156,2157,2158,2159] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup67_2 : ([2160,2161,2162,2163,2164,2165,2166,2167] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup67_3 : ([2168,2169,2170,2171,2172,2173,2174,2175] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_67 : (checkChunk 67).all pointOK = true := by
  have h : checkChunk 67 = [2144,2145,2146,2147,2148,2149,2150,2151] ++ [2152,2153,2154,2155,2156,2157,2158,2159] ++ [2160,2161,2162,2163,2164,2165,2166,2167] ++ [2168,2169,2170,2171,2172,2173,2174,2175] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup67_0, pointGroup67_1, pointGroup67_2, pointGroup67_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
