module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup70_0 : ([2240,2241,2242,2243,2244,2245,2246,2247] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup70_1 : ([2248,2249,2250,2251,2252,2253,2254,2255] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup70_2 : ([2256,2257,2258,2259,2260,2261,2262,2263] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup70_3 : ([2264,2265,2266,2267,2268,2269,2270,2271] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_70 : (checkChunk 70).all pointOK = true := by
  have h : checkChunk 70 = [2240,2241,2242,2243,2244,2245,2246,2247] ++ [2248,2249,2250,2251,2252,2253,2254,2255] ++ [2256,2257,2258,2259,2260,2261,2262,2263] ++ [2264,2265,2266,2267,2268,2269,2270,2271] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup70_0, pointGroup70_1, pointGroup70_2, pointGroup70_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
