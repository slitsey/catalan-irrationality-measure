module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup68_0 : ([2176,2177,2178,2179,2180,2181,2182,2183] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup68_1 : ([2184,2185,2186,2187,2188,2189,2190,2191] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup68_2 : ([2192,2193,2194,2195,2196,2197,2198,2199] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup68_3 : ([2200,2201,2202,2203,2204,2205,2206,2207] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_68 : (checkChunk 68).all pointOK = true := by
  have h : checkChunk 68 = [2176,2177,2178,2179,2180,2181,2182,2183] ++ [2184,2185,2186,2187,2188,2189,2190,2191] ++ [2192,2193,2194,2195,2196,2197,2198,2199] ++ [2200,2201,2202,2203,2204,2205,2206,2207] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup68_0, pointGroup68_1, pointGroup68_2, pointGroup68_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
