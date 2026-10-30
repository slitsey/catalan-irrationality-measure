module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup69_0 : ([2208,2209,2210,2211,2212,2213,2214,2215] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup69_1 : ([2216,2217,2218,2219,2220,2221,2222,2223] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup69_2 : ([2224,2225,2226,2227,2228,2229,2230,2231] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup69_3 : ([2232,2233,2234,2235,2236,2237,2238,2239] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_69 : (checkChunk 69).all pointOK = true := by
  have h : checkChunk 69 = [2208,2209,2210,2211,2212,2213,2214,2215] ++ [2216,2217,2218,2219,2220,2221,2222,2223] ++ [2224,2225,2226,2227,2228,2229,2230,2231] ++ [2232,2233,2234,2235,2236,2237,2238,2239] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup69_0, pointGroup69_1, pointGroup69_2, pointGroup69_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
