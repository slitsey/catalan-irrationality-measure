module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup71_0 : ([2272,2273,2274,2275,2276,2277,2278,2279] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup71_1 : ([2280,2281,2282,2283,2284,2285,2286,2287] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup71_2 : ([2288,2289,2290,2291,2292,2293,2294,2295] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup71_3 : ([2296,2297,2298,2299,2300,2301,2302,2303] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_71 : (checkChunk 71).all pointOK = true := by
  have h : checkChunk 71 = [2272,2273,2274,2275,2276,2277,2278,2279] ++ [2280,2281,2282,2283,2284,2285,2286,2287] ++ [2288,2289,2290,2291,2292,2293,2294,2295] ++ [2296,2297,2298,2299,2300,2301,2302,2303] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup71_0, pointGroup71_1, pointGroup71_2, pointGroup71_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
