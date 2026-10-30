module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup73_0 : ([2336,2337,2338,2339,2340,2341,2342,2343] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup73_1 : ([2344,2345,2346,2347,2348,2349,2350,2351] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup73_2 : ([2352,2353,2354,2355,2356,2357,2358,2359] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup73_3 : ([2360,2361,2362,2363,2364,2365,2366,2367] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_73 : (checkChunk 73).all pointOK = true := by
  have h : checkChunk 73 = [2336,2337,2338,2339,2340,2341,2342,2343] ++ [2344,2345,2346,2347,2348,2349,2350,2351] ++ [2352,2353,2354,2355,2356,2357,2358,2359] ++ [2360,2361,2362,2363,2364,2365,2366,2367] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup73_0, pointGroup73_1, pointGroup73_2, pointGroup73_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
