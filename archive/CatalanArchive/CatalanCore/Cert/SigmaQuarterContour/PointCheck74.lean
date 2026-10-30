module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup74_0 : ([2368,2369,2370,2371,2372,2373,2374,2375] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup74_1 : ([2376,2377,2378,2379,2380,2381,2382,2383] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup74_2 : ([2384,2385,2386,2387,2388,2389,2390,2391] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup74_3 : ([2392,2393,2394,2395,2396,2397,2398,2399] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_74 : (checkChunk 74).all pointOK = true := by
  have h : checkChunk 74 = [2368,2369,2370,2371,2372,2373,2374,2375] ++ [2376,2377,2378,2379,2380,2381,2382,2383] ++ [2384,2385,2386,2387,2388,2389,2390,2391] ++ [2392,2393,2394,2395,2396,2397,2398,2399] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup74_0, pointGroup74_1, pointGroup74_2, pointGroup74_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
