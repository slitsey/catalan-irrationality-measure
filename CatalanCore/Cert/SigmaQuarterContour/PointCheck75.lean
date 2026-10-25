module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup75_0 : ([2400,2401,2402,2403,2404,2405,2406,2407] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup75_1 : ([2408,2409,2410,2411,2412,2413,2414,2415] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup75_2 : ([2416,2417,2418,2419,2420,2421,2422,2423] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup75_3 : ([2424,2425,2426,2427,2428,2429,2430,2431] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_75 : (checkChunk 75).all pointOK = true := by
  have h : checkChunk 75 = [2400,2401,2402,2403,2404,2405,2406,2407] ++ [2408,2409,2410,2411,2412,2413,2414,2415] ++ [2416,2417,2418,2419,2420,2421,2422,2423] ++ [2424,2425,2426,2427,2428,2429,2430,2431] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup75_0, pointGroup75_1, pointGroup75_2, pointGroup75_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
