module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup78_0 : ([2496,2497,2498,2499,2500,2501,2502,2503] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup78_1 : ([2504,2505,2506,2507,2508,2509,2510,2511] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup78_2 : ([2512,2513,2514,2515,2516,2517,2518,2519] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup78_3 : ([2520,2521,2522,2523,2524,2525,2526,2527] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_78 : (checkChunk 78).all pointOK = true := by
  have h : checkChunk 78 = [2496,2497,2498,2499,2500,2501,2502,2503] ++ [2504,2505,2506,2507,2508,2509,2510,2511] ++ [2512,2513,2514,2515,2516,2517,2518,2519] ++ [2520,2521,2522,2523,2524,2525,2526,2527] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup78_0, pointGroup78_1, pointGroup78_2, pointGroup78_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
