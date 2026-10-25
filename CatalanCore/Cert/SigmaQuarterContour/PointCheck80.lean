module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup80_0 : ([2560,2561,2562,2563,2564,2565,2566,2567] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup80_1 : ([2568,2569,2570,2571,2572,2573,2574,2575] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup80_2 : ([2576,2577,2578,2579,2580,2581,2582,2583] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup80_3 : ([2584,2585,2586,2587,2588,2589,2590,2591] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_80 : (checkChunk 80).all pointOK = true := by
  have h : checkChunk 80 = [2560,2561,2562,2563,2564,2565,2566,2567] ++ [2568,2569,2570,2571,2572,2573,2574,2575] ++ [2576,2577,2578,2579,2580,2581,2582,2583] ++ [2584,2585,2586,2587,2588,2589,2590,2591] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup80_0, pointGroup80_1, pointGroup80_2, pointGroup80_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
