module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup83_0 : ([2656,2657,2658,2659,2660,2661,2662,2663] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup83_1 : ([2664,2665,2666,2667,2668,2669,2670,2671] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup83_2 : ([2672,2673,2674,2675,2676,2677,2678,2679] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup83_3 : ([2680,2681,2682,2683,2684,2685,2686,2687] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_83 : (checkChunk 83).all pointOK = true := by
  have h : checkChunk 83 = [2656,2657,2658,2659,2660,2661,2662,2663] ++ [2664,2665,2666,2667,2668,2669,2670,2671] ++ [2672,2673,2674,2675,2676,2677,2678,2679] ++ [2680,2681,2682,2683,2684,2685,2686,2687] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup83_0, pointGroup83_1, pointGroup83_2, pointGroup83_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
