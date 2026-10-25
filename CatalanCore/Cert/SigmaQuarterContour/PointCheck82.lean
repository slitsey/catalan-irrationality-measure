module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup82_0 : ([2624,2625,2626,2627,2628,2629,2630,2631] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup82_1 : ([2632,2633,2634,2635,2636,2637,2638,2639] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup82_2 : ([2640,2641,2642,2643,2644,2645,2646,2647] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup82_3 : ([2648,2649,2650,2651,2652,2653,2654,2655] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_82 : (checkChunk 82).all pointOK = true := by
  have h : checkChunk 82 = [2624,2625,2626,2627,2628,2629,2630,2631] ++ [2632,2633,2634,2635,2636,2637,2638,2639] ++ [2640,2641,2642,2643,2644,2645,2646,2647] ++ [2648,2649,2650,2651,2652,2653,2654,2655] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup82_0, pointGroup82_1, pointGroup82_2, pointGroup82_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
