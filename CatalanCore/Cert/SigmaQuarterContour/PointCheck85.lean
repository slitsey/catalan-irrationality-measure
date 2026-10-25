module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup85_0 : ([2720,2721,2722,2723,2724,2725,2726,2727] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup85_1 : ([2728,2729,2730,2731,2732,2733,2734,2735] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup85_2 : ([2736,2737,2738,2739,2740,2741,2742,2743] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup85_3 : ([2744,2745,2746,2747,2748,2749,2750,2751] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_85 : (checkChunk 85).all pointOK = true := by
  have h : checkChunk 85 = [2720,2721,2722,2723,2724,2725,2726,2727] ++ [2728,2729,2730,2731,2732,2733,2734,2735] ++ [2736,2737,2738,2739,2740,2741,2742,2743] ++ [2744,2745,2746,2747,2748,2749,2750,2751] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup85_0, pointGroup85_1, pointGroup85_2, pointGroup85_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
