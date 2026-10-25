module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup87_0 : ([2784,2785,2786,2787,2788,2789,2790,2791] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup87_1 : ([2792,2793,2794,2795,2796,2797,2798,2799] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup87_2 : ([2800,2801,2802,2803,2804,2805,2806,2807] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup87_3 : ([2808,2809,2810,2811,2812,2813,2814,2815] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_87 : (checkChunk 87).all pointOK = true := by
  have h : checkChunk 87 = [2784,2785,2786,2787,2788,2789,2790,2791] ++ [2792,2793,2794,2795,2796,2797,2798,2799] ++ [2800,2801,2802,2803,2804,2805,2806,2807] ++ [2808,2809,2810,2811,2812,2813,2814,2815] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup87_0, pointGroup87_1, pointGroup87_2, pointGroup87_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
