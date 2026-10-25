module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup88_0 : ([2816,2817,2818,2819,2820,2821,2822,2823] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup88_1 : ([2824,2825,2826,2827,2828,2829,2830,2831] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup88_2 : ([2832,2833,2834,2835,2836,2837,2838,2839] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup88_3 : ([2840,2841,2842,2843,2844,2845,2846,2847] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_88 : (checkChunk 88).all pointOK = true := by
  have h : checkChunk 88 = [2816,2817,2818,2819,2820,2821,2822,2823] ++ [2824,2825,2826,2827,2828,2829,2830,2831] ++ [2832,2833,2834,2835,2836,2837,2838,2839] ++ [2840,2841,2842,2843,2844,2845,2846,2847] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup88_0, pointGroup88_1, pointGroup88_2, pointGroup88_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
