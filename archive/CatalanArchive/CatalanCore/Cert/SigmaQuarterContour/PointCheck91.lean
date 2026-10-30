module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup91_0 : ([2912,2913,2914,2915,2916,2917,2918,2919] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup91_1 : ([2920,2921,2922,2923,2924,2925,2926,2927] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup91_2 : ([2928,2929,2930,2931,2932,2933,2934,2935] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup91_3 : ([2936,2937,2938,2939,2940,2941,2942,2943] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_91 : (checkChunk 91).all pointOK = true := by
  have h : checkChunk 91 = [2912,2913,2914,2915,2916,2917,2918,2919] ++ [2920,2921,2922,2923,2924,2925,2926,2927] ++ [2928,2929,2930,2931,2932,2933,2934,2935] ++ [2936,2937,2938,2939,2940,2941,2942,2943] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup91_0, pointGroup91_1, pointGroup91_2, pointGroup91_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
