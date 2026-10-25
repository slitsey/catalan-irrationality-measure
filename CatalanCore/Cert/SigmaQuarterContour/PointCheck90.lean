module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup90_0 : ([2880,2881,2882,2883,2884,2885,2886,2887] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup90_1 : ([2888,2889,2890,2891,2892,2893,2894,2895] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup90_2 : ([2896,2897,2898,2899,2900,2901,2902,2903] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup90_3 : ([2904,2905,2906,2907,2908,2909,2910,2911] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_90 : (checkChunk 90).all pointOK = true := by
  have h : checkChunk 90 = [2880,2881,2882,2883,2884,2885,2886,2887] ++ [2888,2889,2890,2891,2892,2893,2894,2895] ++ [2896,2897,2898,2899,2900,2901,2902,2903] ++ [2904,2905,2906,2907,2908,2909,2910,2911] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup90_0, pointGroup90_1, pointGroup90_2, pointGroup90_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
