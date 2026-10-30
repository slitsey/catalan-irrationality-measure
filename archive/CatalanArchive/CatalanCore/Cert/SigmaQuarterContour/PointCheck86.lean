module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup86_0 : ([2752,2753,2754,2755,2756,2757,2758,2759] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup86_1 : ([2760,2761,2762,2763,2764,2765,2766,2767] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup86_2 : ([2768,2769,2770,2771,2772,2773,2774,2775] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup86_3 : ([2776,2777,2778,2779,2780,2781,2782,2783] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_86 : (checkChunk 86).all pointOK = true := by
  have h : checkChunk 86 = [2752,2753,2754,2755,2756,2757,2758,2759] ++ [2760,2761,2762,2763,2764,2765,2766,2767] ++ [2768,2769,2770,2771,2772,2773,2774,2775] ++ [2776,2777,2778,2779,2780,2781,2782,2783] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup86_0, pointGroup86_1, pointGroup86_2, pointGroup86_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
