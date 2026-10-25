module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup89_0 : ([2848,2849,2850,2851,2852,2853,2854,2855] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup89_1 : ([2856,2857,2858,2859,2860,2861,2862,2863] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup89_2 : ([2864,2865,2866,2867,2868,2869,2870,2871] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup89_3 : ([2872,2873,2874,2875,2876,2877,2878,2879] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_89 : (checkChunk 89).all pointOK = true := by
  have h : checkChunk 89 = [2848,2849,2850,2851,2852,2853,2854,2855] ++ [2856,2857,2858,2859,2860,2861,2862,2863] ++ [2864,2865,2866,2867,2868,2869,2870,2871] ++ [2872,2873,2874,2875,2876,2877,2878,2879] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup89_0, pointGroup89_1, pointGroup89_2, pointGroup89_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
