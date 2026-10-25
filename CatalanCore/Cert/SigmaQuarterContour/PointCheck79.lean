module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup79_0 : ([2528,2529,2530,2531,2532,2533,2534,2535] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup79_1 : ([2536,2537,2538,2539,2540,2541,2542,2543] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup79_2 : ([2544,2545,2546,2547,2548,2549,2550,2551] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup79_3 : ([2552,2553,2554,2555,2556,2557,2558,2559] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_79 : (checkChunk 79).all pointOK = true := by
  have h : checkChunk 79 = [2528,2529,2530,2531,2532,2533,2534,2535] ++ [2536,2537,2538,2539,2540,2541,2542,2543] ++ [2544,2545,2546,2547,2548,2549,2550,2551] ++ [2552,2553,2554,2555,2556,2557,2558,2559] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup79_0, pointGroup79_1, pointGroup79_2, pointGroup79_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
