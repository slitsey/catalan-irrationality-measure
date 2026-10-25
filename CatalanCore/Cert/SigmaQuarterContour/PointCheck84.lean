module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup84_0 : ([2688,2689,2690,2691,2692,2693,2694,2695] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup84_1 : ([2696,2697,2698,2699,2700,2701,2702,2703] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup84_2 : ([2704,2705,2706,2707,2708,2709,2710,2711] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup84_3 : ([2712,2713,2714,2715,2716,2717,2718,2719] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_84 : (checkChunk 84).all pointOK = true := by
  have h : checkChunk 84 = [2688,2689,2690,2691,2692,2693,2694,2695] ++ [2696,2697,2698,2699,2700,2701,2702,2703] ++ [2704,2705,2706,2707,2708,2709,2710,2711] ++ [2712,2713,2714,2715,2716,2717,2718,2719] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup84_0, pointGroup84_1, pointGroup84_2, pointGroup84_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
