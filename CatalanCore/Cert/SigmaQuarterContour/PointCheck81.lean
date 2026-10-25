module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup81_0 : ([2592,2593,2594,2595,2596,2597,2598,2599] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup81_1 : ([2600,2601,2602,2603,2604,2605,2606,2607] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup81_2 : ([2608,2609,2610,2611,2612,2613,2614,2615] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup81_3 : ([2616,2617,2618,2619,2620,2621,2622,2623] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_81 : (checkChunk 81).all pointOK = true := by
  have h : checkChunk 81 = [2592,2593,2594,2595,2596,2597,2598,2599] ++ [2600,2601,2602,2603,2604,2605,2606,2607] ++ [2608,2609,2610,2611,2612,2613,2614,2615] ++ [2616,2617,2618,2619,2620,2621,2622,2623] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup81_0, pointGroup81_1, pointGroup81_2, pointGroup81_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
