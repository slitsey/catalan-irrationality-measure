module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup77_0 : ([2464,2465,2466,2467,2468,2469,2470,2471] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup77_1 : ([2472,2473,2474,2475,2476,2477,2478,2479] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup77_2 : ([2480,2481,2482,2483,2484,2485,2486,2487] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup77_3 : ([2488,2489,2490,2491,2492,2493,2494,2495] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_77 : (checkChunk 77).all pointOK = true := by
  have h : checkChunk 77 = [2464,2465,2466,2467,2468,2469,2470,2471] ++ [2472,2473,2474,2475,2476,2477,2478,2479] ++ [2480,2481,2482,2483,2484,2485,2486,2487] ++ [2488,2489,2490,2491,2492,2493,2494,2495] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup77_0, pointGroup77_1, pointGroup77_2, pointGroup77_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
