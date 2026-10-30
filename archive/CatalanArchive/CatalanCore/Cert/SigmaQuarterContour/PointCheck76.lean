module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup76_0 : ([2432,2433,2434,2435,2436,2437,2438,2439] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup76_1 : ([2440,2441,2442,2443,2444,2445,2446,2447] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup76_2 : ([2448,2449,2450,2451,2452,2453,2454,2455] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup76_3 : ([2456,2457,2458,2459,2460,2461,2462,2463] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_76 : (checkChunk 76).all pointOK = true := by
  have h : checkChunk 76 = [2432,2433,2434,2435,2436,2437,2438,2439] ++ [2440,2441,2442,2443,2444,2445,2446,2447] ++ [2448,2449,2450,2451,2452,2453,2454,2455] ++ [2456,2457,2458,2459,2460,2461,2462,2463] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup76_0, pointGroup76_1, pointGroup76_2, pointGroup76_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
