module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup72_0 : ([2304,2305,2306,2307,2308,2309,2310,2311] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup72_1 : ([2312,2313,2314,2315,2316,2317,2318,2319] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup72_2 : ([2320,2321,2322,2323,2324,2325,2326,2327] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup72_3 : ([2328,2329,2330,2331,2332,2333,2334,2335] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_72 : (checkChunk 72).all pointOK = true := by
  have h : checkChunk 72 = [2304,2305,2306,2307,2308,2309,2310,2311] ++ [2312,2313,2314,2315,2316,2317,2318,2319] ++ [2320,2321,2322,2323,2324,2325,2326,2327] ++ [2328,2329,2330,2331,2332,2333,2334,2335] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup72_0, pointGroup72_1, pointGroup72_2, pointGroup72_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
