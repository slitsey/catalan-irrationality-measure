module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup65_0 : ([2080,2081,2082,2083,2084,2085,2086,2087] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup65_1 : ([2088,2089,2090,2091,2092,2093,2094,2095] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup65_2 : ([2096,2097,2098,2099,2100,2101,2102,2103] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup65_3 : ([2104,2105,2106,2107,2108,2109,2110,2111] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_65 : (checkChunk 65).all pointOK = true := by
  have h : checkChunk 65 = [2080,2081,2082,2083,2084,2085,2086,2087] ++ [2088,2089,2090,2091,2092,2093,2094,2095] ++ [2096,2097,2098,2099,2100,2101,2102,2103] ++ [2104,2105,2106,2107,2108,2109,2110,2111] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup65_0, pointGroup65_1, pointGroup65_2, pointGroup65_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
