module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup66_0 : ([2112,2113,2114,2115,2116,2117,2118,2119] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup66_1 : ([2120,2121,2122,2123,2124,2125,2126,2127] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup66_2 : ([2128,2129,2130,2131,2132,2133,2134,2135] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup66_3 : ([2136,2137,2138,2139,2140,2141,2142,2143] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_66 : (checkChunk 66).all pointOK = true := by
  have h : checkChunk 66 = [2112,2113,2114,2115,2116,2117,2118,2119] ++ [2120,2121,2122,2123,2124,2125,2126,2127] ++ [2128,2129,2130,2131,2132,2133,2134,2135] ++ [2136,2137,2138,2139,2140,2141,2142,2143] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup66_0, pointGroup66_1, pointGroup66_2, pointGroup66_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
