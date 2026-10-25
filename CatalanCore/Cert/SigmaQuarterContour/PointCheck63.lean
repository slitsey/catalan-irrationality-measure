module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup63_0 : ([2016,2017,2018,2019,2020,2021,2022,2023] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup63_1 : ([2024,2025,2026,2027,2028,2029,2030,2031] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup63_2 : ([2032,2033,2034,2035,2036,2037,2038,2039] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup63_3 : ([2040,2041,2042,2043,2044,2045,2046,2047] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_63 : (checkChunk 63).all pointOK = true := by
  have h : checkChunk 63 = [2016,2017,2018,2019,2020,2021,2022,2023] ++ [2024,2025,2026,2027,2028,2029,2030,2031] ++ [2032,2033,2034,2035,2036,2037,2038,2039] ++ [2040,2041,2042,2043,2044,2045,2046,2047] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup63_0, pointGroup63_1, pointGroup63_2, pointGroup63_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
