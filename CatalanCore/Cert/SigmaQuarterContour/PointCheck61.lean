module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup61_0 : ([1952,1953,1954,1955,1956,1957,1958,1959] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup61_1 : ([1960,1961,1962,1963,1964,1965,1966,1967] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup61_2 : ([1968,1969,1970,1971,1972,1973,1974,1975] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup61_3 : ([1976,1977,1978,1979,1980,1981,1982,1983] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_61 : (checkChunk 61).all pointOK = true := by
  have h : checkChunk 61 = [1952,1953,1954,1955,1956,1957,1958,1959] ++ [1960,1961,1962,1963,1964,1965,1966,1967] ++ [1968,1969,1970,1971,1972,1973,1974,1975] ++ [1976,1977,1978,1979,1980,1981,1982,1983] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup61_0, pointGroup61_1, pointGroup61_2, pointGroup61_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
