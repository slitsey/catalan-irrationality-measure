module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup62_0 : ([1984,1985,1986,1987,1988,1989,1990,1991] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup62_1 : ([1992,1993,1994,1995,1996,1997,1998,1999] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup62_2 : ([2000,2001,2002,2003,2004,2005,2006,2007] : List ℕ).all pointOK = true := by decide +kernel
theorem pointGroup62_3 : ([2008,2009,2010,2011,2012,2013,2014,2015] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_62 : (checkChunk 62).all pointOK = true := by
  have h : checkChunk 62 = [1984,1985,1986,1987,1988,1989,1990,1991] ++ [1992,1993,1994,1995,1996,1997,1998,1999] ++ [2000,2001,2002,2003,2004,2005,2006,2007] ++ [2008,2009,2010,2011,2012,2013,2014,2015] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup62_0, pointGroup62_1, pointGroup62_2, pointGroup62_3, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
