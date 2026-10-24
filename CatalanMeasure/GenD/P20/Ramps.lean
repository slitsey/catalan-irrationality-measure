module

public import CatalanMeasure.GenD.PrimeGrowth

@[expose] public section

/-!
# Ramp list of P20 (instance data)

The three banked P20 content cells (`GenD/Parity/P20Areas`), split into affine pieces:
U6g on `(4, 9/2]`, secondary tent on `(52/9, 44/7]` (two pieces), tent+U3 on `(22/3, 9]` (two
pieces).  Total area `1/16 + 16/63 + 5/3 = 1999/1008`.
-/

namespace CatalanMeasure.GenD
namespace P20

open PL PrimeGrowth

noncomputable section

def cellProfs : List (ℝ × ℝ × Prof) :=
  [((4 : ℝ), (9/2 : ℝ), ⟨(-2 : ℝ), (1/2 : ℝ), []⟩),
   ((52/9 : ℝ), (6 : ℝ), ⟨(-26 : ℝ), (9/2 : ℝ), []⟩),
   ((6 : ℝ), (44/7 : ℝ), ⟨(22 : ℝ), (-7/2 : ℝ), []⟩),
   ((22/3 : ℝ), (8 : ℝ), ⟨(-22 : ℝ), (3 : ℝ), []⟩),
   ((8 : ℝ), (9 : ℝ), ⟨(18 : ℝ), (-2 : ℝ), []⟩)]

def segs : List Seg := profSegs cellProfs

theorem segs_totalArea : totalArea segs = (1999/1008 : ℝ) := by
  rw [segs, totalArea_profSegs _ (by norm_num [cellProfs])]
  norm_num [cellProfs, PL.Prof.area, PL.hingeInt_nil]

end
end P20
end CatalanMeasure.GenD
