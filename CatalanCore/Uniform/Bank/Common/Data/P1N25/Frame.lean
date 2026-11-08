module

public import CatalanCore.Uniform.Bank.Common.Schema

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.P1N25
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) and polygon. -/

def member0 : FrameMember where
  shifts := ratsOf raw_ints% [
    1, 3, 1, 2, 1, 1]
  coeffs := ratsOf raw_ints% [
    5, 36, -1, 18, -1, 12]

def members : List FrameMember := [member0]

def geom : GeomData where
  alpha := q1 (raw_ints% [1, 12])
  dim := 3
  selectorPair := false
  rows := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 7, 6, 1, 2]
  cols := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 7, 6, 1, 2]

def polygon : PolygonData where
  vertices := vertsOf raw_ints% [
    -343, 4000, 0, 1, -455552257, 4000000000, 8499, 200000, -3083908433, 20000000000, 25497, 200000, -19021647793, 100000000000, 233723, 1000000, -876299873, 4000000000, 339961, 1000000, -7877161, 32000000, 424951, 1000000,
    -1253071921, 4000000000, 140619, 250000, -1800417441, 4000000000, 7, 10]
  tailSlope := q1 (raw_ints% [1, 1])
  tailLean := q1 (raw_ints% [-1, 1])

def price : ℚ × ℚ := (q1 (raw_ints% [10427335734250235819, 3235350494615500800]), q1 (raw_ints% [0, 1]))  -- (rational part, coefficient of log 2)

end CatalanCore.Uniform.Bank.Common.Data.P1N25
