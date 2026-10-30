module

public import CatalanCore.Uniform.Bank.Common.Schema

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Chi3
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) and polygon. -/

def member0 : FrameMember where
  shifts := ratsOf raw_ints% [
    1, 3, 1, 2, 1, 1]
  coeffs := ratsOf raw_ints% [
    1, 18, -1, 12, 1, 36]

def members : List FrameMember := [member0]

def geom : GeomData where
  alpha := q1 (raw_ints% [1, 4])
  dim := 3
  selectorPair := false
  rows := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2]
  cols := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2]

def polygon : PolygonData where
  vertices := vertsOf raw_ints% [
    -49, 500, 0, 1, -490443917, 4000000000, 8499, 200000, -3309377731, 20000000000, 25497, 200000, -20605923921, 100000000000, 233723, 1000000, -23555728229, 100000000000, 339961, 1000000, -25788245549, 100000000000, 424951, 1000000,
    -491041141, 1562500000, 140619, 250000, -2222019581, 5000000000, 7, 10]
  tailSlope := q1 (raw_ints% [200, 191])
  tailLean := q1 (raw_ints% [-191, 200])

def price : ℚ × ℚ := (q1 (raw_ints% [4733759984905769, 1155228423148800]), q1 (raw_ints% [0, 1]))  -- (rational part, coefficient of log 2)

end CatalanCore.Uniform.Bank.Common.Data.Chi3
