module

public import CatalanCore.Uniform.Bank.Common.Schema

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Thirds
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) and polygon. -/

def member0 : FrameMember where
  shifts := ratsOf raw_ints% [
    1, 3, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def member1 : FrameMember where
  shifts := ratsOf raw_ints% [
    2, 3, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def members : List FrameMember := [member0, member1]

def geom : GeomData where
  alpha := q1 (raw_ints% [3, 20])
  dim := 2
  selectorPair := false
  rows := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 13, 10, 1, 2]
  cols := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 13, 10, 1, 2]

def polygon : PolygonData where
  vertices := vertsOf raw_ints% [
    -33, 250, 0, 1, -332250187, 2500000000, 193, 25000, -15970759447, 100000000000, 59449, 1000000, -4979766249, 25000000000, 9497, 62500, -6391350939, 25000000000, 43189, 125000]
  tailSlope := q1 (raw_ints% [100000, 31399])
  tailLean := q1 (raw_ints% [-31399, 100000])

def price : ℚ × ℚ := (q1 (raw_ints% [7808344448571, 2379657280000]), q1 (raw_ints% [9, 200]))  -- (rational part, coefficient of log 2)

end CatalanCore.Uniform.Bank.Common.Data.Thirds
