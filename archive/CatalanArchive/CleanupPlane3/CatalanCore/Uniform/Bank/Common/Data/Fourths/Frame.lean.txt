module

public import CatalanCore.Uniform.Bank.Common.Schema

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Fourths
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) and polygon. -/

def member0 : FrameMember where
  shifts := ratsOf raw_ints% [
    1, 4, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def member1 : FrameMember where
  shifts := ratsOf raw_ints% [
    3, 4, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def members : List FrameMember := [member0, member1]

def geom : GeomData where
  alpha := q1 (raw_ints% [1, 10])
  dim := 2
  selectorPair := true
  rows := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2]
  cols := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2]

def polygon : PolygonData where
  vertices := vertsOf raw_ints% [
    -4161, 31250, 0, 1, -43379, 250000, 2, 25, -281617, 1250000, 11, 50]
  tailSlope := q1 (raw_ints% [100000, 25253])
  tailLean := q1 (raw_ints% [-25253, 100000])

def price : ℚ × ℚ := (q1 (raw_ints% [25845089911312474748789, 7378677391061896920000]), q1 (raw_ints% [1, 50]))  -- (rational part, coefficient of log 2)

end CatalanCore.Uniform.Bank.Common.Data.Fourths
