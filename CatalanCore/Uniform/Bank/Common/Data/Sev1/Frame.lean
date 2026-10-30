module

public import CatalanCore.Uniform.Bank.Common.Schema

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Sev1
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) and polygon. -/

def member0 : FrameMember where
  shifts := ratsOf raw_ints% [
    1, 7, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def members : List FrameMember := [member0]

def geom : GeomData where
  alpha := q1 (raw_ints% [1, 12])
  dim := 2
  selectorPair := false
  rows := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 7, 6, 1, 2]
  cols := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 7, 6, 1, 2]

def polygon : PolygonData where
  vertices := vertsOf raw_ints% [
    -273, 2000, 0, 1, -8809027, 50000000, 787, 10000, -11253987, 50000000, 1041, 5000]
  tailSlope := q1 (raw_ints% [5000, 1353])
  tailLean := q1 (raw_ints% [-1353, 5000])


end CatalanCore.Uniform.Bank.Common.Data.Sev1
