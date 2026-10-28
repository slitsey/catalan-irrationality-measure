import CatalanCore.Uniform.Bank.Common.Schema

namespace CatalanCore.Uniform.Bank.Common.Data.Fifths
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) and polygon. -/

def member0 : FrameMember where
  shifts := ratsOf raw_ints% [
    1, 5, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def member1 : FrameMember where
  shifts := ratsOf raw_ints% [
    2, 5, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def member2 : FrameMember where
  shifts := ratsOf raw_ints% [
    3, 5, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def member3 : FrameMember where
  shifts := ratsOf raw_ints% [
    4, 5, 1, 1]
  coeffs := ratsOf raw_ints% [
    -1, 1, 1, 1]

def members : List FrameMember := [member0, member1, member2, member3]

def geom : GeomData where
  alpha := q1 (raw_ints% [1, 9])
  dim := 2
  selectorPair := false
  rows := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 11, 9, 1, 2]
  cols := blocksOf raw_ints% [
    0, 1, 1, 1, 1, 1, 1, 1, 11, 9, 1, 2]

def polygon : PolygonData where
  vertices := vertsOf raw_ints% [
    -16741, 125000, 0, 1, -219513, 1250000, 2, 25, -1121309, 5000000, 11, 50]
  tailSlope := q1 (raw_ints% [12500, 3259])
  tailLean := q1 (raw_ints% [-3259, 12500])

def price : ℚ × ℚ := (q1 (raw_ints% [18612012566760416294509901, 5321679222691225544230080]), q1 (raw_ints% [2, 81]))  -- (rational part, coefficient of log 2)

end CatalanCore.Uniform.Bank.Common.Data.Fifths
