import CatalanCore.Uniform.Bank.Common.Data.Chi3.Data
import CatalanCore.Uniform.Bank.Common.Data.Chi3.Frame
import CatalanCore.Uniform.Bank.Common.Data.Chi3.CellInfo
import CatalanCore.Uniform.Decay.PolyWire2.Kinds
open CatalanCore.Uniform.Bank.Common.Data.Chi3
def main : IO Unit := do
  IO.println s!"segs {segs.length} ray {rayInfo.length} line {lineInfo.length} seg {segInfo.length}"
  IO.println s!"poly {polygon.vertices.length}"
