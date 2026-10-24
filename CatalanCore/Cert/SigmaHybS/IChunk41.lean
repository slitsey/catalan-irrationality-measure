module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [123, 124, 125] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_123 : rowsSum (chunkStart 123) (chunkLen 123) = chunkVal 123 := by decide +kernel

theorem iChunk_124 : rowsSum (chunkStart 124) (chunkLen 124) = chunkVal 124 := by decide +kernel

theorem iChunk_125 : rowsSum (chunkStart 125) (chunkLen 125) = chunkVal 125 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
