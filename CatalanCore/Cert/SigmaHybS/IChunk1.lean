module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [3, 4, 5] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_3 : rowsSum (chunkStart 3) (chunkLen 3) = chunkVal 3 := by decide +kernel

theorem iChunk_4 : rowsSum (chunkStart 4) (chunkLen 4) = chunkVal 4 := by decide +kernel

theorem iChunk_5 : rowsSum (chunkStart 5) (chunkLen 5) = chunkVal 5 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
