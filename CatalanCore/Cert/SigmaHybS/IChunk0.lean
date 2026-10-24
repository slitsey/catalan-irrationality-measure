module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [0, 1, 2] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_0 : rowsSum (chunkStart 0) (chunkLen 0) = chunkVal 0 := by decide +kernel

theorem iChunk_1 : rowsSum (chunkStart 1) (chunkLen 1) = chunkVal 1 := by decide +kernel

theorem iChunk_2 : rowsSum (chunkStart 2) (chunkLen 2) = chunkVal 2 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
