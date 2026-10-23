module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [9, 10, 11] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_9 : rowsSum (chunkStart 9) (chunkLen 9) = chunkVal 9 := by decide +kernel

theorem iChunk_10 : rowsSum (chunkStart 10) (chunkLen 10) = chunkVal 10 := by decide +kernel

theorem iChunk_11 : rowsSum (chunkStart 11) (chunkLen 11) = chunkVal 11 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
