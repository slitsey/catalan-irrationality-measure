module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [12, 13, 14] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_12 : rowsSum (chunkStart 12) (chunkLen 12) = chunkVal 12 := by decide +kernel

theorem iChunk_13 : rowsSum (chunkStart 13) (chunkLen 13) = chunkVal 13 := by decide +kernel

theorem iChunk_14 : rowsSum (chunkStart 14) (chunkLen 14) = chunkVal 14 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
