module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [30, 31, 32] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_30 : rowsSum (chunkStart 30) (chunkLen 30) = chunkVal 30 := by decide +kernel

theorem iChunk_31 : rowsSum (chunkStart 31) (chunkLen 31) = chunkVal 31 := by decide +kernel

theorem iChunk_32 : rowsSum (chunkStart 32) (chunkLen 32) = chunkVal 32 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
