module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [15, 16, 17] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_15 : rowsSum (chunkStart 15) (chunkLen 15) = chunkVal 15 := by decide +kernel

theorem iChunk_16 : rowsSum (chunkStart 16) (chunkLen 16) = chunkVal 16 := by decide +kernel

theorem iChunk_17 : rowsSum (chunkStart 17) (chunkLen 17) = chunkVal 17 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
