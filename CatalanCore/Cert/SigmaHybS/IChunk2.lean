module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [6, 7, 8] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_6 : rowsSum (chunkStart 6) (chunkLen 6) = chunkVal 6 := by decide +kernel

theorem iChunk_7 : rowsSum (chunkStart 7) (chunkLen 7) = chunkVal 7 := by decide +kernel

theorem iChunk_8 : rowsSum (chunkStart 8) (chunkLen 8) = chunkVal 8 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
