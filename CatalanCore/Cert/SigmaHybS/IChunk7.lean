module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [21, 22, 23] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_21 : rowsSum (chunkStart 21) (chunkLen 21) = chunkVal 21 := by decide +kernel

theorem iChunk_22 : rowsSum (chunkStart 22) (chunkLen 22) = chunkVal 22 := by decide +kernel

theorem iChunk_23 : rowsSum (chunkStart 23) (chunkLen 23) = chunkVal 23 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
