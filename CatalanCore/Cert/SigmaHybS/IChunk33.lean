module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [99, 100, 101] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_99 : rowsSum (chunkStart 99) (chunkLen 99) = chunkVal 99 := by decide +kernel

theorem iChunk_100 : rowsSum (chunkStart 100) (chunkLen 100) = chunkVal 100 := by decide +kernel

theorem iChunk_101 : rowsSum (chunkStart 101) (chunkLen 101) = chunkVal 101 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
