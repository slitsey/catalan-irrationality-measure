module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [111, 112, 113] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_111 : rowsSum (chunkStart 111) (chunkLen 111) = chunkVal 111 := by decide +kernel

theorem iChunk_112 : rowsSum (chunkStart 112) (chunkLen 112) = chunkVal 112 := by decide +kernel

theorem iChunk_113 : rowsSum (chunkStart 113) (chunkLen 113) = chunkVal 113 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
