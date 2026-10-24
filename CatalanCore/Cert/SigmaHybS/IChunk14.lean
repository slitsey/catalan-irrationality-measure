module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows of triangle chunks [42, 43, 44] (one kernel cell each). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_42 : rowsSum (chunkStart 42) (chunkLen 42) = chunkVal 42 := by decide +kernel

theorem iChunk_43 : rowsSum (chunkStart 43) (chunkLen 43) = chunkVal 43 := by decide +kernel

theorem iChunk_44 : rowsSum (chunkStart 44) (chunkLen 44) = chunkVal 44 := by decide +kernel


end CatalanCore.Cert.SigmaHybS
