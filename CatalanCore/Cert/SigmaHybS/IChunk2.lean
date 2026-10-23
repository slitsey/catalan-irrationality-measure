module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 34..50 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_2 : rowsSum (chunkStart 2) (chunkLen 2) = chunkVal 2 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
