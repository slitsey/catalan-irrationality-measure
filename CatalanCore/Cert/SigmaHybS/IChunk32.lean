module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 674..702 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_32 : rowsSum (chunkStart 32) (chunkLen 32) = chunkVal 32 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
