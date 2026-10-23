module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 68..85 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_4 : rowsSum (chunkStart 4) (chunkLen 4) = chunkVal 4 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
