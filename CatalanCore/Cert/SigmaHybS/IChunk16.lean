module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 294..314 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_16 : rowsSum (chunkStart 16) (chunkLen 16) = chunkVal 16 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
