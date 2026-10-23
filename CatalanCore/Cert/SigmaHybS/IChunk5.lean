module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 86..103 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_5 : rowsSum (chunkStart 5) (chunkLen 5) = chunkVal 5 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
