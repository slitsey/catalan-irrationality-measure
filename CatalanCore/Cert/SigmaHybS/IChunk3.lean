module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 51..67 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_3 : rowsSum (chunkStart 3) (chunkLen 3) = chunkVal 3 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
