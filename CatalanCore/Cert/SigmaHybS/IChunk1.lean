module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 17..33 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_1 : rowsSum (chunkStart 1) (chunkLen 1) = chunkVal 1 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
