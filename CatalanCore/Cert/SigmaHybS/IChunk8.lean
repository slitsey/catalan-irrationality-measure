module

public import CatalanCore.Cert.SigmaHybS.IBoundDef

@[expose] public section

/-! Generated (genI.py): rows 140..157 of the triangle (one kernel cell). -/
namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000
set_option Elab.async false

theorem iChunk_8 : rowsSum (chunkStart 8) (chunkLen 8) = chunkVal 8 := by decide +kernel

end CatalanCore.Cert.SigmaHybS
