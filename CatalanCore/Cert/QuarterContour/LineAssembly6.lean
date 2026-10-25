module
public import CatalanCore.Cert.QuarterContour.LineFacts6
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly6
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts6.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros6
    LineFacts6.cells LineFacts6.cells_eq LineFacts6.facts LineFacts6.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly6
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly6.sound
