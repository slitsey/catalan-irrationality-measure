module
public import CatalanCore.Cert.QuarterContour.LineFacts8
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly8
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts8.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros8
    LineFacts8.cells LineFacts8.cells_eq LineFacts8.facts LineFacts8.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly8
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly8.sound
