module
public import CatalanCore.Cert.QuarterContour.LineFacts1
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly1
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts1.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros1
    LineFacts1.cells LineFacts1.cells_eq LineFacts1.facts LineFacts1.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly1
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly1.sound
