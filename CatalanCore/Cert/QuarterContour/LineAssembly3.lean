module
public import CatalanCore.Cert.QuarterContour.LineFacts3
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly3
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts3.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros3
    LineFacts3.cells LineFacts3.cells_eq LineFacts3.facts LineFacts3.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly3
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly3.sound
