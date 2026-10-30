module
public import CatalanCore.Cert.QuarterContour.LineFacts17
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly17
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts17.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros17
    LineFacts17.cells LineFacts17.cells_eq LineFacts17.facts LineFacts17.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly17
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly17.sound
