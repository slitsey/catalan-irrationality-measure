module
public import CatalanCore.Cert.QuarterContour.LineFacts0
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly0
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts0.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros0
    LineFacts0.cells LineFacts0.cells_eq LineFacts0.facts LineFacts0.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly0
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly0.sound
