module
public import CatalanCore.Cert.QuarterContour.LineFacts5
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly5
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts5.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros5
    LineFacts5.cells LineFacts5.cells_eq LineFacts5.facts LineFacts5.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly5
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly5.sound
