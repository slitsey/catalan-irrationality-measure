module
public import CatalanCore.Cert.QuarterContour.LineFacts7
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly7
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts7.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros7
    LineFacts7.cells LineFacts7.cells_eq LineFacts7.facts LineFacts7.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly7
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly7.sound
