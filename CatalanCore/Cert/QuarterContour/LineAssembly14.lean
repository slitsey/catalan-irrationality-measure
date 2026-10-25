module
public import CatalanCore.Cert.QuarterContour.LineFacts14
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly14
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts14.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros14
    LineFacts14.cells LineFacts14.cells_eq LineFacts14.facts LineFacts14.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly14
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly14.sound
