module
public import CatalanCore.Cert.QuarterContour.LineFacts10
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly10
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts10.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros10
    LineFacts10.cells LineFacts10.cells_eq LineFacts10.facts LineFacts10.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly10
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly10.sound
