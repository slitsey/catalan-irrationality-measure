module
public import CatalanCore.Cert.QuarterContour.LineFacts12
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly12
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts12.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros12
    LineFacts12.cells LineFacts12.cells_eq LineFacts12.facts LineFacts12.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly12
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly12.sound
