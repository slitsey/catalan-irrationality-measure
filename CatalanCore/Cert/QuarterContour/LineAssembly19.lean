module
public import CatalanCore.Cert.QuarterContour.LineFacts19
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly19
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts19.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros19
    LineFacts19.cells LineFacts19.cells_eq LineFacts19.facts LineFacts19.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly19
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly19.sound
