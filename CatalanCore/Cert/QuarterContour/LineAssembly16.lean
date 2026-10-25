module
public import CatalanCore.Cert.QuarterContour.LineFacts16
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly16
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts16.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros16
    LineFacts16.cells LineFacts16.cells_eq LineFacts16.facts LineFacts16.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly16
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly16.sound
