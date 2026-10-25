module
public import CatalanCore.Cert.QuarterContour.LineFacts15
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly15
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts15.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros15
    LineFacts15.cells LineFacts15.cells_eq LineFacts15.facts LineFacts15.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly15
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly15.sound
