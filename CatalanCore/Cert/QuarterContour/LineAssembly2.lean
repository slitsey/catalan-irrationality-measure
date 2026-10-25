module
public import CatalanCore.Cert.QuarterContour.LineFacts2
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly2
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts2.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros2
    LineFacts2.cells LineFacts2.cells_eq LineFacts2.facts LineFacts2.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly2
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly2.sound
