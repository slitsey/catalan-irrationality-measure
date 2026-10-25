module
public import CatalanCore.Cert.QuarterContour.LineFacts9
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly9
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts9.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros9
    LineFacts9.cells LineFacts9.cells_eq LineFacts9.facts LineFacts9.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly9
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly9.sound
