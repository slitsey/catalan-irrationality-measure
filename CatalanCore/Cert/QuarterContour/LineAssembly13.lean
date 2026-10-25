module
public import CatalanCore.Cert.QuarterContour.LineFacts13
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly13
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts13.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros13
    LineFacts13.cells LineFacts13.cells_eq LineFacts13.facts LineFacts13.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly13
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly13.sound
