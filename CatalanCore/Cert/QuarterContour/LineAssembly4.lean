module
public import CatalanCore.Cert.QuarterContour.LineFacts4
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly4
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts4.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros4
    LineFacts4.cells LineFacts4.cells_eq LineFacts4.facts LineFacts4.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly4
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly4.sound
