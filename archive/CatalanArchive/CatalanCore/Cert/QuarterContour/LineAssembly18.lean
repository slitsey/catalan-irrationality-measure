module
public import CatalanCore.Cert.QuarterContour.LineFacts18
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly18
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts18.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros18
    LineFacts18.cells LineFacts18.cells_eq LineFacts18.facts LineFacts18.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly18
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly18.sound
