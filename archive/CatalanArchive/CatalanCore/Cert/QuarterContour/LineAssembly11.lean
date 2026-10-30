module
public import CatalanCore.Cert.QuarterContour.LineFacts11
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly11
open CatalanCore.Cert.QuarterContour.RawLineAssembly
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts LineFacts11.cells :=
  cells_sound (1/100000) (-28907/20000) SigmaQuarterContour.pts SigmaQuarterContour.lineMacros11
    LineFacts11.cells LineFacts11.cells_eq LineFacts11.facts LineFacts11.shapes
end CatalanCore.Cert.QuarterContour.LineAssembly11
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly11.sound
