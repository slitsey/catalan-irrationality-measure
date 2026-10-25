module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem pointGroup92_0 : ([2944,2945,2946,2947,2948,2949] : List ℕ).all pointOK = true := by decide +kernel
theorem checkChunk_92 : (checkChunk 92).all pointOK = true := by
  have h : checkChunk 92 = [2944,2945,2946,2947,2948,2949] := by decide +kernel
  rw [h]
  simp only [List.all_append, pointGroup92_0, Bool.and_self]
end CatalanCore.Cert.SigmaQuarterContour
