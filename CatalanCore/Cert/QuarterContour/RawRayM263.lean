module
public import CatalanCore.Cert.SigmaQuarterContour.RayM263
public import CatalanCore.Cert.QuarterContour.RawRayAssembly
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.RawRayM263
open CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def macros : List Macro := [rayF263B0P0,rayF263B0P1,rayF263B0P2,rayF263B0P3,rayF263B0P4,rayF263B0P5,rayF263B0P6,rayF263B0P7,rayF263B1P0,rayF263B1P1,rayF263B1P2,rayF263B1P3,rayF263B1P4,rayF263B1P5,rayF263B1P6,rayF263B1P7,rayF263B2P0,rayF263B2P1,rayF263B2P2,rayF263B2P3,rayF263B2P4,rayF263B2P5,rayF263B2P6,rayF263B2P7,rayF263B3P0,rayF263B3P1,rayF263B3P2,rayF263B3P3,rayF263B3P4,rayF263B3P5,rayF263B3P6,rayF263B3P7,rayF263B4P0,rayF263B4P1,rayF263B4P2,rayF263B4P3,rayF263B4P4,rayF263B4P5,rayF263B4P6,rayF263B4P7,rayF263B5P0]
def cells : List QBox := boxes macros
def lo : ℚ := (687/512)
def hi : ℚ := (3/2)
theorem facts : RayMacroFacts (1/100000) (115867/50000) SigmaQuarterContour.pts macros := by
  unfold macros
  exact rayMacroFacts_cons _ _ _ _ _ rayF263B0P0_far rayF263B0P0_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P1_far rayF263B0P1_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P2_far rayF263B0P2_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P3_far rayF263B0P3_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P4_far rayF263B0P4_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P5_far rayF263B0P5_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P6_far rayF263B0P6_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B0P7_far rayF263B0P7_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P0_far rayF263B1P0_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P1_far rayF263B1P1_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P2_far rayF263B1P2_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P3_far rayF263B1P3_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P4_far rayF263B1P4_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P5_far rayF263B1P5_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P6_far rayF263B1P6_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B1P7_far rayF263B1P7_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P0_far rayF263B2P0_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P1_far rayF263B2P1_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P2_far rayF263B2P2_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P3_far rayF263B2P3_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P4_far rayF263B2P4_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P5_far rayF263B2P5_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P6_far rayF263B2P6_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B2P7_far rayF263B2P7_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P0_far rayF263B3P0_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P1_far rayF263B3P1_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P2_far rayF263B3P2_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P3_far rayF263B3P3_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P4_far rayF263B3P4_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P5_far rayF263B3P5_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P6_far rayF263B3P6_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B3P7_far rayF263B3P7_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P0_far rayF263B4P0_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P1_far rayF263B4P1_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P2_far rayF263B4P2_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P3_far rayF263B4P3_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P4_far rayF263B4P4_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P5_far rayF263B4P5_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P6_far rayF263B4P6_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B4P7_far rayF263B4P7_ok (rayMacroFacts_cons _ _ _ _ _ rayF263B5P0_far rayF263B5P0_ok (rayMacroFacts_nil _ _ _)))))))))))))))))))))))))))))))))))))))))
theorem shapes_checked : cells.all (fun b => decide (rayShape (12/5) (107/1000) (1/2^30) b)) = true := by decide +kernel
theorem cover_checked : chainCovers (cells.map (rayInterval (12/5))) lo hi = true := by decide +kernel
theorem chunk_bound : RayChunkBound (1/100000) (115867/50000) (12/5) (107/1000) (1/2^30) SigmaQuarterContour.pts (lo,hi) := by
  intro u delta hu hU hd
  exact ray_macros_cover_sound (1/100000) (115867/50000) (12/5) (107/1000) (1/2^30) lo hi
    (by norm_num) (by norm_num) SigmaQuarterContour.pts macros facts
    (fun b hb => of_decide_eq_true ((List.all_eq_true.mp shapes_checked) b hb))
    (fun x hx hy => chainCovers_sound _ _ _ cover_checked x hx hy) u delta hu hU hd
end CatalanCore.Cert.QuarterContour.RawRayM263
#print axioms CatalanCore.Cert.QuarterContour.RawRayM263.chunk_bound
