module
public import CatalanCore.Cert.SigmaQuarterContour.DirectCertificate
public import CatalanCore.Cert.QuarterContour.RawRayAssembly
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour.ControlsBridge
open CatalanCore.Cert.QuarterContour CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Convert independently checked tube, segment and line bounds into the final controls.
This generic bridge imports no unfinished numerical assembly family. -/
theorem of_bounds (SB : ℚ) (segs lines : List QBox)
    (hray : RayChunkBound (1/100000) (115867/50000) (12/5) (107/1000)
      (1/2^30) pts (0,3/2))
    (hshape : ∀ b ∈ segs, QuarterContour.segShape b)
    (hsegcover : IntervalCovers (segs.map axisInterval) (-107/1000) 0)
    (hscost : SB ≤ (segs.map (segCost (115867/50000))).sum)
    (hseg : ∀ b ∈ segs, ∀ x : ℝ,
      (b.1.1 : ℝ)/2^40 ≤ x → x ≤ (b.1.2.1 : ℝ)/2^40 →
      (gamma b : ℝ) ≤ gQuarter (1/100000) pts x 0)
    (hline : ∀ b ∈ lines, ∀ x : ℝ,
      ((axisInterval b).1 : ℝ) ≤ x → x ≤ ((axisInterval b).2 : ℝ) →
      ((-28907/20000 : ℚ) : ℝ) ≤ Direct.gQ ⟨x,0⟩)
    (hlinecover : IntervalCovers (lines.map axisInterval) 0 1) :
    Direct.Controls SB segs lines := by
  refine {
    ray_tube := ?_
    seg_shape := hshape
    seg_sound := ?_
    seg_cover := hsegcover
    scost := hscost
    line_sound := hline
    line_cover := hlinecover }
  · intro u delta hu hU hd
    have hdelta : delta ≤ (1/2^30 : ℝ) := (abs_le.mp hd).2
    have hW : (1/2^30 : ℝ) < 107/1000 := by norm_num
    have hx : (-107/1000 : ℝ)+delta-u < 0 := by linarith
    have hy : (0 : ℝ) ≤ (12/5 : ℝ)*u := mul_nonneg (by norm_num) hu
    change _ ≤ gAlpha (1/2048) (1/100000) (positions pts) (masses pts) (1/4)
      (CatalanCore.Decay.Unu (1/4)) ⟨-107/1000+delta-u,(12/5)*u⟩
    have heps : (((1/100000 : ℚ) : ℝ)) = (1/100000 : ℝ) := by norm_num
    rw [← heps,gAlpha_bridge (1/100000) pts _ _ hx hy]
    have hh := hray u delta (by simpa using hu)
      (by simpa only [Rat.cast_div,Rat.cast_ofNat] using hU)
      (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hd)
    simpa only [Rat.cast_div,Rat.cast_ofNat,neg_div] using hh
  · intro b hb x h1 h2
    have hlo := h1
    have hhi := h2
    dsimp [axisInterval] at hlo hhi
    push_cast at hlo hhi
    have hnonpos : (b.1.2.1 : ℝ) ≤ 0 := by
      exact_mod_cast (hshape b hb).2
    have hx0 : x ≤ 0 :=
      hhi.trans (div_nonpos_of_nonpos_of_nonneg hnonpos (by positivity))
    have hx : x ≤ 1 := hx0.trans (by norm_num)
    change _ ≤ gAlpha (1/2048) (1/100000) (positions pts) (masses pts) (1/4)
      (CatalanCore.Decay.Unu (1/4)) ⟨x,0⟩
    have heps : (((1/100000 : ℚ) : ℝ)) = (1/100000 : ℝ) := by norm_num
    rw [← heps,gAlpha_bridge_axis (1/100000) pts x hx]
    exact hseg b hb x hlo hhi
end CatalanCore.Cert.SigmaQuarterContour.ControlsBridge
#print axioms CatalanCore.Cert.SigmaQuarterContour.ControlsBridge.of_bounds
