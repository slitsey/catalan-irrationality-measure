module
public import CatalanCore.Cert.SigmaQuarter.FiniteRay
public import CatalanCore.Cert.SigmaQuarter.FiniteSeg
public import CatalanCore.Cert.SigmaQuarter.FiniteLine

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def controls : Controls rays segs lines where
  ray_far := rays_far
  ray_ok := rays_ok
  seg_far := segs_far
  seg_ok := segs_ok
  line_far := lines_far
  line_ok := lines_ok
  ray_shape := by
    intro b hb
    exact of_decide_eq_true (List.all_eq_true.mp rays_shape_check b hb)
  seg_shape := by
    intro b hb
    exact of_decide_eq_true (List.all_eq_true.mp segs_shape_check b hb)
  line_shape := by
    intro b hb
    exact of_decide_eq_true (List.all_eq_true.mp lines_shape_check b hb)
  ray_cover := by simpa only [div_one] using ray_cover_check
  seg_cover := by simpa only [div_one] using seg_cover_check
  line_cover := by simpa only [div_one] using line_cover_check
  scost := scost_check
end CatalanCore.Cert.SigmaQuarter
