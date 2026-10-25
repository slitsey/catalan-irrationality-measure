module
public import CatalanCore.Cert.QuarterContour.PolyRayCertificate0
public import CatalanCore.Cert.QuarterContour.PolyRayCertificate1
public import CatalanCore.Cert.QuarterContour.PolyRayCertificate2
public import CatalanCore.Cert.QuarterContour.RayCellCover
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PolyRay1024
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def cells : List QBox := PolyModel0.cells ++ (PolyModel1.cells ++ PolyModel2.cells)
def upper : ℚ := (1333159527*5)/(12*2^40)

theorem shapes_checked : cells.all (fun b => decide (rayShape (12/5) (107/1000) (1/2^30) b)) = true := by decide +kernel

theorem cover_checked : chainCovers (cells.map (rayInterval (12/5))) 0 upper = true := by decide +kernel

theorem cells_length : cells.length = 1024 := by
  simp only [cells,List.length_append,PolyModel0.cells_length,PolyModel1.cells_length,PolyModel2.cells_length]

theorem ray_bound (u delta : ℝ) (hu : 0 ≤ u) (hU : u ≤ (upper : ℝ))
    (hd : |delta| ≤ (1/2^30 : ℝ)) :
    ((115867/50000 : ℚ) : ℝ) ≤
      gQuarter (1/100000) pts (-107/1000-u+delta) ((12/5)*u) := by
  have ex : -(107/1000 : ℝ)+delta-u = -107/1000-u+delta := by ring
  have h := ray_cells_cover_sound (gQuarter (1/100000) pts) (12/5) (107/1000)
    (1/2^30) 0 upper (115867/50000) (by norm_num) cells
    (fun b hb => of_decide_eq_true ((List.all_eq_true.mp shapes_checked) b hb))
    (fun x hx hy => chainCovers_sound _ _ _ cover_checked x hx hy) ?_ u delta (by simpa using hu) hU (by norm_num at hd ⊢; exact hd)
  · simpa only [Rat.cast_div,Rat.cast_ofNat,ex] using h
  · intro b hb v d hdv h1 h2 h3 h4
    norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] at hdv h1 h2 h3 h4 ⊢
    have ev : -(107/1000 : ℝ)+d-v = -107/1000-v+d := by ring
    rw [ev] at h1 h2 ⊢
    rcases (List.mem_append (s := PolyModel0.cells) (t := PolyModel1.cells ++ PolyModel2.cells)).mp hb with hb | hb
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using PolyRayCertificate0.ray_cell_sound b hb v d (by norm_num at hdv ⊢; exact hdv) (by norm_num at h1 ⊢; exact h1) (by norm_num at h2 ⊢; exact h2) (by norm_num at h3 ⊢; exact h3) (by norm_num at h4 ⊢; exact h4)
    · rcases (List.mem_append (s := PolyModel1.cells) (t := PolyModel2.cells)).mp hb with hb | hb
      · simpa only [Rat.cast_div,Rat.cast_ofNat] using PolyRayCertificate1.ray_cell_sound b hb v d (by norm_num at hdv ⊢; exact hdv) (by norm_num at h1 ⊢; exact h1) (by norm_num at h2 ⊢; exact h2) (by norm_num at h3 ⊢; exact h3) (by norm_num at h4 ⊢; exact h4)
      · simpa only [Rat.cast_div,Rat.cast_ofNat] using PolyRayCertificate2.ray_cell_sound b hb v d (by norm_num at hdv ⊢; exact hdv) (by norm_num at h1 ⊢; exact h1) (by norm_num at h2 ⊢; exact h2) (by norm_num at h3 ⊢; exact h3) (by norm_num at h4 ⊢; exact h4)
end CatalanCore.Cert.QuarterContour.PolyRay1024
#print axioms CatalanCore.Cert.QuarterContour.PolyRay1024.ray_bound
