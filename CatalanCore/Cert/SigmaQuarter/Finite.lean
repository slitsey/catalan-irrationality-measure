module

public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Ray0
public import CatalanCore.Cert.SigmaQuarter.Ray1
public import CatalanCore.Cert.SigmaQuarter.Ray2
public import CatalanCore.Cert.SigmaQuarter.Ray3
public import CatalanCore.Cert.SigmaQuarter.Ray4
public import CatalanCore.Cert.SigmaQuarter.Ray5
public import CatalanCore.Cert.SigmaQuarter.Ray6
public import CatalanCore.Cert.SigmaQuarter.Ray7
public import CatalanCore.Cert.SigmaQuarter.Ray8
public import CatalanCore.Cert.SigmaQuarter.Seg0
public import CatalanCore.Cert.SigmaQuarter.Seg1
public import CatalanCore.Cert.SigmaQuarter.Seg2
public import CatalanCore.Cert.SigmaQuarter.Seg3
public import CatalanCore.Cert.SigmaQuarter.Line0
public import CatalanCore.Cert.SigmaQuarter.Line1
public import CatalanCore.Cert.SigmaQuarter.Line2

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rays : List Macro := Ray0Data ++ Ray1Data ++ Ray2Data ++ Ray3Data ++ Ray4Data ++ Ray5Data ++ Ray6Data ++ Ray7Data ++ Ray8Data
theorem rays_far : ∀ m ∈ rays, farOK pts m := by
  intro m hm
  simp only [rays, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  exacts [Ray0_farAll m h0,Ray1_farAll m h1,Ray2_farAll m h2,Ray3_farAll m h3,Ray4_farAll m h4,Ray5_farAll m h5,Ray6_farAll m h6,Ray7_farAll m h7,Ray8_farAll m h8]
theorem rays_ok : ∀ m ∈ rays, rayOK pts (9327 / 4000) m = true := by
  intro m hm
  simp only [rays, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  exacts [Ray0_okAll m h0,Ray1_okAll m h1,Ray2_okAll m h2,Ray3_okAll m h3,Ray4_okAll m h4,Ray5_okAll m h5,Ray6_okAll m h6,Ray7_okAll m h7,Ray8_okAll m h8]
def segs : List Macro := Seg0Data ++ Seg1Data ++ Seg2Data ++ Seg3Data
theorem segs_far : ∀ m ∈ segs, farOK pts m := by
  intro m hm
  simp only [segs, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3
  exacts [Seg0_farAll m h0,Seg1_farAll m h1,Seg2_farAll m h2,Seg3_farAll m h3]
theorem segs_ok : ∀ m ∈ segs, axisOK pts m = true := by
  intro m hm
  simp only [segs, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3
  exacts [Seg0_okAll m h0,Seg1_okAll m h1,Seg2_okAll m h2,Seg3_okAll m h3]
def lines : List Macro := Line0Data ++ Line1Data ++ Line2Data
theorem lines_far : ∀ m ∈ lines, farOK pts m := by
  intro m hm
  simp only [lines, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2
  exacts [Line0_farAll m h0,Line1_farAll m h1,Line2_farAll m h2]
theorem lines_ok : ∀ m ∈ lines, axisOK pts m = true := by
  intro m hm
  simp only [lines, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2
  exacts [Line0_okAll m h0,Line1_okAll m h1,Line2_okAll m h2]
theorem rays_shape_check : (boxes rays).all (fun b => decide (rayShape b)) = true := by decide +kernel
theorem segs_shape_check : (boxes segs).all (fun b => decide (segShape b)) = true := by decide +kernel
theorem lines_shape_check : (boxes lines).all (fun b => decide (lineShape b)) = true := by decide +kernel
theorem ray_cover_check : chainCovers (rayIntervals rays) 0 (3 / 2) = true := by decide +kernel
theorem seg_cover_check : chainCovers (intervals segs) (-1 / 10) 0 = true := by decide +kernel
theorem line_cover_check : chainCovers (intervals lines) 0 1 = true := by decide +kernel
theorem scost_check : (-1353 / 50000 : ℚ) ≤ ((boxes segs).map segCost).sum := by decide +kernel
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
  ray_cover := ray_cover_check
  seg_cover := seg_cover_check
  line_cover := line_cover_check
  scost := scost_check
end CatalanCore.Cert.SigmaQuarter
