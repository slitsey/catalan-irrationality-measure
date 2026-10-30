module
public import CatalanCore.Cert.QuarterContour.LineAssembly0
public import CatalanCore.Cert.QuarterContour.LineAssembly1
public import CatalanCore.Cert.QuarterContour.LineAssembly2
public import CatalanCore.Cert.QuarterContour.LineAssembly3
public import CatalanCore.Cert.QuarterContour.LineAssembly4
public import CatalanCore.Cert.QuarterContour.LineAssembly5
public import CatalanCore.Cert.QuarterContour.LineAssembly6
public import CatalanCore.Cert.QuarterContour.LineAssembly7
public import CatalanCore.Cert.QuarterContour.LineAssembly8
public import CatalanCore.Cert.QuarterContour.LineAssembly9
public import CatalanCore.Cert.QuarterContour.LineAssembly10
public import CatalanCore.Cert.QuarterContour.LineAssembly11
public import CatalanCore.Cert.QuarterContour.LineAssembly12
public import CatalanCore.Cert.QuarterContour.LineAssembly13
public import CatalanCore.Cert.QuarterContour.LineAssembly14
public import CatalanCore.Cert.QuarterContour.LineAssembly15
public import CatalanCore.Cert.QuarterContour.LineAssembly16
public import CatalanCore.Cert.QuarterContour.LineAssembly17
public import CatalanCore.Cert.QuarterContour.LineAssembly18
public import CatalanCore.Cert.QuarterContour.LineAssembly19
public import CatalanCore.Cert.SigmaQuarterContour.DirectCertificate
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LineAssembly
open CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.QuarterContour.RawLineAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def chunks : List (List QBox) := [LineFacts0.cells,LineFacts1.cells,LineFacts2.cells,LineFacts3.cells,LineFacts4.cells,LineFacts5.cells,LineFacts6.cells,LineFacts7.cells,LineFacts8.cells,LineFacts9.cells,LineFacts10.cells,LineFacts11.cells,LineFacts12.cells,LineFacts13.cells,LineFacts14.cells,LineFacts15.cells,LineFacts16.cells,LineFacts17.cells,LineFacts18.cells,LineFacts19.cells]
def cells : List QBox := chunks.flatten
theorem shapes : ∀ b ∈ cells, lineShape (-28907/20000) b := by
  apply forall_flatten
  unfold chunks
  exact forall_mem_cons _ _ _ (LineFacts0.shapes) (forall_mem_cons _ _ _ (LineFacts1.shapes) (forall_mem_cons _ _ _ (LineFacts2.shapes) (forall_mem_cons _ _ _ (LineFacts3.shapes) (forall_mem_cons _ _ _ (LineFacts4.shapes) (forall_mem_cons _ _ _ (LineFacts5.shapes) (forall_mem_cons _ _ _ (LineFacts6.shapes) (forall_mem_cons _ _ _ (LineFacts7.shapes) (forall_mem_cons _ _ _ (LineFacts8.shapes) (forall_mem_cons _ _ _ (LineFacts9.shapes) (forall_mem_cons _ _ _ (LineFacts10.shapes) (forall_mem_cons _ _ _ (LineFacts11.shapes) (forall_mem_cons _ _ _ (LineFacts12.shapes) (forall_mem_cons _ _ _ (LineFacts13.shapes) (forall_mem_cons _ _ _ (LineFacts14.shapes) (forall_mem_cons _ _ _ (LineFacts15.shapes) (forall_mem_cons _ _ _ (LineFacts16.shapes) (forall_mem_cons _ _ _ (LineFacts17.shapes) (forall_mem_cons _ _ _ (LineFacts18.shapes) (forall_mem_cons _ _ _ (LineFacts19.shapes) (forall_mem_nil _))))))))))))))))))))
theorem sound : LineCellsSound (1/100000) (-28907/20000) SigmaQuarterContour.pts cells := by
  apply sound_flatten
  unfold chunks
  exact forall_mem_cons _ _ _ (LineAssembly0.sound) (forall_mem_cons _ _ _ (LineAssembly1.sound) (forall_mem_cons _ _ _ (LineAssembly2.sound) (forall_mem_cons _ _ _ (LineAssembly3.sound) (forall_mem_cons _ _ _ (LineAssembly4.sound) (forall_mem_cons _ _ _ (LineAssembly5.sound) (forall_mem_cons _ _ _ (LineAssembly6.sound) (forall_mem_cons _ _ _ (LineAssembly7.sound) (forall_mem_cons _ _ _ (LineAssembly8.sound) (forall_mem_cons _ _ _ (LineAssembly9.sound) (forall_mem_cons _ _ _ (LineAssembly10.sound) (forall_mem_cons _ _ _ (LineAssembly11.sound) (forall_mem_cons _ _ _ (LineAssembly12.sound) (forall_mem_cons _ _ _ (LineAssembly13.sound) (forall_mem_cons _ _ _ (LineAssembly14.sound) (forall_mem_cons _ _ _ (LineAssembly15.sound) (forall_mem_cons _ _ _ (LineAssembly16.sound) (forall_mem_cons _ _ _ (LineAssembly17.sound) (forall_mem_cons _ _ _ (LineAssembly18.sound) (forall_mem_cons _ _ _ (LineAssembly19.sound) (forall_mem_nil _))))))))))))))))))))
theorem line_cover : IntervalCovers (cells.map axisInterval) 0 1 := by
  have h0 := LineFacts0.cover
  have h1 := intervalCovers_append h0 LineFacts1.cover (by norm_num [LineFacts0.hi,LineFacts1.lo])
  have h2 := intervalCovers_append h1 LineFacts2.cover (by norm_num [LineFacts1.hi,LineFacts2.lo])
  have h3 := intervalCovers_append h2 LineFacts3.cover (by norm_num [LineFacts2.hi,LineFacts3.lo])
  have h4 := intervalCovers_append h3 LineFacts4.cover (by norm_num [LineFacts3.hi,LineFacts4.lo])
  have h5 := intervalCovers_append h4 LineFacts5.cover (by norm_num [LineFacts4.hi,LineFacts5.lo])
  have h6 := intervalCovers_append h5 LineFacts6.cover (by norm_num [LineFacts5.hi,LineFacts6.lo])
  have h7 := intervalCovers_append h6 LineFacts7.cover (by norm_num [LineFacts6.hi,LineFacts7.lo])
  have h8 := intervalCovers_append h7 LineFacts8.cover (by norm_num [LineFacts7.hi,LineFacts8.lo])
  have h9 := intervalCovers_append h8 LineFacts9.cover (by norm_num [LineFacts8.hi,LineFacts9.lo])
  have h10 := intervalCovers_append h9 LineFacts10.cover (by norm_num [LineFacts9.hi,LineFacts10.lo])
  have h11 := intervalCovers_append h10 LineFacts11.cover (by norm_num [LineFacts10.hi,LineFacts11.lo])
  have h12 := intervalCovers_append h11 LineFacts12.cover (by norm_num [LineFacts11.hi,LineFacts12.lo])
  have h13 := intervalCovers_append h12 LineFacts13.cover (by norm_num [LineFacts12.hi,LineFacts13.lo])
  have h14 := intervalCovers_append h13 LineFacts14.cover (by norm_num [LineFacts13.hi,LineFacts14.lo])
  have h15 := intervalCovers_append h14 LineFacts15.cover (by norm_num [LineFacts14.hi,LineFacts15.lo])
  have h16 := intervalCovers_append h15 LineFacts16.cover (by norm_num [LineFacts15.hi,LineFacts16.lo])
  have h17 := intervalCovers_append h16 LineFacts17.cover (by norm_num [LineFacts16.hi,LineFacts17.lo])
  have h18 := intervalCovers_append h17 LineFacts18.cover (by norm_num [LineFacts17.hi,LineFacts18.lo])
  have h19 := intervalCovers_append h18 LineFacts19.cover (by norm_num [LineFacts18.hi,LineFacts19.lo])
  simpa only [cells,chunks,LineFacts0.lo,LineFacts19.hi,List.flatten_cons,List.flatten_nil,List.map_append,List.map_nil,List.append_nil,List.append_assoc] using h19
theorem line_sound (b : QBox) (hb : b ∈ cells) (x : ℝ)
    (h1 : ((axisInterval b).1 : ℝ) ≤ x) (h2 : x ≤ ((axisInterval b).2 : ℝ)) :
    ((-28907/20000 : ℚ) : ℝ) ≤ SigmaQuarterContour.Direct.gQ ⟨x,0⟩ := by
  have hx2 := h2
  dsimp [axisInterval] at hx2
  push_cast at hx2
  have hh : (b.1.2.1 : ℝ) ≤ (2 : ℝ)^40 := by exact_mod_cast (shapes b hb).1
  have hx : x ≤ 1 := hx2.trans ((div_le_one (by positivity : (0 : ℝ) < 2^40)).mpr hh)
  change _ ≤ gAlpha (1/2048) (1/100000) (positions SigmaQuarterContour.pts)
    (masses SigmaQuarterContour.pts) (1/4) (CatalanCore.Decay.Unu (1/4)) ⟨x,0⟩
  have he : ((1/100000 : ℚ) : ℝ) = (1/100000 : ℝ) := by norm_num
  rw [← he,gAlpha_bridge_axis (1/100000) SigmaQuarterContour.pts x hx]
  exact sound b hb x h1 h2
end CatalanCore.Cert.QuarterContour.LineAssembly
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly.line_sound
#print axioms CatalanCore.Cert.QuarterContour.LineAssembly.line_cover
