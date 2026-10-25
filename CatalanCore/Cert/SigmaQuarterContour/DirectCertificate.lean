module
public import CatalanCore.Cert.SigmaQuarterContour.PointFacts
public import CatalanCore.Cert.QuarterContour.Glue
public import CatalanCore.Cert.QuarterContour.NodeSymmetry
public import CatalanCore.Cert.QuarterContour.Tail
public import CatalanCore.Cert.QuarterContour.UniformRayBridge
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour.Direct
open CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaQuarter
open CatalanCore.Cert.SigmaP6 (qmin_cast)
set_option maxRecDepth 100000

noncomputable def gQ (s : ℂ) : ℝ :=
  gAlpha (1/2048) (1/100000) (positions pts) (masses pts) (1/4)
    (CatalanCore.Decay.Unu (1/4)) s

/-- Concrete analytic obligations, independent of how numerical cells were proved. -/
structure Controls (sb : ℚ) (segs lines : List QBox) : Prop where
  ray_tube : ∀ u delta : ℝ, 0 ≤ u → u ≤ (3/2 : ℝ) → |delta| ≤ (1/2^30 : ℝ) →
    ((115867/50000 : ℚ) : ℝ) ≤ gQ ⟨-107/1000+delta-u,(12/5)*u⟩
  seg_shape : ∀ b ∈ segs, QuarterContour.segShape b
  seg_sound : ∀ b ∈ segs, ∀ x : ℝ,
    ((axisInterval b).1 : ℝ) ≤ x → x ≤ ((axisInterval b).2 : ℝ) →
    (gamma b : ℝ) ≤ gQ ⟨x,0⟩
  seg_cover : IntervalCovers (segs.map axisInterval) (-107/1000) 0
  scost : sb ≤ (segs.map (segCost (115867/50000))).sum
  line_sound : ∀ b ∈ lines, ∀ x : ℝ,
    ((axisInterval b).1 : ℝ) ≤ x → x ≤ ((axisInterval b).2 : ℝ) →
    ((-28907/20000 : ℚ) : ℝ) ≤ gQ ⟨x,0⟩
  line_cover : IntervalCovers (lines.map axisInterval) 0 1

lemma sum_get_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  conv_rhs => rw [← List.ofFn_get l,List.map_ofFn,List.sum_ofFn]
  rfl

lemma cost_cast (b : QBox) : (segCost (115867/50000) b : ℝ) =
    (((axisInterval b).2 : ℝ)-(axisInterval b).1)*
      min ((gamma b : ℝ)-(115867/50000 : ℝ)) 0 := by
  unfold segCost
  push_cast
  norm_num

lemma sum_cost_cast (l : List QBox) :
    ((l.map (segCost (115867/50000))).sum : ℝ) =
      (l.map (fun b => (segCost (115867/50000) b : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

/-- Assemble the existing continuum interface from direct tube and axis proofs.
The symbolic fine grid is never evaluated. -/
noncomputable def assemble {sb : ℚ} {segs lines : List QBox} (C : Controls sb segs lines)
    (hI : CatalanLambda.Decay.Irho (1/2048 : ℝ) (positions pts) (masses pts) ≤
      (179918953/100000000 : ℝ)) :
    CertCoreGs (12/5 : ℝ) pts.length (1/2048 : ℝ) (1/100000 : ℝ)
      (positions pts) (masses pts) where
  g := gQ
  r0 := 107/1000
  W := 1/2^32
  umax := 3/2
  mprime := 115867/50000
  gmin := -28907/20000
  Sbase := sb
  Ibound := 179918953/100000000
  ccert := 376269/50000
  r0_pos := by norm_num
  W_pos := by norm_num
  hρ := by norm_num
  hε0 := by norm_num
  hε1 := by norm_num
  hm := SigmaQuarterContour.mass_sum
  g_conj := by
    intro s
    exact gAlpha_conj_of_involution (1/2048) (1/100000) (1/4) (positions pts) (masses pts)
      sigma sigma_involutive sigma_positions sigma_masses s
  rayBoxes := UniformRayGrid.intervals (2^32) (3/2)
  ray_box_ok := by
    intro p hp x y h1 h2 h3 h4
    have hr := uniform_rectangles_of_ray_tube gQ (12/5) (107/1000) (1/2^32)
      (1/2^30) (3/2) (115867/50000) (2^32) (by norm_num) (by norm_num)
      (by norm_num) quarter_grid_width (by simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_pow,neg_div] using C.ray_tube) p hp x y
    apply hr
    · exact h1
    · exact h2
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h3
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h4
  ray_cover := by
    intro u h0 h1
    exact UniformRayGrid.covers (2^32) (3/2) (by norm_num) u (by simpa using h0) h1
  ray_tail := by
    intro u delta hu hd
    have hd' : |delta| ≤ (1/2^30 : ℝ) := by
      have he : (((1/2^32 : ℚ) : ℝ)) ≤ (1/2^30 : ℝ) := by norm_num
      exact hd.trans he
    have ht := tail_core (12/5) (107/1000) (1/100000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (positions pts) (masses pts) (mass_nonneg pts) SigmaQuarterContour.mass_sum radius_le
      u delta (by convert hu using 1 <;> norm_num) hd'
    simpa only [gQ,Rat.cast_div,Rat.cast_ofNat,neg_div] using (by norm_num : (((115867/50000 : ℚ) : ℝ)) ≤ 3).trans ht
  nSeg := segs.length
  segA := fun i => (axisInterval (segs.get i)).1
  segB := fun i => (axisInterval (segs.get i)).2
  segG := fun i => gamma (segs.get i)
  seg_ab := by
    intro i
    have hs := C.seg_shape _ (List.get_mem _ i)
    dsimp [axisInterval]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs.1) (by positivity)
  seg_ok := by
    intro i x h1 h2
    exact C.seg_sound _ (List.get_mem _ i) x h1 h2
  seg_cover := by
    intro x h0 h1
    obtain ⟨p,hp,ha,hb⟩ := C.seg_cover x (by simpa only [Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,neg_div] using h0) (by simpa using h1)
    obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp hp
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hbmem
    exact ⟨i,by simpa only [hi] using ha,by simpa only [hi] using hb⟩
  Sbase_le := by
    have hh : (sb : ℝ) ≤ ((segs.map (segCost (115867/50000))).sum : ℝ) := by exact_mod_cast C.scost
    rw [sum_cost_cast,← sum_get_eq] at hh
    simp only [cost_cast] at hh
    norm_num at hh ⊢
    exact hh
  lineCells := lines.map axisInterval
  line_ok := by
    intro p hp x h1 h2
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact C.line_sound b hb x h1 h2
  line_cover := by
    intro x h0 h1
    exact C.line_cover x (by simpa using h0) (by simpa using h1)
  I_ok := by convert hI using 1 <;> norm_num
  ccert_ge := by norm_num

/-- The rounded final arithmetic fits the promised14.21 endpoint. -/
theorem final_ratio :
    (376269/50000 : ℚ)/((1485123059/320000000 : ℚ)-339258406689121/82516315939200)
      ≤ (1421/100 : ℚ) := by norm_num

end CatalanCore.Cert.SigmaQuarterContour.Direct
#print axioms CatalanCore.Cert.SigmaQuarterContour.Direct.assemble
#print axioms CatalanCore.Cert.SigmaQuarterContour.Direct.final_ratio
