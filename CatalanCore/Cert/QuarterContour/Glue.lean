module
public import CatalanCore.Cert.QuarterContour.Macros
public import CatalanCore.Cert.QuarterContour.Witness
public import CatalanCore.Cert.SigmaQuarter.Cover
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def boxes (ms : List Macro) : List QBox := ms.flatMap Macro.boxes
def rayInterval (sl : ℚ) (b : QBox) : ℚ × ℚ :=
  ((b.1.2.2.1 : ℚ)/(sl*2^40),(b.1.2.2.2 : ℚ)/(sl*2^40))
def axisInterval (b : QBox) : ℚ × ℚ := ((b.1.1 : ℚ)/2^40,(b.1.2.1 : ℚ)/2^40)
def gamma (b : QBox) : ℚ := (b.2.2.2.1 : ℚ)/2^32
def intervals (ms : List Macro) : List (ℚ × ℚ) := (boxes ms).map axisInterval
def rayIntervals (sl : ℚ) (ms : List Macro) : List (ℚ × ℚ) := (boxes ms).map (rayInterval sl)
def segCost (mp : ℚ) (b : QBox) : ℚ :=
  ((axisInterval b).2-(axisInterval b).1)*qmin (gamma b-mp) 0

def rayShape (sl r0 W : ℚ) (b : QBox) : Prop :=
  0 ≤ (rayInterval sl b).1 ∧
  (b.1.1 : ℚ)/2^40 ≤ -r0-(rayInterval sl b).2-W ∧
  -r0-(rayInterval sl b).1+W ≤ (b.1.2.1 : ℚ)/2^40

def segShape (b : QBox) : Prop := b.1.1 ≤ b.1.2.1 ∧ b.1.2.1 ≤ 0
def lineShape (gm : ℚ) (b : QBox) : Prop := b.1.2.1 ≤ 2^40 ∧ gm ≤ gamma b
instance (sl r0 W : ℚ) (b : QBox) : Decidable (rayShape sl r0 W b) := by unfold rayShape; infer_instance
instance (b : QBox) : Decidable (segShape b) := by unfold segShape; infer_instance
instance (gm : ℚ) (b : QBox) : Decidable (lineShape gm b) := by unfold lineShape; infer_instance

structure Controls (pts : List Pt) (sl r0 W umax epsilon mp gm sb : ℚ)
    (rays segs lines : List Macro) : Prop where
  ray_far : ∀ m ∈ rays, farOK pts m
  ray_ok : ∀ m ∈ rays, QuarterContour.rayOK epsilon pts mp m = true
  seg_far : ∀ m ∈ segs, farOK pts m
  seg_ok : ∀ m ∈ segs, axisOK pts m = true
  line_far : ∀ m ∈ lines, farOK pts m
  line_ok : ∀ m ∈ lines, axisOK pts m = true
  ray_shape : ∀ b ∈ boxes rays, rayShape sl r0 W b
  seg_shape : ∀ b ∈ boxes segs, segShape b
  line_shape : ∀ b ∈ boxes lines, lineShape gm b
  ray_cover : IntervalCovers (rayIntervals sl rays) 0 umax
  seg_cover : IntervalCovers (intervals segs) (-r0) 0
  line_cover : IntervalCovers (intervals lines) 0 1
  scost : sb ≤ ((boxes segs).map (segCost mp)).sum

variable {pts : List Pt} {sl r0 W umax epsilon mp gm sb : ℚ} {rays segs lines : List Macro}

 theorem ray_gQuarter (he : epsilon ≤ 1/1000)
    (C : Controls pts sl r0 W umax epsilon mp gm sb rays segs lines)
    (b : QBox) (hb : b ∈ boxes rays) (x y : ℝ)
    (h1 : (b.1.1 : ℝ)/2^40 ≤ x) (h2 : x ≤ (b.1.2.1 : ℝ)/2^40)
    (h3 : (b.1.2.2.1 : ℝ)/2^40 ≤ y) (h4 : y ≤ (b.1.2.2.2 : ℝ)/2^40) :
    (mp : ℝ) ≤ QuarterContour.gQuarter epsilon pts x y := by
  obtain ⟨m,hm,hb⟩ := List.mem_flatMap.mp hb
  exact QuarterContour.rayMacro_sound epsilon he pts mp m (C.ray_far m hm) (C.ray_ok m hm)
    b hb x y h1 h2 h3 h4

theorem axis_gQuarter (pts : List Pt) (epsilon : ℚ) (ms : List Macro)
    (hf : ∀ m ∈ ms, farOK pts m) (hc : ∀ m ∈ ms, axisOK pts m = true)
    (b : QBox) (hb : b ∈ boxes ms) (x : ℝ)
    (h1 : (b.1.1 : ℝ)/2^40 ≤ x) (h2 : x ≤ (b.1.2.1 : ℝ)/2^40) :
    (gamma b : ℝ) ≤ QuarterContour.gQuarter epsilon pts x 0 := by
  obtain ⟨m,hm,hb⟩ := List.mem_flatMap.mp hb
  simpa [gamma] using QuarterContour.axisMacro_sound epsilon pts m (hf m hm) (hc m hm) b hb x h1 h2

theorem ray_box_bound (he : epsilon ≤ 1/1000) (hsl : 0 < sl) (hrW : W < r0)
    (C : Controls pts sl r0 W umax epsilon mp gm sb rays segs lines)
    (p : ℚ × ℚ) (hp : p ∈ rayIntervals sl rays) (x y : ℝ)
    (h1 : -(r0 : ℝ)-p.2-W ≤ x) (h2 : x ≤ -(r0 : ℝ)-p.1+W)
    (h3 : (sl : ℝ)*(p.1 : ℝ) ≤ y) (h4 : y ≤ (sl : ℝ)*(p.2 : ℝ)) :
    (mp : ℝ) ≤ gAlpha (1/2048) epsilon (positions pts) (masses pts) (1/4)
      (CatalanCore.Decay.Unu (1/4)) ⟨x,y⟩ := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  have hs := C.ray_shape b hb
  have ha : (0 : ℝ) ≤ ((rayInterval sl b).1 : ℝ) := Rat.cast_nonneg.mpr hs.1
  have hslR : (0 : ℝ) < sl := Rat.cast_pos.mpr hsl
  have hrWR : (W : ℝ) < r0 := Rat.cast_lt.mpr hrW
  have hx1 : (b.1.1 : ℝ)/2^40 ≤ x := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    push_cast at hh
    linarith
  have hx2 : x ≤ (b.1.2.1 : ℝ)/2^40 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hs.2.2
    push_cast at hh
    linarith
  have es (q : ℤ) : (sl : ℝ)*(((q : ℚ)/(sl*2^40) : ℚ) : ℝ) = (q : ℝ)/2^40 := by
    push_cast
    field_simp [ne_of_gt hslR]
    <;> ring
  have hy1 : (b.1.2.2.1 : ℝ)/2^40 ≤ y := by
    change (sl : ℝ)*(((b.1.2.2.1 : ℚ)/(sl*2^40) : ℚ) : ℝ) ≤ y at h3
    rwa [es] at h3
  have hy2 : y ≤ (b.1.2.2.2 : ℝ)/2^40 := by
    change y ≤ (sl : ℝ)*(((b.1.2.2.2 : ℚ)/(sl*2^40) : ℚ) : ℝ) at h4
    rwa [es] at h4
  have hx : x < 0 := by linarith
  have hy : 0 ≤ y := le_trans (mul_nonneg hslR.le ha) h3
  rw [gAlpha_bridge epsilon pts x y hx hy]
  exact ray_gQuarter he C b hb x y hx1 hx2 hy1 hy2

theorem segment_bound (C : Controls pts sl r0 W umax epsilon mp gm sb rays segs lines)
    (b : QBox) (hb : b ∈ boxes segs) (x : ℝ)
    (h1 : ((axisInterval b).1 : ℝ) ≤ x) (h2 : x ≤ ((axisInterval b).2 : ℝ)) :
    (gamma b : ℝ) ≤ gAlpha (1/2048) epsilon (positions pts) (masses pts) (1/4)
      (CatalanCore.Decay.Unu (1/4)) ⟨x,0⟩ := by
  have hs := C.seg_shape b hb
  have hx : x ≤ 1 := by
    dsimp [axisInterval] at h2
    push_cast at h2
    have hh : (b.1.2.1 : ℝ) ≤ 0 := by exact_mod_cast hs.2
    linarith
  rw [gAlpha_bridge_axis epsilon pts x hx]
  exact axis_gQuarter pts epsilon segs C.seg_far C.seg_ok b hb x
    (by simpa [axisInterval] using h1) (by simpa [axisInterval] using h2)

theorem line_bound (C : Controls pts sl r0 W umax epsilon mp gm sb rays segs lines)
    (p : ℚ × ℚ) (hp : p ∈ intervals lines) (x : ℝ)
    (h1 : (p.1 : ℝ) ≤ x) (h2 : x ≤ (p.2 : ℝ)) :
    (gm : ℝ) ≤ gAlpha (1/2048) epsilon (positions pts) (masses pts) (1/4)
      (CatalanCore.Decay.Unu (1/4)) ⟨x,0⟩ := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  have hs := C.line_shape b hb
  have hx : x ≤ 1 := by
    dsimp [axisInterval] at h2
    push_cast at h2
    have hh : (b.1.2.1 : ℝ) ≤ 2^40 := by exact_mod_cast hs.1
    linarith
  rw [gAlpha_bridge_axis epsilon pts x hx]
  have hg : (gm : ℝ) ≤ (gamma b : ℝ) := Rat.cast_le.mpr hs.2
  exact hg.trans (axis_gQuarter pts epsilon lines C.line_far C.line_ok b hb x
    (by simpa [axisInterval] using h1) (by simpa [axisInterval] using h2))
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.ray_box_bound
#print axioms CatalanCore.Cert.QuarterContour.segment_bound
#print axioms CatalanCore.Cert.QuarterContour.line_bound
