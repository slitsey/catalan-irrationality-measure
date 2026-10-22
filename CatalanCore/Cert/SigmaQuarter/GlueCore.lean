module

public import CatalanCore.Cert.SigmaQuarter.Macros
public import CatalanCore.Cert.SigmaQuarter.Cover
public import CatalanCore.Cert.SigmaQuarter.Bridge
public import CatalanCore.Cert.SigmaQuarter.TailCore

@[expose] public section

open Real

namespace CatalanCore.Cert.SigmaQuarter

open CatalanCore.Cert.SigmaP6 (Pt qmin qmin_cast)

def boxes (ms : List Macro) : List QBox := ms.flatMap Macro.boxes
def rayInterval (b : QBox) : ℚ × ℚ :=
  ((b.1.2.2.1 : ℚ) / (3 * 2 ^ 40), (b.1.2.2.2 : ℚ) / (3 * 2 ^ 40))
def axisInterval (b : QBox) : ℚ × ℚ :=
  ((b.1.1 : ℚ) / 2 ^ 40, (b.1.2.1 : ℚ) / 2 ^ 40)
def gamma (b : QBox) : ℚ := (b.2.2.2.1 : ℚ) / 2 ^ 32
def intervals (ms : List Macro) : List (ℚ × ℚ) := (boxes ms).map axisInterval
def rayIntervals (ms : List Macro) : List (ℚ × ℚ) := (boxes ms).map rayInterval
lemma boxes_append (a b : List Macro) : boxes (a ++ b) = boxes a ++ boxes b := by
  simp only [boxes, List.flatMap_append]
lemma intervals_append (a b : List Macro) : intervals (a ++ b) = intervals a ++ intervals b := by
  simp only [intervals, boxes_append, List.map_append]
lemma rayIntervals_append (a b : List Macro) : rayIntervals (a ++ b) = rayIntervals a ++ rayIntervals b := by
  simp only [rayIntervals, boxes_append, List.map_append]

def segCost (b : QBox) : ℚ :=
  ((axisInterval b).2 - (axisInterval b).1) * qmin (gamma b - 231169/100000) 0

def rayShape (b : QBox) : Prop :=
  0 ≤ (rayInterval b).1 ∧
  (b.1.1 : ℚ) / 2 ^ 40 ≤ -1 / 10 - (rayInterval b).2 - 1 / 2 ^ 30 ∧
  -1 / 10 - (rayInterval b).1 + 1 / 2 ^ 30 ≤ (b.1.2.1 : ℚ) / 2 ^ 40

def segShape (b : QBox) : Prop := b.1.1 ≤ b.1.2.1 ∧ b.1.2.1 ≤ 0
def lineShape (b : QBox) : Prop :=
  b.1.2.1 ≤ 2 ^ 40 ∧ (-143459/100000 : ℚ) ≤ gamma b

instance (b : QBox) : Decidable (rayShape b) := by unfold rayShape; infer_instance
instance (b : QBox) : Decidable (segShape b) := by unfold segShape; infer_instance
instance (b : QBox) : Decidable (lineShape b) := by unfold lineShape; infer_instance

structure Controls (rays segs lines : List Macro) : Prop where
  ray_far : ∀ m ∈ rays, farOK pts m
  ray_ok : ∀ m ∈ rays, rayOK pts (231169/100000) m = true
  seg_far : ∀ m ∈ segs, farOK pts m
  seg_ok : ∀ m ∈ segs, axisOK pts m = true
  line_far : ∀ m ∈ lines, farOK pts m
  line_ok : ∀ m ∈ lines, axisOK pts m = true
  ray_shape : ∀ b ∈ boxes rays, rayShape b
  seg_shape : ∀ b ∈ boxes segs, segShape b
  line_shape : ∀ b ∈ boxes lines, lineShape b
  ray_cover : IntervalCovers (rayIntervals rays) 0 (3 / 2)
  seg_cover : IntervalCovers (intervals segs) (-1 / 10) 0
  line_cover : IntervalCovers (intervals lines) 0 1
  scost : (-274719/10000000 : ℚ) ≤ ((boxes segs).map segCost).sum

variable {rays segs lines : List Macro} (C : Controls rays segs lines)

include C in
theorem ray_gQuarter (b : QBox) (hb : b ∈ boxes rays) (x y : ℝ)
    (h1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40)
    (h3 : (b.1.2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ (b.1.2.2.2 : ℝ) / 2 ^ 40) :
    (231169/100000 : ℝ) ≤ gQuarter pts x y := by
  obtain ⟨m,hm,hb⟩ := List.mem_flatMap.mp hb
  have h := rayMacro_sound pts _ m (C.ray_far m hm) (C.ray_ok m hm) b hb x y h1 h2 h3 h4
  norm_num at h
  exact h

theorem axis_gQuarter (ms : List Macro)
    (hf : ∀ m ∈ ms, farOK pts m) (hc : ∀ m ∈ ms, axisOK pts m = true)
    (b : QBox) (hb : b ∈ boxes ms) (x : ℝ)
    (h1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40) :
    (gamma b : ℝ) ≤ gQuarter pts x 0 := by
  obtain ⟨m,hm,hb⟩ := List.mem_flatMap.mp hb
  have h := axisMacro_sound pts m (hf m hm) (hc m hm) b hb x h1 h2
  simpa [gamma] using h

include C in
theorem ray_box_bound (p : ℚ × ℚ) (hp : p ∈ rayIntervals rays) (x y : ℝ)
    (h1 : -(1 / 10 : ℝ) - p.2 - 1 / 2 ^ 30 ≤ x)
    (h2 : x ≤ -(1 / 10 : ℝ) - p.1 + 1 / 2 ^ 30)
    (h3 : 3 * (p.1 : ℝ) ≤ y) (h4 : y ≤ 3 * (p.2 : ℝ)) :
    (231169/100000 : ℝ) ≤
      gAlpha (1 / 2048) (1 / 1000) cQ mQ (1 / 4) (CatalanCore.Decay.Unu (1 / 4)) ⟨x,y⟩ := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp

  have hs := C.ray_shape b hb
  have ha : (0 : ℝ) ≤ ((rayInterval b).1 : ℚ) := Rat.cast_nonneg.mpr hs.1
  have hx1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    push_cast at hh
    linarith
  have hx2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hs.2.2
    push_cast at hh
    linarith
  have hy1 : (b.1.2.2.1 : ℝ) / 2 ^ 40 ≤ y := by
    dsimp [rayInterval] at h3
    push_cast at h3
    linarith
  have hy2 : y ≤ (b.1.2.2.2 : ℝ) / 2 ^ 40 := by
    dsimp [rayInterval] at h4
    push_cast at h4
    linarith
  have hx : x < 0 := by linarith
  have hy : 0 ≤ y := by linarith
  rw [gAlpha_bridge x y hx hy]
  exact ray_gQuarter C b hb x y hx1 hx2 hy1 hy2

include C in
theorem segment_bound (b : QBox) (hb : b ∈ boxes segs) (x : ℝ)
    (h1 : ((axisInterval b).1 : ℝ) ≤ x) (h2 : x ≤ ((axisInterval b).2 : ℝ)) :
    (gamma b : ℝ) ≤
      gAlpha (1 / 2048) (1 / 1000) cQ mQ (1 / 4) (CatalanCore.Decay.Unu (1 / 4)) ⟨x,0⟩ := by
  have hs := C.seg_shape b hb
  have hx : x ≤ 1 := by
    dsimp [axisInterval] at h2
    push_cast at h2
    have hh : (b.1.2.1 : ℝ) ≤ 0 := by exact_mod_cast hs.2
    linarith
  rw [gAlpha_bridge_axis x hx]
  have h1' : (b.1.1 : ℝ) / 2 ^ 40 ≤ x := by simpa [axisInterval] using h1
  have h2' : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40 := by simpa [axisInterval] using h2
  exact axis_gQuarter segs C.seg_far C.seg_ok b hb x h1' h2'

include C in
theorem line_bound (p : ℚ × ℚ) (hp : p ∈ intervals lines) (x : ℝ)
    (h1 : (p.1 : ℝ) ≤ x) (h2 : x ≤ (p.2 : ℝ)) :
    (-143459/100000 : ℝ) ≤
      gAlpha (1 / 2048) (1 / 1000) cQ mQ (1 / 4) (CatalanCore.Decay.Unu (1 / 4)) ⟨x,0⟩ := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  have hs := C.line_shape b hb
  have hx : x ≤ 1 := by
    dsimp [axisInterval] at h2
    push_cast at h2
    have hh : (b.1.2.1 : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hs.1
    linarith
  rw [gAlpha_bridge_axis x hx]
  have h1' : (b.1.1 : ℝ) / 2 ^ 40 ≤ x := by simpa [axisInterval] using h1
  have h2' : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40 := by simpa [axisInterval] using h2
  have hg : (-143459/100000 : ℝ) ≤ (gamma b : ℝ) := by exact_mod_cast hs.2
  exact hg.trans (axis_gQuarter lines C.line_far C.line_ok b hb x h1' h2')

end CatalanCore.Cert.SigmaQuarter
