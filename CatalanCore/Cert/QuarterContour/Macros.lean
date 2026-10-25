module
public import CatalanCore.Cert.QuarterContour.Box
public import CatalanCore.Cert.SigmaQuarter.Macros
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def rayOK (epsilon : ℚ) (pts : List Pt) (mp : ℚ) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b => decide (boxGeom b) &&
    decide (mp ≤ quarterBoxLB epsilon (macroLB pts m b.1) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2
      b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2))

theorem rayMacro_sound (epsilon : ℚ) (he : epsilon ≤ 1 / 1000)
    (pts : List Pt) (mp : ℚ) (m : Macro) (hf : farOK pts m)
    (hc : rayOK epsilon pts mp m = true) (b : QBox) (hb : b ∈ m.boxes)
    (x y : ℝ) (h1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40) (h3 : (b.1.2.2.1 : ℝ) / 2 ^ 40 ≤ y)
    (h4 : y ≤ (b.1.2.2.2 : ℝ) / 2 ^ 40) :
    (mp : ℝ) ≤ QuarterContour.gQuarter epsilon pts x y := by
  simp only [rayOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hi, hc⟩ := hc
  obtain ⟨hg, hm⟩ := hc b hb
  rcases hg with ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10⟩
  have hs := QuarterContour.quarterBox_sound epsilon he pts (macroLB pts m b.1)
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2
    g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 x y h1 h2 h3 h4
    (macroLB_sound pts m hf hi b.1 x y h1 h2 h3 h4)
  exact (Rat.cast_le.mpr hm).trans hs

/-- Axis checks are independent of epsilon, so reuse their original proof. -/
theorem axisMacro_sound (epsilon : ℚ) (pts : List Pt) (m : Macro) (hf : farOK pts m)
    (hc : axisOK pts m = true) (b : QBox) (hb : b ∈ m.boxes)
    (x : ℝ) (h1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40) :
    ((b.2.2.2.1 : ℚ) / 2 ^ 32 : ℝ) ≤ QuarterContour.gQuarter epsilon pts x 0 := by
  rw [gQuarter_eq]
  simpa using SigmaQuarter.axisMacro_sound pts m hf hc b hb x h1 h2
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.rayMacro_sound
#print axioms CatalanCore.Cert.QuarterContour.axisMacro_sound
