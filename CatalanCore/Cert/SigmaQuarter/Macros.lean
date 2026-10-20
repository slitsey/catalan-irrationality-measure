module

public import CatalanCore.Cert.SigmaQuarter.Box

@[expose] public section

namespace CatalanCore.Cert.SigmaQuarter

open CatalanCore.Cert.SigmaP6

abbrev Quad := ℤ × ℤ × ℤ × ℤ
abbrev QBox := Quad × Quad

structure Macro where
  x0 : ℤ
  y0 : ℤ
  i0 : ℕ
  i1 : ℕ
  fd : FD
  boxes : List QBox

def macroFar (pts : List Pt) (m : Macro) : List Pt := pts.take m.i0 ++ pts.drop m.i1
def macroNear (pts : List Pt) (m : Macro) : List Pt := (pts.drop m.i0).take (m.i1 - m.i0)
def farOK (pts : List Pt) (m : Macro) : Prop := farSum m.x0 m.y0 (macroFar pts m) = m.fd

instance (pts : List Pt) (m : Macro) : Decidable (farOK pts m) := by
  unfold farOK
  infer_instance

def macroLB (pts : List Pt) (m : Macro) (b : Quad) : ℚ :=
  sigTL m.x0 m.y0 m.fd b.1 b.2.1 b.2.2.1 b.2.2.2
    (sigSum b.1 b.2.1 b.2.2.1 b.2.2.2 (macroNear pts m))

theorem macroLB_sound (pts : List Pt) (m : Macro) (hf : farOK pts m) (hi : m.i0 ≤ m.i1)
    (b : Quad) (x y : ℝ) (h1 : (b.1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ (b.2.1 : ℝ) / 2 ^ 40) (h3 : (b.2.2.1 : ℝ) / 2 ^ 40 ≤ y)
    (h4 : y ≤ (b.2.2.2 : ℝ) / 2 ^ 40) :
    (macroLB pts m b : ℝ) ≤ Usig pts x y := by
  have hs := sigTL_sound m.x0 m.y0 (pts.take m.i0) (macroNear pts m) (pts.drop m.i1)
    b.1 b.2.1 b.2.2.1 b.2.2.2 x y h1 h2 h3 h4
  have he := split_eq pts m.i0 m.i1 hi
  change pts.take m.i0 ++ macroNear pts m ++ pts.drop m.i1 = pts at he
  rw [he] at hs
  change farSum m.x0 m.y0 (pts.take m.i0 ++ pts.drop m.i1) = m.fd at hf
  rw [hf] at hs
  exact hs

def boxGeom (b : QBox) : Prop :=
  b.1.2.1 < 0 ∧ b.1.1 ≤ b.1.2.1 ∧ 0 ≤ b.1.2.2.1 ∧
  b.2.2.1 < 0 ∧ b.2.1 ≤ b.2.2.1 ∧ 0 ≤ b.2.2.2.1 ∧
  (b.2.1 : ℚ) ≤ 2 * b.1.1 / 3 ∧ 2 * (b.1.2.1 : ℚ) / 3 ≤ b.2.2.1 ∧
  (b.2.2.2.1 : ℚ) ≤ 2 * b.1.2.2.1 / 3 ∧ 2 * (b.1.2.2.2 : ℚ) / 3 ≤ b.2.2.2.2

instance (b : QBox) : Decidable (boxGeom b) := by unfold boxGeom; infer_instance

def rayOK (pts : List Pt) (mp : ℚ) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b => decide (boxGeom b) &&
    decide (mp ≤ quarterBoxLB (macroLB pts m b.1) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2
      b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2))

theorem rayMacro_sound (pts : List Pt) (mp : ℚ) (m : Macro) (hf : farOK pts m)
    (hc : rayOK pts mp m = true) (b : QBox) (hb : b ∈ m.boxes)
    (x y : ℝ) (h1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40) (h3 : (b.1.2.2.1 : ℝ) / 2 ^ 40 ≤ y)
    (h4 : y ≤ (b.1.2.2.2 : ℝ) / 2 ^ 40) : (mp : ℝ) ≤ gQuarter pts x y := by
  simp only [rayOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hi, hc⟩ := hc
  obtain ⟨hg, hm⟩ := hc b hb
  rcases hg with ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10⟩
  have hs := quarterBox_sound pts (macroLB pts m b.1) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2
    b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 x y h1 h2 h3 h4
    (macroLB_sound pts m hf hi b.1 x y h1 h2 h3 h4)
  exact (Rat.cast_le.mpr hm).trans hs

def axisUt (a b : ℤ) : ℚ := if b ≤ 0 then utA a b else utB a b

def axisDomain (a b : ℤ) : Prop :=
  a ≤ b ∧ ((-(2 ^ 40 : ℤ) ≤ a ∧ b ≤ 0) ∨ (0 ≤ a ∧ b ≤ 2 ^ 40))

instance (a b : ℤ) : Decidable (axisDomain a b) := by unfold axisDomain; infer_instance

theorem axisUt_sound (a b : ℤ) (hd : axisDomain a b) (x : ℝ)
    (h1 : (a : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ (b : ℝ) / 2 ^ 40) :
    Utau x 0 ≤ (axisUt a b : ℝ) := by
  unfold axisUt
  split_ifs with hb
  · have ha : -(2 ^ 40 : ℤ) ≤ a := by
      rcases hd.2 with h | h
      · exact h.1
      · omega
    exact utA_sound a b hb ha hd.1 x h1 h2
  · have ha : 0 ≤ a := by
      rcases hd.2 with h | h
      · omega
      · exact h.1
    have hh : b ≤ 2 ^ 40 := by
      rcases hd.2 with h | h
      · omega
      · exact h.2
    exact utB_sound a b ha hd.1 hh x h1 h2

def axisGeom (b : QBox) : Prop :=
  axisDomain b.1.1 b.1.2.1 ∧ axisDomain b.2.1 b.2.2.1 ∧
  b.1.2.2.1 = 0 ∧ b.1.2.2.2 = 0 ∧
  (b.2.1 : ℚ) ≤ 2 * b.1.1 / 3 ∧ 2 * (b.1.2.1 : ℚ) / 3 ≤ b.2.2.1

instance (b : QBox) : Decidable (axisGeom b) := by unfold axisGeom; infer_instance

def axisOK (pts : List Pt) (m : Macro) : Bool :=
  decide (m.i0 ≤ m.i1) && m.boxes.all (fun b => decide (axisGeom b) &&
    decide ((b.2.2.2.1 : ℚ) / 2 ^ 32 ≤ quarterAxisLB (macroLB pts m b.1)
      (axisUt b.1.1 b.1.2.1) (axisUt b.2.1 b.2.2.1)))

theorem axisMacro_sound (pts : List Pt) (m : Macro) (hf : farOK pts m)
    (hc : axisOK pts m = true) (b : QBox) (hb : b ∈ m.boxes)
    (x : ℝ) (h1 : (b.1.1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ (b.1.2.1 : ℝ) / 2 ^ 40) :
    ((b.2.2.2.1 : ℚ) / 2 ^ 32 : ℝ) ≤ gQuarter pts x 0 := by
  simp only [axisOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hi, hc⟩ := hc
  obtain ⟨hg, hm⟩ := hc b hb
  rcases hg with ⟨hd1,hd2,hy1,hy2,hl,hh⟩
  have hlr : (b.2.1 : ℝ) ≤ 2 * b.1.1 / 3 := by exact_mod_cast hl
  have hhr : 2 * (b.1.2.1 : ℝ) / 3 ≤ b.2.2.1 := by exact_mod_cast hh
  have hS := macroLB_sound pts m hf hi b.1 x 0 h1 h2 (by simp [hy1]) (by simp [hy2])
  have hs := quarterAxis_sound pts (macroLB pts m b.1)
    (axisUt b.1.1 b.1.2.1) (axisUt b.2.1 b.2.2.1) x hS
    (axisUt_sound _ _ hd1 x h1 h2)
    (axisUt_sound _ _ hd2 (2 * x / 3) (by linarith) (by linarith))
  have he := (Rat.cast_le.mpr hm).trans hs
  push_cast at he
  exact he

end CatalanCore.Cert.SigmaQuarter
