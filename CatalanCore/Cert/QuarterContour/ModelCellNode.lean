module
public import CatalanCore.Cert.QuarterCompute.ModelCell
public import CatalanCore.Cert.QuarterContour.Macros
public import CatalanCore.Cert.QuarterContour.DyadicInterval
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelCellNode
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def nodeOK (epsilon mp : ℚ) (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (b : QBox) : Bool :=
  decide (boxGeom b) &&
  decide (-H ≤ (vInterval p b.1.2.2.1 b.1.2.2.2).1 ∧ (vInterval p b.1.2.2.1 b.1.2.2.2).2 ≤ H) &&
  decide (mp ≤ QuarterContour.quarterBoxLB epsilon
    ((sigmaLower p cs denom base error b.1.2.2.1 b.1.2.2.2 : ℤ)/(2^48 : ℚ))
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2)

theorem range_of_nodeOK (epsilon mp : ℚ) (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (b : QBox)
    (hc : nodeOK epsilon mp p cs denom base error b = true) :
    -H ≤ (vInterval p b.1.2.2.1 b.1.2.2.2).1 ∧ (vInterval p b.1.2.2.1 b.1.2.2.2).2 ≤ H := by
  simp only [nodeOK,Bool.and_eq_true,decide_eq_true_eq] at hc
  exact hc.1.2

theorem abs_le_one_of_nodeOK (epsilon mp : ℚ) (p : CatalanCore.Cert.QuarterCompute.Model.Params)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (b : QBox)
    (hc : nodeOK epsilon mp p cs denom base error b = true) (v : ℝ)
    (hv : DyadicInterval.Contains H (vInterval p b.1.2.2.1 b.1.2.2.2) v) : |v| ≤ 1 := by
  have hr := range_of_nodeOK epsilon mp p cs denom base error b hc
  have hp : (0 : ℝ) < H := by norm_num [H]
  have hlo : (-1 : ℝ) ≤ ((vInterval p b.1.2.2.1 b.1.2.2.2).1 : ℝ)/(H : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    norm_num only [neg_mul,one_mul]
    exact_mod_cast hr.1
  have hhi : ((vInterval p b.1.2.2.1 b.1.2.2.2).2 : ℝ)/(H : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    norm_num only [one_mul]
    exact_mod_cast hr.2
  exact abs_le.mpr ⟨hlo.trans hv.1,hv.2.trans hhi⟩

/-- The old verified node arithmetic consumes only the new sigma lower bound. -/
theorem node_sound (epsilon mp : ℚ) (hepsilon : epsilon ≤ 1/1000)
    (p : CatalanCore.Cert.QuarterCompute.Model.Params) (pts : List Pt)
    (cs : List ℤ) (denom : ℕ) (base : ℤ) (error : ℕ) (b : QBox)
    (hc : nodeOK epsilon mp p cs denom base error b = true)
    (x y : ℝ) (hx1 : (b.1.1 : ℝ)/2^40 ≤ x) (hx2 : x ≤ (b.1.2.1 : ℝ)/2^40)
    (hy1 : (b.1.2.2.1 : ℝ)/2^40 ≤ y) (hy2 : y ≤ (b.1.2.2.2 : ℝ)/2^40)
    (hS : (sigmaLower p cs denom base error b.1.2.2.1 b.1.2.2.2 : ℝ)/(H : ℝ) ≤ SigmaP6.Usig pts x y) :
    (mp : ℝ) ≤ QuarterContour.gQuarter epsilon pts x y := by
  simp only [nodeOK,Bool.and_eq_true,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hg,hrange⟩,hm⟩
  have hs : ((((sigmaLower p cs denom base error b.1.2.2.1 b.1.2.2.2 : ℤ)/(2^48 : ℚ)) : ℚ) : ℝ)
      ≤ SigmaP6.Usig pts x y := by
    push_cast
    norm_num [H] at hS ⊢
    exact hS
  rcases hg with ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10⟩
  have hb := QuarterContour.quarterBox_sound epsilon hepsilon pts _
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2
    g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 x y hx1 hx2 hy1 hy2 hs
  exact (Rat.cast_le.mpr hm).trans hb
end CatalanCore.Cert.QuarterContour.ModelCellNode
#print axioms CatalanCore.Cert.QuarterContour.ModelCellNode.node_sound