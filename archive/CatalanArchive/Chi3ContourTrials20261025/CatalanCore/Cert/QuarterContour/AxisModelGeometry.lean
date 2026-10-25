module
public import CatalanCore.Cert.QuarterCompute.AxisModelCell
public import CatalanCore.Cert.QuarterContour.ModelCurve
public import CatalanCore.Cert.QuarterContour.ModelCell
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.AxisModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval
open CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterContour.DyadicInterval

/-- An axis model is exact at the x-based normalized parameter. -/
theorem axis_modelZ (m : Params) (hU : 0 < m.U) (hDX : 0 < m.DX)
    (hY : m.Y0 = 0) (hD : m.DY = 0) (x : ℝ) :
    modelZ m (((m.U : ℝ)*x-(m.X0 : ℝ))/(m.DX : ℝ)) = (⟨x,0⟩ : ℂ) := by
  have hUr : (m.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hU)
  have hDXr : (m.DX : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hDX)
  apply Complex.ext
  · change ((m.X0 : ℝ)+(m.DX : ℝ)*(((m.U : ℝ)*x-(m.X0 : ℝ))/(m.DX : ℝ)))/(m.U : ℝ) = x
    field_simp [hUr,hDXr] <;> ring
  · change ((m.Y0 : ℝ)+(m.DY : ℝ)*_)/(m.U : ℝ) = 0
    simp only [hY,hD,Int.cast_zero,zero_mul,zero_add,zero_div]

theorem vInterval_contains (m : Params) (hU : 0 < m.U) (hDX : 0 < m.DX)
    (xl xh : ℤ) (x : ℝ) (hx : (xl : ℝ)/2^40 ≤ x ∧ x ≤ (xh : ℝ)/2^40) :
    Contains H (AxisModelCell.vInterval m xl xh) (((m.U : ℝ)*x-m.X0)/m.DX) := by
  exact ModelCell.vInterval_contains (AxisModelCell.carrier m) hU hDX xl xh x hx

theorem abs_le_one_of_range (I : Interval) (hrange : -H ≤ I.1 ∧ I.2 ≤ H)
    (v : ℝ) (hv : Contains H I v) : |v| ≤ 1 := by
  have hp : (0 : ℝ) < H := by norm_num [H]
  have hlo : (-1 : ℝ) ≤ (I.1 : ℝ)/(H : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    norm_num only [neg_mul,one_mul]
    exact_mod_cast hrange.1
  have hhi : (I.2 : ℝ)/(H : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    norm_num only [one_mul]
    exact_mod_cast hrange.2
  exact abs_le.mpr ⟨hlo.trans hv.1,hv.2.trans hhi⟩
end CatalanCore.Cert.QuarterContour.AxisModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.AxisModelGeometry.axis_modelZ
