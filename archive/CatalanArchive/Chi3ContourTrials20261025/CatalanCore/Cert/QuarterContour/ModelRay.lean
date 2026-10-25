module
public import CatalanCore.Cert.QuarterContour.ModelCurve
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Model

/-- The canonical integer affine model parametrizes the fixed quarter ray. -/
theorem ray_modelZ (m : Params) (hU : 0 < m.U) (hdy : 0 < m.DY)
    (hdir : 5*m.DY = -12*m.DX)
    (horigin : 3000*m.X0+1250*m.Y0 = -321*(m.U : ℤ)) (y : ℝ) :
    modelZ m (((m.U : ℝ)*y-(m.Y0 : ℝ))/(m.DY : ℝ)) =
      (⟨-107/1000-(5/12)*y,y⟩ : ℂ) := by
  have hUr : (m.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hU)
  have hDyr : (m.DY : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdy)
  have hdR : 5*(m.DY : ℝ) = -12*(m.DX : ℝ) := by exact_mod_cast hdir
  have hoR : 3000*(m.X0 : ℝ)+1250*(m.Y0 : ℝ) = -321*(m.U : ℝ) := by
    exact_mod_cast horigin
  have hDX : (m.DX : ℝ) = -(5/12)*(m.DY : ℝ) := by linarith only [hdR]
  have hX0 : (m.X0 : ℝ) = -(107/1000)*(m.U : ℝ)-(5/12)*(m.Y0 : ℝ) := by
    linarith only [hoR]
  apply Complex.ext
  · change ((m.X0 : ℝ)+(m.DX : ℝ)*(((m.U : ℝ)*y-(m.Y0 : ℝ))/(m.DY : ℝ)))/(m.U : ℝ) = _
    rw [hDX,hX0]
    field_simp [hUr,hDyr] <;> ring
  · change ((m.Y0 : ℝ)+(m.DY : ℝ)*(((m.U : ℝ)*y-(m.Y0 : ℝ))/(m.DY : ℝ)))/(m.U : ℝ) = y
    field_simp [hUr,hDyr] <;> ring

/-- The horizontal quarter-ray displacement is exactly the tube radius. -/
theorem ray_tube_distance (m : Params) (hU : 0 < m.U) (hdy : 0 < m.DY)
    (hdir : 5*m.DY = -12*m.DX)
    (horigin : 3000*m.X0+1250*m.Y0 = -321*(m.U : ℤ)) (u delta : ℝ) :
    ‖(⟨-107/1000-u+delta,(12/5)*u⟩ : ℂ) -
      modelZ m (((m.U : ℝ)*((12/5)*u)-(m.Y0 : ℝ))/(m.DY : ℝ))‖ = |delta| := by
  rw [ray_modelZ m hU hdy hdir horigin]
  have he : (⟨-107/1000-u+delta,(12/5)*u⟩ : ℂ) -
      (⟨-107/1000-(5/12)*((12/5)*u),(12/5)*u⟩ : ℂ) = (delta : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs]
end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.ray_tube_distance
