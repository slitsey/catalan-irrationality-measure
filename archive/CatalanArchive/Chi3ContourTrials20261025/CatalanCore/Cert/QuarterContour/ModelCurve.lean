module
public import CatalanCore.Cert.QuarterContour.ModelInputs
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.Polynomial

lemma validParams_facts (m : Params) (h : validParams m = true) :
    0 < m.U ∧ m.U % 2^40 = 0 ∧ m.U % 2048 = 0 := by
  simpa only [validParams,decide_eq_true_eq] using h

lemma step_cast (m : Params) (h : m.U % 2^40 = 0) :
    (step m : ℝ) = (m.U : ℝ)/2^40 := by
  have hh := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
  apply (eq_div_iff (by positivity : (2 : ℝ)^40 ≠ 0)).mpr
  dsimp [step]
  exact_mod_cast hh

lemma rhoStep_cast (m : Params) (h : m.U % 2048 = 0) :
    ((m.U/2048 : ℕ) : ℝ) = (m.U : ℝ)/2048 := by
  have hh := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
  apply (eq_div_iff (by norm_num : (2048 : ℝ) ≠ 0)).mpr
  exact_mod_cast hh

noncomputable def modelQ (m : Params) (p : Pt) (v : ℝ) : ℝ :=
  ‖modelZ m v-QuarterContour.cpt p‖^2+(1/2048 : ℝ)^2
noncomputable def centreQ (m : Params) (p : Pt) : ℝ := (q0N m p : ℝ)/(m.U : ℝ)^2

lemma modelQ_eq (m : Params) (p : Pt) (v : ℝ) (hm : validParams m = true) :
    modelQ m p v = rawQ m p v/(m.U : ℝ)^2 := by
  obtain ⟨hU,hstep,hrho⟩ := validParams_facts m hm
  have hUr : (m.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hU)
  unfold modelQ
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [modelZ,QuarterContour.cpt,Complex.sub_re,Complex.sub_im]
  unfold rawQ
  rw [step_cast m hstep,rhoStep_cast m hrho]
  field_simp [hUr] <;> ring

lemma modelQ_factor (m : Params) (p : Pt) (v : ℝ) (hm : validParams m = true)
    (hq : q0N m p ≠ 0) : modelQ m p v = centreQ m p*(1+exactT m p v) := by
  rw [modelQ_eq m p v hm,rawQ_factor m p v hq]
  unfold centreQ
  ring
end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.modelQ_eq