module
public import CatalanCore.Cert.QuarterContour.LogModelTube
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LogModel
lemma log_variation {x y c d : ℝ} (hx : 0 < x) (hy : 0 < y) (hc : 0 < c)
    (hxc : c ≤ x) (hyc : c ≤ y) (hxy : |x-y| ≤ d) :
    |Real.log x-Real.log y| ≤ d/c := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hxy
  have one_side : ∀ a b : ℝ, 0 < a → 0 < b → c ≤ b → a-b ≤ d →
      Real.log a-Real.log b ≤ d/c := by
    intro a b ha hb hcb hab
    have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at h
    have he : a/b-1 = (a-b)/b := by field_simp
    rw [he] at h
    exact h.trans (((div_le_div_iff_of_pos_right hb).mpr hab).trans
      (div_le_div_of_nonneg_left hd hc hcb))
  apply abs_le.mpr
  constructor
  · have h := one_side y x hy hx hxc (by linarith [(abs_le.mp hxy).1])
    linarith
  · exact one_side x y hx hy hyc (abs_le.mp hxy).2

/-- A dyadic approximation of the normalized coefficients needs only a small explicit error. -/
lemma rounded_error {t t' r d : ℝ} (ht : |t| ≤ r) (ht' : |t'| ≤ r)
    (hr : r < 1) (hd : |t-t'| ≤ d) (n : ℕ) :
    |Real.log (1+t)-poly n t'| ≤ (r^(n+1)+d)/(1-r) := by
  have hc : 0 < 1-r := by linarith
  have hx : 0 < 1+t := by linarith [(abs_le.mp ht).1]
  have hy : 0 < 1+t' := by linarith [(abs_le.mp ht').1]
  have h1 := log_variation hx hy hc (by linarith [(abs_le.mp ht).1])
    (by linarith [(abs_le.mp ht').1]) (by simpa only [add_sub_add_left_eq_sub] using hd)
  have h2 := error ht' hr n
  calc
    _ ≤ |Real.log (1+t)-Real.log (1+t')|+|Real.log (1+t')-poly n t'| := abs_sub_le _ _ _
    _ ≤ d/(1-r)+r^(n+1)/(1-r) := add_le_add h1 h2
    _ = _ := by ring
end CatalanCore.Cert.QuarterContour.LogModel
#print axioms CatalanCore.Cert.QuarterContour.LogModel.rounded_error