module
public import CatalanCore.Cert.QuarterCompute.ModelDefs
public import CatalanCore.Cert.QuarterContour.LogModelDyadic
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.Model

lemma floor_error (S q A a : ℝ) (hS : 0 < S) (hq : 0 < q)
    (hl : a*q ≤ S*A) (hu : S*A < (a+1)*q) :
    |A/q-a/S| ≤ 1/S := by
  have h1 : a/S ≤ A/q := (div_le_div_iff₀ hS hq).mpr (by simpa only [mul_comm S A] using hl)
  have h2 : A/q < (a+1)/S := (div_lt_div_iff₀ hq hS).mpr (by simpa only [mul_comm S A] using hu)
  have hp : 0 ≤ 1/S := le_of_lt (one_div_pos.mpr hS)
  apply abs_le.mpr
  constructor
  · linarith
  · rw [add_div] at h2; linarith

lemma rounded_ratio_bounds (a b ar br S v : ℝ) (hS : 0 < S)
    (ha : |a-ar/S| ≤ 1/S) (hb : |b-br/S| ≤ 1/S) (hv : |v| ≤ 1) :
    |(a*v+b*v^2)-((ar*v+br*v^2)/S)| ≤ 2/S ∧
    |a*v+b*v^2| ≤ (|ar|+|br|+2)/S ∧
    |(ar*v+br*v^2)/S| ≤ (|ar|+|br|+2)/S := by
  have hta := LogModel.ratio_bound ar br v hv
  have hs : 0 ≤ 1/S := le_of_lt (one_div_pos.mpr hS)
  have hd : |(a-ar/S)*v+(b-br/S)*v^2| ≤ 2/S := by
    have hsum := add_le_add ha hb
    have he : 1/S+1/S = 2/S := by ring
    rw [he] at hsum
    exact (LogModel.ratio_bound (a-ar/S) (b-br/S) v hv).trans hsum
  have he : a*v+b*v^2-(ar*v+br*v^2)/S = (a-ar/S)*v+(b-br/S)*v^2 := by ring
  have hd' : |a*v+b*v^2-(ar*v+br*v^2)/S| ≤ 2/S := by rw [he];exact hd
  have ht : |(ar*v+br*v^2)/S| ≤ (|ar|+|br|)/S := by
    rw [abs_div,abs_of_pos hS]
    exact (div_le_div_iff_of_pos_right hS).mpr hta
  refine ⟨hd', ?_, ?_⟩
  · have htri := abs_sub_le (a*v+b*v^2) ((ar*v+br*v^2)/S) 0
    simp only [sub_zero] at htri
    rw [add_div]
    linarith
  · exact ht.trans ((div_le_div_iff_of_pos_right hS).mpr (by linarith))
end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.rounded_ratio_bounds