module
public import CatalanCore.Cert.QuarterContour.Energy
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LogModel
open Finset Real
/-- Polynomial for log(1+t), with a rigorously bounded remainder. -/
noncomputable def poly (n : ℕ) (t : ℝ) : ℝ := - ∑ i ∈ range n, (-t)^(i+1)/(i+1)

lemma error {t r : ℝ} (ht : |t| ≤ r) (hr : r < 1) (n : ℕ) :
    |Real.log (1+t) - poly n t| ≤ r^(n+1)/(1-r) := by
  have hlt : |t| < 1 := ht.trans_lt hr
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by simpa using hlt) n
  have h1 : |Real.log (1+t) - poly n t| ≤ |t|^(n+1)/(1-|t|) := by
    simpa only [poly, abs_neg, sub_neg_eq_add, add_comm, neg_neg] using h
  apply h1.trans
  have hr0 : 0 ≤ r := (abs_nonneg t).trans ht
  gcongr

lemma relative_error {q q0 r : ℝ} (hq : 0 < q) (h0 : 0 < q0)
    (ht : |(q-q0)/q0| ≤ r) (hr : r < 1) (n : ℕ) :
    |Real.log q - (Real.log q0 + poly n ((q-q0)/q0))| ≤ r^(n+1)/(1-r) := by
  have he : 1+(q-q0)/q0 = q/q0 := by field_simp; ring
  have h := error ht hr n
  rw [he, Real.log_div hq.ne' h0.ne'] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The model bounds the same regularized logarithmic kernel as the certificates. -/
lemma kernel_bounds {q q0 r : ℝ} (hq : 0 < q) (h0 : 0 < q0)
    (ht : |(q-q0)/q0| ≤ r) (hr : r < 1) (n : ℕ) :
    -(Real.log q0 + poly n ((q-q0)/q0) + r^(n+1)/(1-r))/2 ≤ -(Real.log q)/2 ∧
    -(Real.log q)/2 ≤ -(Real.log q0 + poly n ((q-q0)/q0) - r^(n+1)/(1-r))/2 := by
  have h := (abs_le.mp (relative_error hq h0 ht hr n))
  constructor <;> linarith [h.1,h.2]

lemma sum_lower {K : ℕ} (w q q0 r : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i, 0 < q i) (h0 : ∀ i, 0 < q0 i)
    (ht : ∀ i, |(q i-q0 i)/q0 i| ≤ r i) (hr : ∀ i, r i < 1) (n : ℕ) :
    -((∑ i, w i*Real.log (q0 i)) + (∑ i, w i*poly n ((q i-q0 i)/q0 i)) +
      (∑ i, w i*(r i)^(n+1)/(1-r i)))/2 ≤ ∑ i, w i*(-Real.log (q i)/2) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (kernel_bounds (hq i) (h0 i) (ht i) (hr i) n).1 (hw i))
  have he : (∑ i, w i*(-(Real.log (q0 i)+poly n ((q i-q0 i)/q0 i)+(r i)^(n+1)/(1-r i))/2)) =
      -((∑ i, w i*Real.log (q0 i)) + (∑ i, w i*poly n ((q i-q0 i)/q0 i)) +
      (∑ i, w i*(r i)^(n+1)/(1-r i)))/2 := by
    calc
      _ = ∑ i, -(w i*Real.log (q0 i)+w i*poly n ((q i-q0 i)/q0 i)+w i*(r i)^(n+1)/(1-r i))/2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [he] at h
  exact h
end CatalanCore.Cert.QuarterContour.LogModel
#print axioms CatalanCore.Cert.QuarterContour.LogModel.kernel_bounds