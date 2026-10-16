module
public import CatalanMeasure.Parametric.SecondaryTentSourceTrace

/-! Frobenius commutes with the elementary two-sheet trace. -/
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section

theorem secondaryTent_source_trace_frobenius {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (x s A B P Q : K) (h2 : (2:K)≠0) (hx : x≠0) (hs : s≠0)
    (hw : x-1≠0) (hcurve : s^2=x^2-1) :
    (secondaryTentSourceTraceTerm x s A B (P/(2*x)) (Q/(2*x*(x-1))))^p +
      (secondaryTentSourceTraceTerm x (-s) A B (P/(2*x)) (Q/(2*x*(x-1))))^p =
      (((x*B-(x-1)*A)*P+(x*B-(x+1)*A)*Q)/16)^p / x^(6*p) := by
  have ht := secondaryTent_source_natural_trace x s A B P Q h2 hx hs hw hcurve
  have he :
      secondaryTentSourceTraceTerm x s A B (P/(2*x)) (Q/(2*x*(x-1))) +
        secondaryTentSourceTraceTerm x (-s) A B (P/(2*x)) (Q/(2*x*(x-1))) =
      (((x*B-(x-1)*A)*P+(x*B-(x+1)*A)*Q)/16)/x^6 := by
    apply (eq_div_iff (pow_ne_zero 6 hx)).mpr
    simpa only [mul_comm] using ht
  rw [← add_pow_char, he, div_pow, ← pow_mul]

theorem secondaryTent_source_sixteen_frobenius {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [CharP K p] : (16:K)^p=16 := by
  have h2 : (2:K)^p=2 := by
    simpa only [one_add_one_eq_two, one_pow] using add_pow_char (1:K) 1 p
  calc
    (16:K)^p = ((2:K)^4)^p := by norm_num
    _ = ((2:K)^p)^4 := by rw [← pow_mul, ← pow_mul]; congr 1; omega
    _ = 16 := by rw [h2]; norm_num

/-- Two natural numerator channels combine into the single ordinary
source symbol after the actual row's common normalization factor eight. -/
theorem secondaryTent_source_natural_mirror_frobenius {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (x s A B HU HV : K) (h2 : (2:K)≠0) (hx : x≠0) (hs : s≠0)
    (hw : x-1≠0) (hcurve : s^2=x^2-1) :
    8*s*((secondaryTentSourceTraceTerm x s A B (1/(2*x)) 0)^p*HU +
          (secondaryTentSourceTraceTerm x s A B 0 (1/(2*x*(x-1))))^p*HV) +
      8*s*((secondaryTentSourceTraceTerm x (-s) A B (1/(2*x)) 0)^p*HU +
          (secondaryTentSourceTraceTerm x (-s) A B 0 (1/(2*x*(x-1))))^p*HV) =
      8*s*(((x*B-(x-1)*A)^p*HU+(x*B-(x+1)*A)^p*HV)/16)/x^(6*p) := by
  have hP := secondaryTent_source_trace_frobenius x s A B 1 0 h2 hx hs hw hcurve
  have hQ := secondaryTent_source_trace_frobenius x s A B 0 1 h2 hx hs hw hcurve
  simp only [zero_div, mul_one, mul_zero, add_zero, zero_add] at hP hQ
  rw [div_pow, secondaryTent_source_sixteen_frobenius] at hP hQ
  calc
    _ = 8*s*
      (((secondaryTentSourceTraceTerm x s A B (1/(2*x)) 0)^p+
          (secondaryTentSourceTraceTerm x (-s) A B (1/(2*x)) 0)^p)*HU +
       ((secondaryTentSourceTraceTerm x s A B 0 (1/(2*x*(x-1))))^p+
          (secondaryTentSourceTraceTerm x (-s) A B 0 (1/(2*x*(x-1))))^p)*HV) := by ring
    _ = _ := by rw [hP, hQ]; ring

end
end CatalanMeasure.Parametric
