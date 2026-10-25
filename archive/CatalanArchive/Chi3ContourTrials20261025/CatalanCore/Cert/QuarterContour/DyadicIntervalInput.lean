module
public import CatalanCore.Cert.QuarterCompute.DyadicIntervalInput
public import CatalanCore.Cert.QuarterContour.DyadicInterval
public import CatalanCore.Cert.QuarterContour.RealPolynomial
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.DyadicInterval
open CatalanCore.Cert.QuarterCompute.DyadicInterval

lemma evalReal_map_div (x d : ℝ) (cs : List ℝ) :
    evalReal x (cs.map (fun c => c/d)) = evalReal x cs/d := by
  induction cs with
  | nil => simp [evalReal]
  | cons c cs ih => simp only [List.map_cons,evalReal,ih]; ring

lemma evalReal_cast (x : ℝ) (cs : List ℤ) :
    evalReal x (cs.map (fun c : ℤ => (c : ℝ))) = RealPolynomial.evalReal x cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons,evalReal,RealPolynomial.evalReal,ih]

lemma coefficients_sound_normalized (H d : ℤ) (hH : 0 < H) (hd : 0 < d) (cs : List ℤ)
    (v : Interval) (x : ℝ) (hx : Contains H v x) :
    Contains H (horner H (coefficients H d cs) v) (RealPolynomial.evalReal x cs/(d : ℝ)) := by
  induction cs with
  | nil => simp [coefficients,horner,RealPolynomial.evalReal,Contains]
  | cons c cs ih =>
    have hc := encloseRatio_sound H c d hH hd
    have ht := mul_sound H hH v (horner H (coefficients H d cs) v) x
      (RealPolynomial.evalReal x cs/(d : ℝ)) hx ih
    have h := add_sound H (encloseRatio H c d) (mul H v (horner H (coefficients H d cs) v))
      ((c : ℝ)/d) (x*(RealPolynomial.evalReal x cs/(d : ℝ))) hc ht
    change Contains H (add (encloseRatio H c d) (mul H v (horner H (coefficients H d cs) v)))
      (((c : ℝ)+x*RealPolynomial.evalReal x cs)/(d : ℝ))
    have he : ((c : ℝ)+x*RealPolynomial.evalReal x cs)/(d : ℝ) =
        (c : ℝ)/d+x*(RealPolynomial.evalReal x cs/(d : ℝ)) := by ring
    rw [he]
    exact h
lemma encloseFractions_sound (H lo hi d : ℤ) (hH : 0 < H) (hd : 0 < d) (x : ℝ)
    (hx : (lo : ℝ)/d ≤ x ∧ x ≤ (hi : ℝ)/d) : Contains H (encloseFractions H lo hi d) x := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo := (encloseRatio_sound H lo d hH hd).1
  have hint : hi*H ≤ ceilDiv (hi*H) d*d := by
    have h := Int.ediv_mul_le (-(hi*H)) (ne_of_gt hd)
    unfold ceilDiv
    nlinarith only [h]
  have hreal : (hi : ℝ)*H ≤ (ceilDiv (hi*H) d : ℝ)*d := by exact_mod_cast hint
  have hhi : (hi : ℝ)/d ≤ (ceilDiv (hi*H) d : ℝ)/H := (div_le_div_iff₀ hdp hp).mpr hreal
  exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩
end CatalanCore.Cert.QuarterContour.DyadicInterval
#print axioms CatalanCore.Cert.QuarterContour.DyadicInterval.coefficients_sound_normalized
#print axioms CatalanCore.Cert.QuarterContour.DyadicInterval.encloseFractions_sound