module
public import CatalanCore.Cert.QuarterCompute.ModelDefs
public import CatalanCore.Cert.QuarterContour.LogModelDyadic
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.Polynomial

private lemma errorCeil_real_ge (n d : ℕ) (hd : 0 < d) :
    (n : ℝ)/(d : ℝ) ≤ (((n+d-1)/d : ℕ) : ℝ) := by
  have h := CatalanLambda.Cert.ceil_div_ge n d hd
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast h
lemma errorCeil_bound (S : ℕ) (j : Jet) (hs : ratioNumerator j < S) :
    ((j.2.2 : ℝ)/2^32)/2 *
      (((ratioNumerator j : ℝ)/(S : ℝ))^16+2/(S : ℝ))/(1-(ratioNumerator j : ℝ)/(S : ℝ)) ≤
    (errorCeil S j : ℝ)/2^64 := by
  let r := ratioNumerator j
  let num := j.2.2*2^31*(r^16+2*S^15)
  let den := S^15*(S-r)
  have hSN : 0 < S := by omega
  have hden : 0 < den := Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt hs)
  have h := errorCeil_real_ge num den hden
  change (num : ℝ)/(den : ℝ) ≤ (errorCeil S j : ℝ) at h
  have hSr : 0 < (S : ℝ) := by exact_mod_cast hSN
  have hrS : (r : ℝ) < (S : ℝ) := by exact_mod_cast hs
  have hdiff : 0 < (S : ℝ)-(r : ℝ) := sub_pos.mpr hrS
  have hdc : (den : ℝ) = (S : ℝ)^15*((S : ℝ)-(r : ℝ)) := by
    dsimp [den]
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (Nat.le_of_lt (show r < S from hs))]
  have hnc : (num : ℝ) = (j.2.2 : ℝ)*2^31*((r : ℝ)^16+2*(S : ℝ)^15) := by
    dsimp [num]
    push_cast
    norm_num
  have he : ((j.2.2 : ℝ)/2^32)/2 * (((r : ℝ)/(S : ℝ))^16+2/(S : ℝ))/(1-(r : ℝ)/(S : ℝ)) =
      (num : ℝ)/(den : ℝ)/2^64 := by
    rw [hnc,hdc]
    have hone : 1-(r : ℝ)/(S : ℝ) = ((S : ℝ)-(r : ℝ))/(S : ℝ) := by field_simp [ne_of_gt hSr]
    rw [hone]
    field_simp [ne_of_gt hSr,ne_of_gt hdiff]
  change ((j.2.2 : ℝ)/2^32)/2 * (((r : ℝ)/(S : ℝ))^16+2/(S : ℝ))/(1-(r : ℝ)/(S : ℝ)) ≤ _
  rw [he]
  exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2^64)).mpr h
end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.errorCeil_bound