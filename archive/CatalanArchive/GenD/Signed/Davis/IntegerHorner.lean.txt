module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/IntegerHorner.lean
Original SHA256: 01797a911dee806321a552c0a0b89d144c7ae350cfb12d6e761120cd0ed8a430
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.PolynomialData

@[expose] public section

/-! Integer homogeneous Horner evaluation avoids rational gcd normalization
inside the kernel when checking the signs of large fixed polynomials. -/

namespace CatalanMeasure.Refinement

def homogeneousHorner : List ℤ → ℤ → ℤ → ℤ
  | [], _, _ => 0
  | a :: as, n, d => a * d ^ (as.length + 1) + n * homogeneousHorner as n d

theorem homogeneousHorner_eq (as : List ℤ) (n d D : ℤ) (hd : d ≠ 0) (hD : D ≠ 0) :
    (D : ℚ) * (d : ℚ) ^ as.length *
        rationalHorner (as.map (fun a : ℤ => (a : ℚ) / (D : ℚ))) ((n : ℚ) / (d : ℚ)) =
      (homogeneousHorner as n d : ℚ) := by
  induction as with
  | nil => simp [rationalHorner, homogeneousHorner]
  | cons a as ih =>
    simp only [List.length_cons, List.map_cons, rationalHorner, homogeneousHorner,
      Int.cast_add, Int.cast_mul, Int.cast_pow]
    rw [← ih]
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    simp only [pow_succ]
    field_simp

theorem homogeneousHorner_at_rat (as : List ℤ) (D : ℤ) (hD : D ≠ 0) (x : ℚ) :
    ((D * (x.den : ℤ) ^ as.length : ℤ) : ℚ) *
        rationalHorner (as.map (fun a : ℤ => (a : ℚ) / (D : ℚ))) x =
      (homogeneousHorner as x.num (x.den : ℤ) : ℚ) := by
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Rat.num_div_den] using
    homogeneousHorner_eq as x.num (x.den : ℤ) D (by exact_mod_cast x.den_ne_zero) hD

theorem rationalHorner_lt_of_homogeneous (as : List ℤ) (D : ℤ) (hD : 0 < D)
    (x : ℚ) (k : ℤ)
    (h : homogeneousHorner as x.num (x.den : ℤ) < k * (D * (x.den : ℤ) ^ as.length)) :
    rationalHorner (as.map (fun a : ℤ => (a : ℚ) / (D : ℚ))) x < (k : ℚ) := by
  have hs : (0 : ℚ) < ((D * (x.den : ℤ) ^ as.length : ℤ) : ℚ) := by
    have hxD : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
    exact_mod_cast mul_pos hD (pow_pos hxD _)
  have he := homogeneousHorner_at_rat as D hD.ne' x
  have hQ : (homogeneousHorner as x.num (x.den : ℤ) : ℚ) <
      (k : ℚ) * ((D * (x.den : ℤ) ^ as.length : ℤ) : ℚ) := by exact_mod_cast h
  rw [← he, mul_comm (k : ℚ)] at hQ
  exact (mul_lt_mul_iff_right₀ hs).mp hQ

theorem lt_rationalHorner_of_homogeneous (as : List ℤ) (D : ℤ) (hD : 0 < D)
    (x : ℚ) (k : ℤ)
    (h : k * (D * (x.den : ℤ) ^ as.length) < homogeneousHorner as x.num (x.den : ℤ)) :
    (k : ℚ) < rationalHorner (as.map (fun a : ℤ => (a : ℚ) / (D : ℚ))) x := by
  have hs : (0 : ℚ) < ((D * (x.den : ℤ) ^ as.length : ℤ) : ℚ) := by
    have hxD : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
    exact_mod_cast mul_pos hD (pow_pos hxD _)
  have he := homogeneousHorner_at_rat as D hD.ne' x
  have hQ : (k : ℚ) * ((D * (x.den : ℤ) ^ as.length : ℤ) : ℚ) <
      (homogeneousHorner as x.num (x.den : ℤ) : ℚ) := by exact_mod_cast h
  rw [← he, mul_comm (k : ℚ)] at hQ
  exact (mul_lt_mul_iff_right₀ hs).mp hQ

end CatalanMeasure.Refinement

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.homogeneousHorner
#print axioms CatalanMeasure.Refinement.homogeneousHorner_eq
#print axioms CatalanMeasure.Refinement.homogeneousHorner_at_rat
#print axioms CatalanMeasure.Refinement.rationalHorner_lt_of_homogeneous
#print axioms CatalanMeasure.Refinement.lt_rationalHorner_of_homogeneous
