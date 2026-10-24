module
public import CatalanArchive.CatalanMeasure.Parametric.U3ChebyshevFrobenius
public import CatalanMeasure.Parametric.CoefficientBounds
public import CatalanMeasure.Parametric.TwentyParameters
@[expose] public section

/-!
# Row form of identity K (Lemma U3)

For every row `r < 20N` of the canonical design, reduced modulo an odd prime
`p` with `8N < p < 9N`, the row polynomials satisfy
`X^(24N) ∣ (1-X^2)^((p+1)/2) * D_r - X * P_r`.
-/

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem reflect_shift {R : Type*} [Semiring R] (f : R[X]) {n : ℕ} (hf : f.natDegree ≤ n)
    (k : ℕ) : reflect (n + k) f = X ^ k * reflect n f := by
  have h := reflect_mul f (1 : R[X]) (F := n) (G := k) hf (by simp)
  rw [mul_one, reflect_one] at h
  rw [h, X_pow_mul]

theorem reflect_pow_two {R : Type*} [CommRing R] (h : ℕ) :
    reflect (2 * h) ((X ^ 2 - 1 : R[X]) ^ h) = (1 - X ^ 2) ^ h := by
  induction h with
  | zero => simp [reflect_one]
  | succ h ih =>
    have hd : ((X ^ 2 - 1 : R[X]) ^ h).natDegree ≤ 2 * h := by
      calc _ ≤ h * (X ^ 2 - 1 : R[X]).natDegree := natDegree_pow_le
        _ ≤ h * 2 := Nat.mul_le_mul_left _ (by compute_degree)
        _ = 2 * h := by ring
    have hd2 : (X ^ 2 - 1 : R[X]).natDegree ≤ 2 := by compute_degree
    have := reflect_mul ((X ^ 2 - 1 : R[X]) ^ h) (X ^ 2 - 1 : R[X]) hd hd2
    have hr2 : reflect 2 (X ^ 2 - 1 : R[X]) = 1 - X ^ 2 := by
      rw [reflect_sub, reflect_monomial, reflect_one]
      simp [revAt_le]
    rw [← pow_succ, show 2 * h + 2 = 2 * (h + 1) by ring] at this
    rw [this, ih, hr2]
    exact (pow_succ _ _).symm

theorem reflect_dvd_of_natDegree_le {R : Type*} [Semiring R] (f : R[X]) {d E : ℕ}
    (hf : f.natDegree ≤ d) (hd : d ≤ E) : X ^ (E - d) ∣ reflect E f := by
  have := reflect_shift f hf (E - d)
  rw [show d + (E - d) = E by omega] at this
  rw [this]
  exact dvd_mul_right _ _

theorem reversedRow_eq_reflect (C : ℕ) (F : ℤ[X]) (hF : F.natDegree < C) :
    reversedRow C F = reflect (C - 1) F := by
  ext i
  rw [reversedRow_coeff, coeff_reflect]
  by_cases hi : i < C
  · simp only [hi, ite_true, revAt_le (show i ≤ C - 1 by omega)]
  · simp only [hi, ite_false, revAt_eq_self_of_lt (show C - 1 < i by omega)]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Reflected form of the Chebyshev Frobenius identity (identity K, one row). -/
theorem chebyshev_reflect_row (hp2 : p ≠ 2) (E : ℕ) (m : ℤ)
    (hU : (Chebyshev.U (ZMod p) (m - 1)).natDegree ≤ E)
    (hT : (Chebyshev.T (ZMod p) m).natDegree ≤ E)
    (hTp : (Chebyshev.T (ZMod p) ((p : ℤ) - m)).natDegree ≤ E) :
    (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * reflect E (Chebyshev.U (ZMod p) (m - 1)) -
        X * reflect E (Chebyshev.T (ZMod p) m) =
      -(X ^ (p + 1) * reflect E (Chebyshev.T (ZMod p) ((p : ℤ) - m))) := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have h2h : 2 * ((p + 1) / 2) = p + 1 := by omega
  have e : (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2) * Chebyshev.U (ZMod p) (m - 1) +
      Chebyshev.T (ZMod p) ((p : ℤ) - m) = X ^ p * Chebyshev.T (ZMod p) m := by
    linear_combination zmod_chebyshev_reflect p hp2 m
  have hdeg1 : ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)).natDegree ≤ p + 1 := by
    calc _ ≤ ((p + 1) / 2) * (X ^ 2 - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
      _ ≤ ((p + 1) / 2) * 2 := Nat.mul_le_mul_left _ (by compute_degree)
      _ = p + 1 := by omega
  have hx : ((X : (ZMod p)[X]) ^ p).natDegree ≤ p := by simp
  have r := congrArg (reflect (p + 1 + E)) e
  rw [reflect_add] at r
  have a1 := reflect_mul ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2))
    (Chebyshev.U (ZMod p) (m - 1)) hdeg1 hU
  have a2 : reflect (p + 1 + E) (Chebyshev.T (ZMod p) ((p : ℤ) - m)) =
      X ^ (p + 1) * reflect E (Chebyshev.T (ZMod p) ((p : ℤ) - m)) := by
    rw [add_comm (p + 1) E]
    exact reflect_shift _ hTp (p + 1)
  have a3 : reflect (p + 1 + E) (X ^ p * Chebyshev.T (ZMod p) m) =
      X * reflect E (Chebyshev.T (ZMod p) m) := by
    rw [Nat.add_assoc, reflect_mul ((X : (ZMod p)[X]) ^ p) (Chebyshev.T (ZMod p) m) hx
      (show (Chebyshev.T (ZMod p) m).natDegree ≤ 1 + E by omega), reflect_monomial,
      revAt_le le_rfl, Nat.sub_self, pow_zero, one_mul, add_comm 1 E,
      reflect_shift _ hT 1, pow_one]
  have a5 : reflect (2 * ((p + 1) / 2)) ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p + 1) / 2)) =
      (1 - X ^ 2) ^ ((p + 1) / 2) := reflect_pow_two _
  rw [h2h] at a5
  rw [a1, a5, a2, a3] at r
  linear_combination r

/-- The signed offset of row `r` in the canonical design. -/
def u3Offset (N r : ℕ) : ℤ := (r : ℤ) - 2 * N

theorem u3Offset_eq (N r : ℕ) : rowOffset twenty N r = u3Offset N r := by
  simp [rowOffset, u3Offset, Parameters.g, twenty]

theorem u3Offset_natAbs_le {N r : ℕ} (hr : r < 20 * N) :
    (u3Offset N r).natAbs ≤ 18 * N - 1 := by
  unfold u3Offset; omega

theorem rowP_map_eq {N : ℕ} (hN : 0 < N) {r : ℕ} (hr : r < 20 * N) :
    (rowP twenty N r).map (Int.castRingHom (ZMod p)) =
      (1 - X) ^ N * reflect (26 * N - 1) (Chebyshev.T (ZMod p) (u3Offset N r)) := by
  have hd : rowDistance twenty N r = (u3Offset N r).natAbs := by
    unfold rowDistance; rw [u3Offset_eq]
  have hC : twenty.C N = 26 * N := twenty_C N
  have hh : twenty.h N = N := by simp [Parameters.h, twenty]
  have hdeg : (Chebyshev.T ℤ (rowDistance twenty N r : ℤ)).natDegree < twenty.C N := by
    rw [Chebyshev.natDegree_T, Int.natAbs_natCast, hd, hC]
    have := u3Offset_natAbs_le hr
    omega
  unfold rowP
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, hh, reversedRow_eq_reflect _ _ hdeg, hC, ← reflect_map,
    Chebyshev.map_T, hd, Chebyshev.T_natAbs]

theorem rowD_map_eq {N : ℕ} (hN : 0 < N) {r : ℕ} (hr : r < 20 * N) :
    (rowD twenty N r).map (Int.castRingHom (ZMod p)) =
      (1 - X) ^ N * reflect (26 * N - 1) (Chebyshev.U (ZMod p) (u3Offset N r - 1)) := by
  have hd : rowDistance twenty N r = (u3Offset N r).natAbs := by
    unfold rowDistance; rw [u3Offset_eq]
  have hC : twenty.C N = 26 * N := twenty_C N
  have hh : twenty.h N = N := by simp [Parameters.h, twenty]
  have hdeg : (Chebyshev.U ℤ ((rowDistance twenty N r : ℤ) - 1)).natDegree <
      twenty.C N := by
    rw [Chebyshev.natDegree_U, hd, hC]
    have := u3Offset_natAbs_le hr
    omega
  unfold rowD
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_C, hh,
    reversedRow_eq_reflect _ _ hdeg, hC, ← reflect_map, Chebyshev.map_U, u3Offset_eq, hd]
  generalize u3Offset N r = m
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hs : Int.sign m = -1 := Int.sign_eq_neg_one_of_neg hm
    have ha : ((m.natAbs : ℕ) : ℤ) = -m := by omega
    have e : Chebyshev.U (ZMod p) (m - 1) = -Chebyshev.U (ZMod p) (-m - 1) := by
      simpa using Chebyshev.U_neg_sub_one (ZMod p) (-m)
    rw [hs, ha, e, reflect_neg]
    simp only [map_neg, map_one]
    ring
  · subst hm
    simp [Chebyshev.U_neg_one]
  · have hs : Int.sign m = 1 := Int.sign_eq_one_of_pos hm
    have ha : ((m.natAbs : ℕ) : ℤ) = m := by omega
    rw [hs, ha]
    simp

/-- Identity K for one row of the canonical design, on the reflected Chebyshev
pieces (character `p`). -/
theorem row_identity_core {N : ℕ} (hN : 0 < N) (hp2 : p ≠ 2) (h8 : 8 * N < p) (h9 : p < 9 * N)
    {r : ℕ} (hr : r < 20 * N) :
    X ^ (24 * N) ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        reflect (26 * N - 1) (Chebyshev.U (ZMod p) (u3Offset N r - 1)) -
      X * reflect (26 * N - 1) (Chebyshev.T (ZMod p) (u3Offset N r)) := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  have hm := u3Offset_natAbs_le hr
  have hm1 : (-(2 * N : ℤ)) ≤ u3Offset N r := by unfold u3Offset; omega
  have hm2 : u3Offset N r ≤ 18 * N - 1 := by unfold u3Offset; omega
  have hU : (Chebyshev.U (ZMod p) (u3Offset N r - 1)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_U]; omega
  have hT : (Chebyshev.T (ZMod p) (u3Offset N r)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_T]; omega
  have hTp : (Chebyshev.T (ZMod p) ((p : ℤ) - u3Offset N r)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_T]; omega
  rw [chebyshev_reflect_row hp2 (26 * N - 1) (u3Offset N r) hU hT hTp]
  have hd : (Chebyshev.T (ZMod p) ((p : ℤ) - u3Offset N r)).natDegree ≤ p + 2 * N := by
    rw [Chebyshev.natDegree_T]; omega
  have hdv := reflect_dvd_of_natDegree_le _ hd (show p + 2 * N ≤ 26 * N - 1 by omega)
  rw [dvd_neg]
  refine (pow_dvd_pow X (show 24 * N ≤ p + 1 + (26 * N - 1 - (p + 2 * N)) by omega)).trans ?_
  rw [pow_add]
  exact mul_dvd_mul (dvd_refl _) hdv

end

end
end CatalanMeasure.Parametric
