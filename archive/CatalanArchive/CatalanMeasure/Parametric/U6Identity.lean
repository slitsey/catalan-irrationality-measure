module
public import CatalanArchive.CatalanMeasure.Parametric.U6Chebyshev
public import CatalanArchive.CatalanMeasure.Parametric.U3Digits
@[expose] public section

/-!
# Identity K6 on row combinations (Lemma U6)

For a prime `p ≥ 4N`, a row combination `c` of the canonical design satisfies
`X^(24N) ∣ 2 X W S_c - (2 - X^(2p)) U_c`, with `W = (1-X^2)^((p-1)/2)`,
`S_c = u3S p N c`, `U_c = u3U p N c`.
-/

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

section
variable {p N : ℕ} [hp : Fact p.Prime]

theorem reflect_K6_left (hp2 : p ≠ 2) :
    reflect (2 * p) (2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)) =
      2 * X * oddPrimeWeight p := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hp1 := hp.out.one_le
  obtain ⟨h', hh⟩ : ∃ h', h' = (p - 1) / 2 := ⟨_, rfl⟩
  have hph : p = 2 * h' + 1 := by omega
  rw [← hh]
  have hZ : ((X ^ 2 - 1 : (ZMod p)[X]) ^ h').natDegree ≤ 2 * h' := by
    calc _ ≤ h' * (X ^ 2 - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
      _ ≤ h' * 2 := Nat.mul_le_mul_left _ (by compute_degree)
      _ = 2 * h' := by ring
  have hX : ((X : (ZMod p)[X]) ^ p).natDegree ≤ p := by simp
  have e1 : (2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h') =
      C 2 * (X ^ p * (X ^ 2 - 1) ^ h') := by
    rw [C_ofNat]; ring
  have e2 : reflect (p + 2 * h') (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h') =
      (1 - X ^ 2) ^ h' := by
    rw [reflect_mul _ _ hX hZ, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero,
      reflect_pow_two, one_mul]
  have e3 : reflect (2 * p) (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h') =
      X * (1 - X ^ 2) ^ h' := by
    have hd : (X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ h').natDegree ≤ p + 2 * h' :=
      natDegree_mul_le.trans (Nat.add_le_add hX hZ)
    have := reflect_shift _ hd 1
    rw [show 2 * p = p + 2 * h' + 1 by omega, this, e2, pow_one]
  rw [e1, reflect_C_mul, e3, oddPrimeWeight, ← hh]
  rw [C_ofNat]; ring

theorem reflect_K6_right :
    reflect (2 * p) (2 * X ^ (2 * p) - 1 : (ZMod p)[X]) = 2 - X ^ (2 * p) := by
  have e : (2 * X ^ (2 * p) - 1 : (ZMod p)[X]) = C 2 * X ^ (2 * p) - 1 := by
    rw [C_ofNat]
  rw [e, reflect_sub, reflect_C_mul_X_pow, reflect_one, revAt_le le_rfl, Nat.sub_self, pow_zero,
    mul_one, C_ofNat]


/-- Identity K6 for one row of the canonical design (`4N ≤ p`). -/
theorem row_identity_K6 (hN : 0 < N) (hp2 : p ≠ 2) (h4 : 4 * N ≤ p)
    {r : ℕ} (hr : r < 20 * N) :
    X ^ (24 * N) ∣ 2 * X * oddPrimeWeight p * u3Sv p N r - (2 - X ^ (2 * p)) * u3Uv p N r := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  have hm := u3Offset_natAbs_le hr
  have hm1 : (-(2 * N : ℤ)) ≤ u3Offset N r := by unfold u3Offset; omega
  have hm2 : u3Offset N r ≤ 18 * N - 1 := by unfold u3Offset; omega
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hU : (Chebyshev.U (ZMod p) (u3Offset N r - 1)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_U]; omega
  have hT : (Chebyshev.T (ZMod p) (u3Offset N r)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_T]; omega
  have hA : (2 * X ^ p * (X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).natDegree ≤ 2 * p := by
    have hZ : ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).natDegree ≤ p - 1 := by
      calc _ ≤ ((p - 1) / 2) * (X ^ 2 - 1 : (ZMod p)[X]).natDegree := natDegree_pow_le
        _ ≤ ((p - 1) / 2) * 2 := Nat.mul_le_mul_left _ (by compute_degree)
        _ ≤ p - 1 := by omega
    have hX : (2 * (X : (ZMod p)[X]) ^ p).natDegree ≤ p := by
      refine (natDegree_mul_le).trans ?_
      have : (2 : (ZMod p)[X]).natDegree = 0 := by
        rw [← C_ofNat]; exact natDegree_C _
      simp
    calc _ ≤ _ := natDegree_mul_le
      _ ≤ p + (p - 1) := Nat.add_le_add hX hZ
      _ ≤ 2 * p := by omega
  have hB : (2 * X ^ (2 * p) - 1 : (ZMod p)[X]).natDegree ≤ 2 * p := by
    rw [← C_ofNat]
    compute_degree
  have key := congrArg (reflect (2 * p + (26 * N - 1))) (zmod_chebyshev_K6 p hp2 (u3Offset N r))
  rw [reflect_sub, reflect_mul _ _ hA hT, reflect_mul _ _ hB hU, reflect_K6_left hp2,
    reflect_K6_right] at key
  have hd : (Chebyshev.U (ZMod p) (2 * (p : ℤ) - u3Offset N r - 1)).natDegree ≤
      2 * p + 2 * N - 1 := by
    rw [Chebyshev.natDegree_U]; omega
  have hdv := reflect_dvd_of_natDegree_le _ hd (show 2 * p + 2 * N - 1 ≤ 2 * p + (26 * N - 1)
    by omega)
  rw [← key] at hdv
  refine (pow_dvd_pow X (show 24 * N ≤ 2 * p + (26 * N - 1) - (2 * p + 2 * N - 1) by omega)).trans ?_
  unfold u3Sv u3Uv
  exact hdv


/-- Identity K6 for any row combination. -/
theorem comb_identity_K6 (hN : 0 < N) (hp2 : p ≠ 2) (h4 : 4 * N ≤ p)
    (c : Fin (20 * N) → ZMod p) :
    X ^ (24 * N) ∣ 2 * X * oddPrimeWeight p * u3S p N c - (2 - X ^ (2 * p)) * u3U p N c := by
  have h : 2 * X * oddPrimeWeight p * u3S p N c - (2 - X ^ (2 * p)) * u3U p N c =
      ∑ r : Fin (20 * N), C (c r) * (2 * X * oddPrimeWeight p * u3Sv p N r.val -
        (2 - X ^ (2 * p)) * u3Uv p N r.val) := by
    simp only [u3U, u3S, combLin_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h]
  exact Finset.dvd_sum fun r _ =>
    Dvd.dvd.mul_left (row_identity_K6 hN hp2 h4 r.isLt) _

end

end
end CatalanMeasure.Parametric
