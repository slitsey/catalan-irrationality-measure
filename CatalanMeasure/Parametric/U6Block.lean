module
public import CatalanMeasure.Parametric.U6Identity
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

/-- The alternating binomial filter is the coefficient of a power of `X - 1`. -/
theorem binom_filter {R : Type*} [CommRing R] (A : R[X]) (m n : ℕ) :
    ∑ v ∈ Finset.range (n + 1), (-1 : R) ^ v * (n.choose v : R) * A.coeff (m + v) =
      ((X - 1) ^ n * A).coeff (m + n) := by
  have h1 : (X - 1 : R[X]) ^ n = ∑ i ∈ Finset.range (n + 1),
      X ^ i * C ((-1 : R) ^ (n - i) * (n.choose i : R)) := by
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [map_mul, map_pow]; ring
  rw [h1, Finset.sum_mul, finsetSum_coeff]
  have h2 : ∀ i ∈ Finset.range (n + 1), (X ^ i * C ((-1 : R) ^ (n - i) * (n.choose i : R)) * A).coeff
      (m + n) = (-1 : R) ^ (n - i) * (n.choose i : R) * A.coeff (m + n - i) := by
    intro i hi
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [mul_assoc, coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => absurd (by omega) h), coeff_C_mul]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvn : v ≤ n := by have := Finset.mem_range.mp hv; omega
  rw [show n + 1 - 1 - v = n - v by omega, Nat.choose_symm hvn, Nat.add_sub_assoc hvn]

theorem natDegree_one_sub_X_pow_le {R : Type*} [CommRing R] (n : ℕ) :
    ((1 - X : R[X]) ^ n).natDegree ≤ n := by
  calc _ ≤ n * (1 - X : R[X]).natDegree := natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = n := by ring

theorem natDegree_X_sub_one_pow_le {R : Type*} [CommRing R] (n : ℕ) :
    ((X - 1 : R[X]) ^ n).natDegree ≤ n := by
  calc _ ≤ n * (X - 1 : R[X]).natDegree := natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = n := by ring

theorem natDegree_one_add_X_pow_le {R : Type*} [CommRing R] (n : ℕ) :
    ((1 + X : R[X]) ^ n).natDegree ≤ n := by
  calc _ ≤ n * (1 + X : R[X]).natDegree := natDegree_pow_le
    _ ≤ n * 1 := Nat.mul_le_mul_left _ (by compute_degree)
    _ = n := by ring

section
variable {p N : ℕ} [hp : Fact p.Prime]

/-- `X^(8N+1)` divides every reflected `U` row. -/
theorem u3Uv_dvd (hp2 : p ≠ 2) {r : ℕ} (hr : r < 20 * N) :
    X ^ (8 * N + 1) ∣ u3Uv p N r := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  have hm := u3Offset_natAbs_le hr
  have hd : (Chebyshev.U (ZMod p) (u3Offset N r - 1)).natDegree ≤ 18 * N - 2 := by
    rw [Chebyshev.natDegree_U]; omega
  have := reflect_dvd_of_natDegree_le _ hd (show 18 * N - 2 ≤ 26 * N - 1 by omega)
  refine (pow_dvd_pow X ?_).trans this
  omega

theorem u3U_dvd (hp2 : p ≠ 2) (c : Fin (20 * N) → ZMod p) :
    X ^ (8 * N + 1) ∣ u3U p N c := by
  simp only [u3U, combLin_apply]
  exact Finset.dvd_sum fun r _ => Dvd.dvd.mul_left (u3Uv_dvd hp2 r.isLt) _

/-- The `X - 1` twisted `P` side: `(X-1)^N * X * W * (1-X)^N * S_c`. -/
def u6Q (p N : ℕ) [Fact p.Prime] (c : Fin (20 * N) → ZMod p) : (ZMod p)[X] :=
  (X - 1) ^ N * (X * oddPrimeWeight p * ((1 - X) ^ N * u3S p N c))

/-- The `X - 1` twisted `D` side: `(X-1)^N * (1-X)^N * U_c`. -/
def u6D (p N : ℕ) [Fact p.Prime] (c : Fin (20 * N) → ZMod p) : (ZMod p)[X] :=
  (X - 1) ^ N * ((1 - X) ^ N * u3U p N c)

theorem oddPrimeWeight_natDegree_le : (oddPrimeWeight p).natDegree ≤ p - 1 := by
  unfold oddPrimeWeight
  rw [one_sub_X_sq_natDegree]; omega

theorem u6Q_coeff_zero (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) {i : ℕ}
    (hi : i ≤ 8 * N) : (u6Q p N c).coeff i = 0 := by
  have hd : X ^ (8 * N + 1) ∣ u6Q p N c := by
    unfold u6Q
    have h1 : X ^ (8 * N + 1) ∣ X * u3S p N c := by
      rw [pow_succ']; exact mul_dvd_mul_left X (u3S_dvd hp2 hN c)
    have : X * oddPrimeWeight p * ((1 - X) ^ N * u3S p N c) =
        oddPrimeWeight p * (1 - X) ^ N * (X * u3S p N c) := by ring
    rw [this]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h1 _) _
  exact X_pow_dvd_iff.mp hd i (by omega)

theorem u6D_coeff_zero (hp2 : p ≠ 2) (c : Fin (20 * N) → ZMod p) {i : ℕ}
    (hi : i ≤ 8 * N) : (u6D p N c).coeff i = 0 := by
  have hd : X ^ (8 * N + 1) ∣ u6D p N c := by
    unfold u6D
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (u3U_dvd hp2 c) _) _
  exact X_pow_dvd_iff.mp hd i (by omega)

theorem u6Q_natDegree (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) :
    (u6Q p N c).natDegree ≤ 28 * N + p - 1 := by
  have hp1 := hp.out.one_le
  unfold u6Q
  have h1 := natDegree_X_sub_one_pow_le (R := ZMod p) N
  have h2 := natDegree_one_sub_X_pow_le (R := ZMod p) N
  have h3 := oddPrimeWeight_natDegree_le (p := p)
  have h4 := u3S_natDegree hp2 hN c
  have h5 : (X * oddPrimeWeight p * ((1 - X) ^ N * u3S p N c)).natDegree ≤
      1 + (p - 1) + (N + (26 * N - 1)) :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X_le h3)
      (natDegree_mul_le_of_le h2 h4)
  have := natDegree_mul_le_of_le h1 h5
  omega

theorem u6D_natDegree (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) :
    (u6D p N c).natDegree ≤ 28 * N - 1 := by
  unfold u6D
  have h1 := natDegree_X_sub_one_pow_le (R := ZMod p) N
  have h2 := natDegree_one_sub_X_pow_le (R := ZMod p) N
  have h4 := u3U_natDegree hp2 hN c
  have := natDegree_mul_le_of_le h1 (natDegree_mul_le_of_le h2 h4)
  omega

/-- Identity K6 at the level of coefficients below `24N`. -/
theorem u6_K6_coeff (hN : 0 < N) (hp2 : p ≠ 2) (h4 : 4 * N ≤ p)
    (c : Fin (20 * N) → ZMod p) {i : ℕ} (hi : i < 24 * N) :
    2 * (u6Q p N c).coeff i + (if 2 * p ≤ i then (u6D p N c).coeff (i - 2 * p) else 0) =
      2 * (u6D p N c).coeff i := by
  have hK := comb_identity_K6 hN hp2 h4 c
  have hK' : X ^ (24 * N) ∣ 2 * u6Q p N c - (2 - X ^ (2 * p)) * u6D p N c := by
    have : 2 * u6Q p N c - (2 - X ^ (2 * p)) * u6D p N c =
        (X - 1) ^ N * (1 - X) ^ N *
          (2 * X * oddPrimeWeight p * u3S p N c - (2 - X ^ (2 * p)) * u3U p N c) := by
      unfold u6Q u6D; ring
    rw [this]
    exact Dvd.dvd.mul_left hK _
  have h0 := X_pow_dvd_iff.mp hK' i hi
  have e : 2 * u6Q p N c - (2 - X ^ (2 * p)) * u6D p N c =
      2 * u6Q p N c - 2 * u6D p N c + X ^ (2 * p) * u6D p N c := by ring
  rw [e, coeff_add, coeff_sub, coeff_X_pow_mul'] at h0
  have h2 : ∀ q : (ZMod p)[X], (2 * q).coeff i = 2 * q.coeff i := by
    intro q
    rw [← C_ofNat, coeff_C_mul]
  rw [h2, h2] at h0
  linear_combination h0


/-- The quotient `Y` in the Frobenius class-sum law. -/
def u6Y (p N : ℕ) [Fact p.Prime] (c : Fin (20 * N) → ZMod p) : (ZMod p)[X] :=
  (-1) ^ N * X * (1 + X) ^ ((p - 1) / 2) * u3S p N c

theorem u6_frobenius {e : ℕ} (he : e + (p - 1) / 2 + 2 * N = p) (c : Fin (20 * N) → ZMod p) :
    (1 - X) ^ e * u6Q p N c = (1 - X ^ p) * u6Y p N c := by
  have hsub : (1 - X : (ZMod p)[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char, one_pow]
  have h1 : (X - 1 : (ZMod p)[X]) ^ N = (-1) ^ N * (1 - X) ^ N := by
    rw [← neg_sub, neg_pow]
  have h2 : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p - 1) / 2) =
      (1 - X) ^ ((p - 1) / 2) * (1 + X) ^ ((p - 1) / 2) := by
    rw [← mul_pow]; congr 1; ring
  have h3 : (1 - X : (ZMod p)[X]) ^ p =
      (1 - X) ^ e * (1 - X) ^ ((p - 1) / 2) * (1 - X) ^ N * (1 - X) ^ N := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  unfold u6Q u6Y oddPrimeWeight
  rw [h1, h2, ← hsub, h3]
  ring

theorem u6Y_natDegree (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) :
    (u6Y p N c).natDegree ≤ 26 * N + (p - 1) / 2 := by
  unfold u6Y
  have h4 := u3S_natDegree hp2 hN c
  have h5 := natDegree_one_add_X_pow_le (R := ZMod p) ((p - 1) / 2)
  have h6 : ((-1 : (ZMod p)[X]) ^ N * X).natDegree ≤ 0 + 1 := by
    refine natDegree_mul_le_of_le ?_ natDegree_X_le
    rw [← C_1, ← C_neg, ← C_pow]; exact natDegree_C _ |>.le
  have := natDegree_mul_le_of_le (natDegree_mul_le_of_le h6 h5) h4
  omega

theorem u6Y_coeff_zero (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) {i : ℕ}
    (hi : i ≤ 8 * N) : (u6Y p N c).coeff i = 0 := by
  have hd : X ^ (8 * N + 1) ∣ u6Y p N c := by
    unfold u6Y
    have h1 : X ^ (8 * N + 1) ∣ X * u3S p N c := by
      rw [pow_succ']; exact mul_dvd_mul_left X (u3S_dvd hp2 hN c)
    have : (-1 : (ZMod p)[X]) ^ N * X * (1 + X) ^ ((p - 1) / 2) * u3S p N c =
        (-1) ^ N * (1 + X) ^ ((p - 1) / 2) * (X * u3S p N c) := by ring
    rw [this]
    exact Dvd.dvd.mul_left h1 _
  exact X_pow_dvd_iff.mp hd i (by omega)

end

end
end CatalanMeasure.Parametric
