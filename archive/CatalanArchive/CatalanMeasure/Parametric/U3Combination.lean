module
public import CatalanArchive.CatalanMeasure.Parametric.U3RowIdentity
public import Mathlib.Algebra.Polynomial.Taylor
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeWeight
@[expose] public section

/-!
# Row combinations and the flag subspace (Lemma U3)

For a coefficient vector `c` over the rows of the canonical design, with
`S_c = ∑ c_r reflect(T_r)` and `U_c = ∑ c_r reflect(U_r)`, we have
`P_c = (1-X)^N S_c`, `D_c = (1-X)^N U_c`.  On the flag subspace
(`(1-X^2)^((p+1)/2) ∣ P_c`) we define `Q~ = X * (P_c / (1-X^2)^h)` and prove
its support and identity K (`D_c ≡ Q~` modulo `X^(24N)`).
-/

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

/-- The polynomial combination `∑ c_i • v_i`. -/
def combLin {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (v : ι → R[X]) :
    (ι → R) →ₗ[R] R[X] where
  toFun c := ∑ i, C (c i) * v i
  map_add' c d := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum, mul_assoc, smul_eq_C_mul]

theorem combLin_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (v : ι → R[X])
    (c : ι → R) : combLin v c = ∑ i, C (c i) * v i := rfl

theorem combLin_mul_left {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (v : ι → R[X])
    (f : R[X]) (c : ι → R) : f * combLin v c = combLin (fun i => f * v i) c := by
  simp only [combLin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section
variable {p N : ℕ} [hp : Fact p.Prime]

/-- Reflected Chebyshev `T` of row `r`. -/
def u3Sv (p N r : ℕ) : (ZMod p)[X] :=
  reflect (26 * N - 1) (Chebyshev.T (ZMod p) (u3Offset N r))

/-- Reflected Chebyshev `U` of row `r`. -/
def u3Uv (p N r : ℕ) : (ZMod p)[X] :=
  reflect (26 * N - 1) (Chebyshev.U (ZMod p) (u3Offset N r - 1))

def u3S (p N : ℕ) : (Fin (20 * N) → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  combLin (fun r : Fin (20 * N) => u3Sv p N r.val)

def u3U (p N : ℕ) : (Fin (20 * N) → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  combLin (fun r : Fin (20 * N) => u3Uv p N r.val)

/-- Identity K for any row combination. -/
theorem comb_identity_K (hN : 0 < N) (hp2 : p ≠ 2) (h8 : 8 * N < p) (h9 : p < 9 * N)
    (c : Fin (20 * N) → ZMod p) :
    X ^ (24 * N) ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * u3U p N c -
      X * u3S p N c := by
  have h : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * u3U p N c - X * u3S p N c =
      ∑ r : Fin (20 * N), C (c r) * ((1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        u3Uv p N r.val - X * u3Sv p N r.val) := by
    simp only [u3U, u3S, combLin_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h]
  exact Finset.dvd_sum fun r _ =>
    Dvd.dvd.mul_left (row_identity_core hN hp2 h8 h9 r.isLt) _

/-- Every reflected row is divisible by `X^(8N)`. -/
theorem u3Sv_dvd (hp2 : p ≠ 2) (hN : 0 < N) {r : ℕ} (hr : r < 20 * N) :
    X ^ (8 * N) ∣ u3Sv p N r := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  have hm := u3Offset_natAbs_le hr
  have hd : (Chebyshev.T (ZMod p) (u3Offset N r)).natDegree ≤ 18 * N - 1 := by
    rw [Chebyshev.natDegree_T]; exact hm
  have := reflect_dvd_of_natDegree_le _ hd (show 18 * N - 1 ≤ 26 * N - 1 by omega)
  exact (pow_dvd_pow X (by omega)).trans this

theorem u3S_dvd (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) :
    X ^ (8 * N) ∣ u3S p N c := by
  simp only [u3S, combLin_apply]
  exact Finset.dvd_sum fun r _ => Dvd.dvd.mul_left (u3Sv_dvd hp2 hN r.isLt) _

theorem u3S_natDegree (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) :
    (u3S p N c).natDegree ≤ 26 * N - 1 := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  simp only [u3S, combLin_apply]
  apply natDegree_sum_le_of_forall_le
  intro r _
  refine (natDegree_C_mul_le _ _).trans ?_
  unfold u3Sv
  refine natDegree_reflect_le.trans ?_
  have hm := u3Offset_natAbs_le r.isLt
  have hd : (Chebyshev.T (ZMod p) (u3Offset N r)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_T]; omega
  exact max_le le_rfl hd

theorem u3U_natDegree (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) :
    (u3U p N c).natDegree ≤ 26 * N - 1 := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  simp only [u3U, combLin_apply]
  apply natDegree_sum_le_of_forall_le
  intro r _
  refine (natDegree_C_mul_le _ _).trans ?_
  unfold u3Uv
  refine natDegree_reflect_le.trans ?_
  have hm := u3Offset_natAbs_le r.isLt
  have hd : (Chebyshev.U (ZMod p) (u3Offset N r - 1)).natDegree ≤ 26 * N - 1 := by
    rw [Chebyshev.natDegree_U]; omega
  exact max_le le_rfl hd

theorem u3D_coeff_zero (hp2 : p ≠ 2) (hN : 0 < N) (c : Fin (20 * N) → ZMod p) {i : ℕ}
    (hi : 27 * N ≤ i) : ((1 - X) ^ N * u3U p N c).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt natDegree_mul_le ?_
  have h1 : ((1 - X : (ZMod p)[X]) ^ N).natDegree ≤ N := by
    calc _ ≤ N * (1 - X : (ZMod p)[X]).natDegree := natDegree_pow_le
      _ ≤ N * 1 := Nat.mul_le_mul_left _ (by compute_degree)
      _ = N := by ring
  have := u3U_natDegree hp2 hN c
  omega

/-! ### Flag conditions -/

theorem dvd_of_taylor_coeff_zero {R : Type*} [CommRing R] (a : R) (k : ℕ) (f : R[X])
    (h : ∀ i < k, (taylor a f).coeff i = 0) : (X - C a) ^ k ∣ f := by
  obtain ⟨g, hg⟩ := X_pow_dvd_iff.mpr h
  refine ⟨g.comp (X - C a), ?_⟩
  have h1 : f = (taylor a f).comp (X - C a) := by
    rw [taylor_apply, comp_assoc]
    simp
  conv_lhs => rw [h1, hg]
  rw [mul_comp, pow_comp, X_comp]

/-- Taylor coefficient functionals at `1`, orders `0 .. h-N-1`. -/
def u3FlagUp (p N : ℕ) : (Fin (20 * N) → ZMod p) →ₗ[ZMod p]
    (Fin ((p + 1) / 2 - N) → ZMod p) :=
  LinearMap.pi fun i => (lcoeff (ZMod p) (i : ℕ)).comp ((taylor (1 : ZMod p)).comp (u3S p N))

/-- Taylor coefficient functionals at `-1`, orders `0 .. h-1`. -/
def u3FlagDown (p N : ℕ) : (Fin (20 * N) → ZMod p) →ₗ[ZMod p]
    (Fin ((p + 1) / 2) → ZMod p) :=
  LinearMap.pi fun i => (lcoeff (ZMod p) (i : ℕ)).comp ((taylor (-1 : ZMod p)).comp (u3S p N))

theorem u3Flag_dvd (hp2 : p ≠ 2) (hNh : N ≤ (p + 1) / 2) (c : Fin (20 * N) → ZMod p)
    (h1 : u3FlagUp p N c = 0) (h2 : u3FlagDown p N c = 0) :
    ∃ Y : (ZMod p)[X], (1 - X) ^ N * u3S p N c = (1 - X ^ 2) ^ ((p + 1) / 2) * Y := by
  have hu : (X - C (1 : ZMod p)) ^ ((p + 1) / 2 - N) ∣ u3S p N c := by
    apply dvd_of_taylor_coeff_zero
    intro i hi
    have := congrFun h1 ⟨i, hi⟩
    simpa [u3FlagUp] using this
  have hd : (X - C (-1 : ZMod p)) ^ ((p + 1) / 2) ∣ u3S p N c := by
    apply dvd_of_taylor_coeff_zero
    intro i hi
    have := congrFun h2 ⟨i, hi⟩
    simpa [u3FlagDown] using this
  have hcop : IsCoprime ((X - C (1 : ZMod p)) ^ ((p + 1) / 2 - N))
      ((X - C (-1 : ZMod p)) ^ ((p + 1) / 2)) := by
    apply IsCoprime.pow
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero p hp2
    refine ⟨-C (2 : ZMod p)⁻¹, C (2 : ZMod p)⁻¹, ?_⟩
    have : (C (2 : ZMod p)⁻¹ * C 2 : (ZMod p)[X]) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ h2, C_1]
    have h2c : (2 : (ZMod p)[X]) = C 2 := (C_ofNat (R := ZMod p) 2).symm
    simp only [map_neg, map_one]
    linear_combination this + (C (2 : ZMod p)⁻¹) * h2c
  obtain ⟨Z, hZ⟩ := hcop.mul_dvd hu hd
  generalize hk : (p + 1) / 2 - N = k at hZ
  have hk2 : (p + 1) / 2 = N + k := by omega
  refine ⟨(-1) ^ k * Z, ?_⟩
  have e1 : (X - C (1 : ZMod p)) = -(1 - X) := by simp
  have e2 : (X - C (-1 : ZMod p)) = 1 + X := by
    rw [map_neg, map_one]; ring
  have e3 : (1 - X ^ 2 : (ZMod p)[X]) = (1 - X) * (1 + X) := by ring
  rw [hZ, e1, e2, e3, hk2, mul_pow, neg_pow]
  ring

theorem isCoprime_X_pow_one_sub_X_sq (m h : ℕ) :
    IsCoprime ((X : (ZMod p)[X]) ^ m) ((1 - X ^ 2 : (ZMod p)[X]) ^ h) := by
  apply IsCoprime.pow
  exact ⟨X, 1, by ring⟩

theorem one_sub_X_sq_pow_prime : (1 - X ^ 2 : (ZMod p)[X]) ^ p = 1 - X ^ (2 * p) := by
  rw [sub_pow_char, one_pow, ← pow_mul]

theorem one_sub_X_sq_natDegree (h : ℕ) :
    ((1 - X ^ 2 : (ZMod p)[X]) ^ h).natDegree = 2 * h := by
  have h1 : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp
  rw [natDegree_pow, h1]; ring

/-- Support and identity K for `Q~ = X * Y` on the flag subspace. -/
theorem u3Qt_props (hp2 : p ≠ 2) (hN : 0 < N) (h9 : p < 9 * N)
    (h8 : 8 * N < p) (c : Fin (20 * N) → ZMod p) (Y : (ZMod p)[X])
    (hY : (1 - X) ^ N * u3S p N c = (1 - X ^ 2) ^ ((p + 1) / 2) * Y) :
    (∀ i, i ≤ 8 * N → (X * Y).coeff i = 0) ∧
    (∀ i, 27 * N - p ≤ i → (X * Y).coeff i = 0) ∧
    (∀ k, k < 24 * N → ((1 - X) ^ N * u3U p N c).coeff k = (X * Y).coeff k) ∧
    X * oddPrimeWeight p * ((1 - X) ^ N * u3S p N c) = (1 - X ^ (2 * p)) * (X * Y) := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hcop8 := isCoprime_X_pow_one_sub_X_sq (p := p) (8 * N) ((p + 1) / 2)
  have hcop24 := isCoprime_X_pow_one_sub_X_sq (p := p) (24 * N) ((p + 1) / 2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hd : X ^ (8 * N) ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * Y := by
      rw [← hY]
      exact Dvd.dvd.mul_left (u3S_dvd hp2 hN c) _
    have hY8 := X_pow_dvd_iff.mp (hcop8.dvd_of_dvd_mul_left hd)
    rcases i with _ | i
    · simp
    · rw [coeff_X_mul]; exact hY8 i (by omega)
  · intro i hi
    by_cases hY0 : Y = 0
    · simp [hY0]
    have hA0 : ((1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2)) ≠ 0 := by
      intro h
      have := congrArg natDegree h
      rw [one_sub_X_sq_natDegree] at this
      simp at this
      omega
    have hdeg : ((1 - X) ^ N * u3S p N c).natDegree ≤ 27 * N - 1 := by
      refine natDegree_mul_le.trans ?_
      have h1 : ((1 - X : (ZMod p)[X]) ^ N).natDegree ≤ N := by
        calc _ ≤ N * (1 - X : (ZMod p)[X]).natDegree := natDegree_pow_le
          _ ≤ N * 1 := Nat.mul_le_mul_left _ (by compute_degree)
          _ = N := by ring
      have := u3S_natDegree hp2 hN c
      omega
    rw [hY, natDegree_mul hA0 hY0, one_sub_X_sq_natDegree] at hdeg
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_X_mul hY0]
    have : (p + 1) / 2 * 2 = p + 1 := by omega
    omega
  · intro k hk
    have hK := comb_identity_K hN hp2 h8 h9 c
    have hK' : X ^ (24 * N) ∣ (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) *
        ((1 - X) ^ N * u3U p N c) - X * ((1 - X) ^ N * u3S p N c) := by
      have : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * ((1 - X) ^ N * u3U p N c) -
          X * ((1 - X) ^ N * u3S p N c) = (1 - X) ^ N *
          ((1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * u3U p N c - X * u3S p N c) := by ring
      rw [this]
      exact Dvd.dvd.mul_left hK _
    rw [hY] at hK'
    have : (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * ((1 - X) ^ N * u3U p N c) -
        X * ((1 - X ^ 2) ^ ((p + 1) / 2) * Y) =
        (1 - X ^ 2 : (ZMod p)[X]) ^ ((p + 1) / 2) * ((1 - X) ^ N * u3U p N c - X * Y) := by ring
    rw [this] at hK'
    have h24 := X_pow_dvd_iff.mp (hcop24.dvd_of_dvd_mul_left hK') k hk
    rw [coeff_sub] at h24
    exact sub_eq_zero.mp h24
  · rw [hY, oddPrimeWeight]
    have e : (X : (ZMod p)[X]) * (1 - X ^ 2) ^ ((p - 1) / 2) *
        ((1 - X ^ 2) ^ ((p + 1) / 2) * Y) = X * ((1 - X ^ 2) ^ ((p - 1) / 2 + (p + 1) / 2) * Y) := by
      rw [pow_add]; ring
    rw [e, show (p - 1) / 2 + (p + 1) / 2 = p by omega, one_sub_X_sq_pow_prime]
    ring

end

end
end CatalanMeasure.Parametric
