module

public import CatalanCore.Zeta5.Local.SmallPrimeF
public import CatalanCore.Zeta5.Local.GleBridge

@[expose] public section

/-!
# Row ZC08: the integer-valued basis `f_i` and `F_K = det[(K!)² μ_X(f_i f_j / D_K)]`

`q_0 = 1`, `q_i = (-1)^i 2 t D_{i-1}/(2i)!` is `qP i` (ported), `f_i = (D_N/(N!)²)³ q_i` is
`fpoly n i`.  We prove

* `F_eq_det_basis` : `F_K = det_{i,j<h} [(K!)² μ_X(f_i f_j / D_K)]` (exact identity in `ℚ[X]`);
* `fpoly_eval_int` : `f_i(-z²)` is an integer for every integer `z` (all primes at once).
-/

open Finset Polynomial

namespace Apery

/-- `f_i = (D_N / (N!)²)³ q_i` for `N = 3n`. -/
noncomputable def fpoly (n a : ℕ) : ℚ[X] :=
  C ((((3 * n).factorial : ℚ) ^ 6)⁻¹) * D (3 * n) ^ 3 * qP a

/-- `F_K` as a scaled basis determinant (the intermediate form used by `small_prime_bound`). -/
theorem F_eq_smul_det {n : ℕ} (hn : 1 ≤ n) :
    F n = ((C (((40 * n).factorial : ℚ) ^ 2 / ((3 * n).factorial : ℚ) ^ 12)) •
      (Matrix.of fun a b : Fin (37 * n) => μX (40 * n) (D (3 * n) ^ 6 * qP a * qP b))).det := by
  have hEdeg : ∀ a : Fin (37 * n), (qP (a : ℕ)).natDegree < 37 * n := fun a => by
    rw [natDegree_qP]; exact a.isLt
  have hbc := det_basis_change n (fun a : Fin (37 * n) => qP (a : ℕ)) hEdeg
  rw [Matrix.det_smul, hbc, Fintype.card_fin, F, S_eq_qlead n hn, det_coeffMat_qP]
  simp only [map_mul, map_pow]
  ring

/-- **ZC08**: `F_K = det[(K!)² μ_X(f_i f_j / D_K)]`. -/
theorem F_eq_det_basis (n : ℕ) :
    F n = (Matrix.of fun a b : Fin (37 * n) =>
      C (((40 * n).factorial : ℚ) ^ 2) * μX (40 * n) (fpoly n a * fpoly n b)).det := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [F, S, Δ]
  rw [F_eq_smul_det hn]
  congr 1
  ext a b
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have e : fpoly n a * fpoly n b =
      C ((((3 * n).factorial : ℚ) ^ 12)⁻¹) * (D (3 * n) ^ 6 * qP a * qP b) := by
    unfold fpoly
    have : C ((((3 * n).factorial : ℚ) ^ 12)⁻¹) =
        C ((((3 * n).factorial : ℚ) ^ 6)⁻¹) * C ((((3 * n).factorial : ℚ) ^ 6)⁻¹) := by
      rw [← C_mul]; congr 1; rw [← mul_inv, ← pow_add]
    rw [this]; ring
  rw [e, μX_C_mul, ← mul_assoc, ← C_mul]
  congr 2

/-- **ZC08**: `f_i(-z²)` is an integer for every integer `z`. -/
theorem fpoly_eval_int (n a : ℕ) (z : ℤ) : ∃ w : ℤ, (fpoly n a).eval (-(z : ℚ) ^ 2) = w := by
  apply CatalanCore.Basic.int_of_forall_locRing
  intro p _
  rw [mem_locRing_iff_VG]
  have e : (fpoly n a).eval (-(z : ℚ) ^ 2) =
      ((D (3 * n)).eval (-(z : ℚ) ^ 2) / ((3 * n).factorial : ℚ) ^ 2) ^ 3 *
        (qP a).eval (-(z : ℚ) ^ 2) := by
    unfold fpoly
    simp only [eval_mul, eval_C, eval_pow]
    have : ((3 * n).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  rw [e]
  have := ((VG_D_eval (p := p) (3 * n) z).pow 3).mul (VG_qP_eval (p := p) a z)
  simpa using this

end Apery
