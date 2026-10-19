module

public import CatalanCore.Star.Leonard.DeltaMat

/-!
# Prop hDelta, step (4): `det E` in terms of the binomial Hankel matrix `C(K, i+j+1)`

`E_{pq} = ∑_{a<K} 1/(a+θ+p+1)_{2m-p-q}`.  After reversing rows and columns,
`E'_{pq} = pochr(θ+1)(m-1-p) · pochr(θ+1)(m+q+K)⁻¹ · f[u_p, v_q]` with `f = (z)_K`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- The matrix `E` of Prop hDelta. -/
noncomputable def Emat (θ : F) (K m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun (p q : Fin m) => ∑ a : Fin K,
    (pochr (((a : ℕ) : F) + θ + ((p : ℕ) : F) + 1) (2 * m - (p : ℕ) - (q : ℕ)))⁻¹

lemma pochr_one_ne (θ : F) (hθ : Gen θ) (L : ℕ) : pochr (θ + 1) L ≠ 0 :=
  pochr_ne_zero _ _ fun i _ => by
    have := hθ (1 + i); push_cast at this
    intro h; apply this; linear_combination h

lemma alg_aux {P' P'' Q Q'' : F} (h1 : P' ≠ 0) (h2 : Q ≠ 0) (h3 : Q'' ≠ 0) :
    P' / Q - P'' / Q'' = P' * Q''⁻¹ * (Q'' / Q - P'' / P') := by
  field_simp

/-- the entry of the reversed matrix -/
lemma E'_entry (θ : F) (hθ : Gen θ) (K m p q : ℕ) (hp : p < m) (hq : q < m) :
    ∑ a ∈ range K, (pochr ((a : F) + (θ + (m : F)) - (p : F)) (p + q + 2))⁻¹ =
      pochr (θ + 1) (m - 1 - p) * (pochr (θ + 1) (m + q + K))⁻¹ *
        dd (fun z => pochr z K) (insert (uN (θ + (m : F)) p) {vN (θ + (m : F)) q}) := by
  set b : F := θ + 1 with hb
  set a0 : ℕ := m - 1 - p with ha0
  set c : F := b + (a0 : F) with hc
  have hcx : θ + (m : F) - (p : F) = c := by
    simp only [hc, hb, ha0]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hL : ((p + q + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hne : uN (θ + (m : F)) p ≠ vN (θ + (m : F)) q := fun h => (vN_ne_uN _ q p) h.symm
  rw [dd_pair _ _ _ hne]
  have hvu : vN (θ + (m : F)) q - uN (θ + (m : F)) p = ((p + q + 1 : ℕ) : F) := by
    simp only [vN, uN]; push_cast; ring
  have hu : uN (θ + (m : F)) p = c := by simp only [uN]; rw [← hcx]
  have hv : vN (θ + (m : F)) q = c + ((p + q + 1 : ℕ) : F) := by
    rw [← hu]; simp only [vN, uN]; push_cast; ring
  rw [hvu, hu, hv]
  -- telescoping
  have hnz : ∀ i : ℕ, i < K + (p + q + 1) + 1 → c + (i : F) ≠ 0 := by
    intro i _
    have := hθ ((m : ℤ) - p + i); push_cast at this
    intro h; apply this
    rw [← hcx] at h; linear_combination h
  have tele := tele_sum c (p + q + 1) K hnz
  have hs : ∑ a ∈ range K, (pochr ((a : F) + (θ + (m : F)) - (p : F)) (p + q + 2))⁻¹ =
      ∑ a ∈ range K, (pochr (c + (a : F)) (p + q + 1 + 1))⁻¹ :=
    Finset.sum_congr rfl fun a _ => by rw [← hcx]; congr 2; ring
  rw [hs]
  have key : ∑ a ∈ range K, (pochr (c + (a : F)) (p + q + 1 + 1))⁻¹ =
      ((pochr c (p + q + 1))⁻¹ - (pochr (c + (K : F)) (p + q + 1))⁻¹) / ((p + q + 1 : ℕ) : F) := by
    rw [eq_div_iff hL, mul_comm]
    exact_mod_cast tele
  rw [key]
  -- pochr bookkeeping
  have e1 : pochr b (a0 + (p + q + 1)) = pochr b a0 * pochr c (p + q + 1) := pochr_add b a0 _
  have e2 : pochr b ((a0 + K) + (p + q + 1)) = pochr b (a0 + K) * pochr (c + (K : F)) (p + q + 1) := by
    rw [pochr_add]; congr 2; simp only [hc]; push_cast; ring
  have e3 : pochr b (a0 + K) = pochr b a0 * pochr c K := pochr_add b a0 K
  have e4 : pochr b ((a0 + (p + q + 1)) + K) =
      pochr b (a0 + (p + q + 1)) * pochr (c + ((p + q + 1 : ℕ) : F)) K := by
    rw [pochr_add]; congr 2; simp only [hc]; push_cast; ring
  have n1 : a0 + (p + q + 1) = m + q := by omega
  have n2 : (a0 + (p + q + 1)) + K = m + q + K := by omega
  have n3 : (a0 + K) + (p + q + 1) = m + q + K := by omega
  rw [n1] at e1 e4
  rw [n3] at e2
  have hP' : pochr b a0 ≠ 0 := pochr_one_ne θ hθ _
  have hP'' : pochr b (a0 + K) ≠ 0 := pochr_one_ne θ hθ _
  have hQ : pochr b (m + q) ≠ 0 := pochr_one_ne θ hθ _
  have hQ'' : pochr b (m + q + K) ≠ 0 := pochr_one_ne θ hθ _
  have hpc : pochr c (p + q + 1) ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hQ e1
  have hpcK : pochr (c + (K : F)) (p + q + 1) ≠ 0 := by
    intro h; rw [h, mul_zero] at e2; exact hQ'' e2
  have i1 : (pochr c (p + q + 1))⁻¹ = pochr b a0 / pochr b (m + q) := by
    rw [e1]; field_simp
  have i2 : (pochr (c + (K : F)) (p + q + 1))⁻¹ = pochr b (a0 + K) / pochr b (m + q + K) := by
    rw [e2]; field_simp
  have i3 : pochr c K = pochr b (a0 + K) / pochr b a0 := by rw [e3]; field_simp
  have i4 : pochr (c + ((p + q + 1 : ℕ) : F)) K = pochr b (m + q + K) / pochr b (m + q) := by
    rw [e4]; field_simp
  rw [i1, i2, i3, i4, alg_aux hP' hQ hQ'']
  ring

/-- `det E` as a product of Pochhammer factors times `det (dd-matrix)`. -/
theorem det_E_MD (θ : F) (hθ : Gen θ) (K m : ℕ) :
    (Emat θ K m).det = (∏ p : Fin m, pochr (θ + 1) (m - 1 - (p : ℕ))) *
      (∏ q : Fin m, (pochr (θ + 1) (m + (q : ℕ) + K))⁻¹) * (MD (θ + (m : F)) K m).det := by
  rw [← Matrix.det_submatrix_equiv_self (Fin.revPerm : Equiv.Perm (Fin m)) (Emat θ K m)]
  have : (Emat θ K m).submatrix (Fin.revPerm : Equiv.Perm (Fin m)) Fin.revPerm =
      Matrix.diagonal (fun p : Fin m => pochr (θ + 1) (m - 1 - (p : ℕ))) * MD (θ + (m : F)) K m *
        Matrix.diagonal (fun q : Fin m => (pochr (θ + 1) (m + (q : ℕ) + K))⁻¹) := by
    ext p q
    simp only [Matrix.submatrix_apply, Emat, Matrix.of_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, MD, Fin.revPerm_apply, Fin.val_rev]
    have hp := p.2
    have hq := q.2
    rw [Fin.sum_univ_eq_sum_range (fun a => (pochr ((a : F) + θ + (((m - ((p : ℕ) + 1) : ℕ)) : F) + 1)
      (2 * m - (m - ((p : ℕ) + 1)) - (m - ((q : ℕ) + 1))))⁻¹) K]
    have h1 : ∀ a : ℕ, ((a : F) + θ + (((m - ((p : ℕ) + 1) : ℕ)) : F) + 1) =
        (a : F) + (θ + (m : F)) - ((p : ℕ) : F) := by
      intro a; rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h2 : 2 * m - (m - ((p : ℕ) + 1)) - (m - ((q : ℕ) + 1)) = (p : ℕ) + q + 2 := by omega
    simp only [h1, h2]
    rw [E'_entry θ hθ K m p q hp hq]
    have h3 : m - 1 - (p : ℕ) = m - ((p : ℕ) + 1) := by omega
    rw [h3]; ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-- **Step (4) done:** `det E` in terms of the binomial Hankel determinant `det [C(K,i+j+1)]`. -/
theorem det_E_HB (θ : F) (hθ : Gen θ) (K m : ℕ) :
    (Emat θ K m).det = (∏ p : Fin m, pochr (θ + 1) (m - 1 - (p : ℕ))) *
      (∏ q : Fin m, (pochr (θ + 1) (m + (q : ℕ) + K))⁻¹) *
      ((∏ p : Fin m, ((-1 : F) ^ (p : ℕ) * ((p : ℕ).factorial : F))) *
        ((∏ i : Fin m, pochr (θ + (m : F) + 1) (K - 1 - (i : ℕ))) *
          (∏ j : Fin m, (pochr (θ + (m : F) + 1) (j : ℕ))⁻¹) * (HB K m).det) *
        ∏ q : Fin m, (((q : ℕ).factorial : F))) := by
  rw [det_E_MD θ hθ K m, det_MD, det_DM]
  intro j
  exact pochr_ne_zero _ _ fun i _ => by
    have := hθ ((m : ℤ) + 1 + i); push_cast at this
    intro h; apply this; linear_combination h

end CatalanCore.Star.Leonard
