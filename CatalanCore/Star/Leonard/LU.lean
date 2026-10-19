module

public import CatalanCore.Star.Leonard.Ttil

/-!
# (K1): the Darboux LU factorisation `T~ = L U` at `g = 0` (package H5)

`U = diag(μ) - Σ σ(a) E_{a,a+1}`, `L = I + Σ λ_a E_{a,a-1}`, `λ_a = -τ(a-1)/μ(a-1)`; for `K = S+m+1`
(i.e. `g = 0`) `Ttil K m S θ = L * U` (the pivots `μ(a)` are the `LU` pivots, `μ(K-1) = 0`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `(L U)` for unit lower bidiagonal `L` (subdiagonal `l`) and upper bidiagonal `U` (diagonal `d`,
superdiagonal `u`): entrywise. -/
lemma trid_mul_trid (n : ℕ) (u l d : ℕ → F) :
    trid n (fun _ => 0) l (fun _ => 1) * trid n u (fun _ => 0) d =
      trid n u (fun j => l j * d j)
        (fun i => d i + (if 0 < i then l (i - 1) * u (i - 1) else 0)) := by
  ext i j
  have hL : ∀ k : Fin n, trid n (fun _ => 0) l (fun _ => 1) i k =
      (if (k : ℕ) = i then 1 else 0) + (if (i : ℕ) = k + 1 then l k else 0) := by
    intro k; simp only [trid, Matrix.of_apply]; split_ifs <;> first | (exfalso; omega) | simp
  simp only [Matrix.mul_apply, hL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  rw [CatalanCore.sum_ite_val_eq (i : ℕ) (fun k => trid n u (fun _ => 0) d k j),
    show (∑ k : Fin n, if (i : ℕ) = k + 1 then l k * trid n u (fun _ => 0) d k j else 0) =
      if h : 0 < (i : ℕ) then l ((i : ℕ) - 1) * trid n u (fun _ => 0) d ⟨(i : ℕ) - 1, by omega⟩ j
        else 0 from by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
      · rw [dif_neg (by omega)]
        exact Finset.sum_eq_zero fun k _ => if_neg (by omega)
      · rw [dif_pos h]
        have : ∑ k : Fin n, (if (i : ℕ) = k + 1 then l k * trid n u (fun _ => 0) d k j else 0) =
            ∑ k : Fin n, (if (k : ℕ) = (i : ℕ) - 1 then l k * trid n u (fun _ => 0) d k j else 0) :=
          Finset.sum_congr rfl fun k _ => by
            congr 1; exact propext ⟨fun h2 => by omega, fun h2 => by omega⟩
        rw [this, CatalanCore.sum_ite_val_eq ((i : ℕ) - 1)
          (fun k => l k * trid n u (fun _ => 0) d k j), dif_pos (by omega)]]
  rw [dif_pos i.2]
  by_cases h0 : 0 < (i : ℕ)
  · rw [dif_pos h0]
    simp only [trid, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | skip
    all_goals first | rfl | (simp; done) | (rw [show (j : ℕ) = (i : ℕ) - 1 by omega]; simp; done)
  · rw [dif_neg h0]
    simp only [trid, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | skip
    all_goals first | rfl | (simp; done) | (rw [show (j : ℕ) = (i : ℕ) - 1 by omega]; simp; done)


/-- `L = I + Σ λ_a E_{a,a-1}`, `λ_{j+1} = -τ(j)/μ(j)`. -/
noncomputable def Lmat (K m S : ℕ) (θ : F) : Matrix (Fin K) (Fin K) F :=
  trid K (fun _ => 0) (fun j => -tau K m S θ j / mu K m S θ j) (fun _ => 1)

/-- `U = diag(μ) - Σ σ(a) E_{a,a+1}`. -/
noncomputable def Umat (K m S : ℕ) (θ : F) : Matrix (Fin K) (Fin K) F :=
  trid K (fun i => -sigma K m S θ i) (fun _ => 0) (fun i => mu K m S θ i)

lemma mu_ne_zero [CharZero F] (K m S : ℕ) (θ : F) (hθ : Gen θ) (j : ℕ) (hj : j + 1 < K) :
    mu K m S θ j ≠ 0 := by
  have hK : (K : F) - 1 - j ≠ 0 := by
    have := natsub_ne (F := F) (a := K - 1) (b := j) (by omega)
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; exact this
  have hG := genAt_nat hθ j
  have h1 : θ + (S : F) + 1 + j ≠ 0 := by
    have := hG (S + 1); push_cast at this; intro h0; apply this; linear_combination h0
  have h2 : θ + (S : F) + 2 * m + 1 + j ≠ 0 := by
    have := hG (S + 2 * m + 1); push_cast at this; intro h0; apply this; linear_combination h0
  unfold mu
  exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hK) h1) h2)

/-- **(K1).**  At `g = 0` (`K = S + m + 1`): `T~ = L U`. -/
theorem Ttil_eq_LU [CharZero F] (K m S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
    (hKS : K = S + m + 1) : Ttil K m S θ = Lmat K m S θ * Umat K m S θ := by
  have hg : gg K m S = (0 : F) := by
    unfold gg; rw [hKS]; push_cast; ring
  unfold Ttil Lmat Umat
  rw [trid_mul_trid]
  ext i j
  simp only [trid, Matrix.of_apply]
  have hsub : ∀ j : ℕ, j + 1 < K → -(-tau K m S θ j / mu K m S θ j * mu K m S θ j) = tau K m S θ j := by
    intro j hj
    rw [div_mul_cancel₀ _ (mu_ne_zero K m S θ hθ j hj)]; ring
  have hdiag : Dd K m S θ i = mu K m S θ i +
      (if 0 < (i : ℕ) then -tau K m S θ ((i : ℕ) - 1 : ℕ) / mu K m S θ ((i : ℕ) - 1 : ℕ)
        * -sigma K m S θ ((i : ℕ) - 1 : ℕ) else 0) := by
    unfold Dd
    rw [hg]
    split_ifs with h
    · have : (((i : ℕ) - 1 : ℕ) : F) = ((i : ℕ) : F) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; ring
    · have h0 : (i : ℕ) = 0 := by omega
      have : ((i : ℕ) : F) = 0 := by rw [h0]; simp
      rw [this, tau_bot]; simp
  by_cases h1 : (j : ℕ) = i
  · rw [if_pos h1, if_pos h1]; exact hdiag
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (j : ℕ) = i + 1
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : (i : ℕ) = j + 1
      · rw [if_pos h3, if_pos h3]
        have := hsub j (by have := i.2; omega)
        linear_combination this
      · rw [if_neg h3, if_neg h3]

end CatalanCore.Star.Leonard
