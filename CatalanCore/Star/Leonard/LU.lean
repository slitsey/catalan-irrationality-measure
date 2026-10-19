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

end CatalanCore.Star.Leonard
