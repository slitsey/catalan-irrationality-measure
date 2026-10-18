module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Symmetric tridiagonal matrices

`tri n up d` is the `n × n` symmetric tridiagonal matrix with diagonal `d i` and off-diagonal
entries `T i (i+1) = T (i+1) i = up i`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {n : ℕ}

/-- Symmetric tridiagonal matrix. -/
def tri (n : ℕ) (up d : ℕ → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then d i else if (j : ℕ) = i + 1 then up i else if (i : ℕ) = j + 1 then up j
    else 0

lemma tri_apply (up d : ℕ → F) (i j : Fin n) :
    tri n up d i j = (if (j : ℕ) = i then d i else 0) + (if (j : ℕ) = i + 1 then up i else 0)
      + (if (i : ℕ) = j + 1 then up j else 0) := by
  simp only [tri, Matrix.of_apply]
  split_ifs <;> first | (exfalso; omega) | rfl | simp

lemma tri_transpose (up d : ℕ → F) : (tri n up d)ᵀ = tri n up d := by
  ext i j
  simp only [Matrix.transpose_apply, tri_apply]
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · have h1 : (j : ℕ) ≠ i := by omega
    simp [h1, h, show (i : ℕ) ≠ j from by omega]
    by_cases h2 : (j : ℕ) = i + 1 <;> simp [h2, show ¬ ((i : ℕ) = i + 1 + 1) from by omega, add_comm]
  · have : i = j := Fin.ext h
    subst this
    simp
  · have h1 : (j : ℕ) ≠ i := by omega
    simp [h1, h, show (i : ℕ) ≠ j from by omega]
    by_cases h2 : (i : ℕ) = j + 1 <;> simp [h2, show ¬ ((j : ℕ) = j + 1 + 1) from by omega, add_comm]

lemma sum_ite_val_eq (m : ℕ) (x : Fin n → F) :
    ∑ j : Fin n, (if (j : ℕ) = m then x j else 0) = if h : m < n then x ⟨m, h⟩ else 0 := by
  by_cases h : m < n
  · rw [dif_pos h, Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro hjm; exact hj (Fin.ext hjm)
    · simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    have := j.2
    omega

/-- Row sums of a tridiagonal matrix against an arbitrary function. -/
theorem tri_sum (up d : ℕ → F) (a : Fin n) (g : ℕ → F) (gm lo : F)
    (h1 : (a : ℕ) + 1 = n → up a = 0) (h0 : (a : ℕ) = 0 → lo = 0)
    (hlo : 0 < (a : ℕ) → lo = up ((a : ℕ) - 1) ∧ gm = g ((a : ℕ) - 1)) :
    ∑ j : Fin n, tri n up d a j * g j = d a * g a + up a * g (a + 1) + lo * gm := by
  simp only [tri_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [sum_ite_val_eq (a : ℕ) (fun j => d a * g j), sum_ite_val_eq ((a : ℕ) + 1) (fun j => up a * g j)]
  have e3 : ∑ j : Fin n, (if (a : ℕ) = j + 1 then up j * g j else 0) =
      if 0 < (a : ℕ) then lo * gm else 0 := by
    rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
    · rw [if_neg (by omega)]
      exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
    · rw [if_pos h]
      obtain ⟨hl, hg⟩ := hlo h
      have : ∑ j : Fin n, (if (a : ℕ) = j + 1 then up j * g j else 0) =
          ∑ j : Fin n, (if (j : ℕ) = (a : ℕ) - 1 then up j * g j else 0) :=
        Finset.sum_congr rfl fun j _ => by
          congr 1; exact propext ⟨fun h2 => by omega, fun h2 => by omega⟩
      rw [this, sum_ite_val_eq ((a : ℕ) - 1) (fun j => up j * g j), dif_pos (by omega)]
      simp [hl, hg]
  rw [e3, dif_pos a.2]
  have h3 : (if 0 < (a : ℕ) then lo * gm else 0) = lo * gm := by
    split_ifs with h
    · rfl
    · rw [h0 (by omega), zero_mul]
  rw [h3]
  by_cases h : (a : ℕ) + 1 < n
  · rw [dif_pos h]
  · rw [dif_neg h, h1 (by have := a.2; omega)]
    simp

end CatalanCore
