module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# General tridiagonal matrices over a commutative ring

`tri3 n sup d sub` is the `n × n` tridiagonal matrix with diagonal `d i`, superdiagonal
`M i (i+1) = sup i` and subdiagonal `M (i+1) i = sub i`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

variable {R : Type*} [CommRing R] {n : ℕ}

/-- General tridiagonal matrix. -/
def tri3 (n : ℕ) (sup d sub : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then d i else if (j : ℕ) = i + 1 then sup i else if (i : ℕ) = j + 1 then sub j
    else 0

lemma tri3_apply (sup d sub : ℕ → R) (i j : Fin n) :
    tri3 n sup d sub i j = (if (j : ℕ) = i then d i else 0) + (if (j : ℕ) = i + 1 then sup i else 0)
      + (if (i : ℕ) = j + 1 then sub j else 0) := by
  simp only [tri3, Matrix.of_apply]
  split_ifs <;> first | (exfalso; omega) | rfl | simp

lemma tri3_diag (sup d sub : ℕ → R) (i : Fin n) : tri3 n sup d sub i i = d i := by
  simp [tri3]

lemma tri3_super (sup d sub : ℕ → R) {i j : Fin n} (h : (j : ℕ) = i + 1) :
    tri3 n sup d sub i j = sup i := by
  have : (j : ℕ) ≠ i := by omega
  simp [tri3, this, h]

lemma tri3_sub (sup d sub : ℕ → R) {i j : Fin n} (h : (i : ℕ) = j + 1) :
    tri3 n sup d sub i j = sub j := by
  have h1 : (j : ℕ) ≠ i := by omega
  have h2 : (j : ℕ) ≠ i + 1 := by omega
  rw [tri3, Matrix.of_apply, if_neg h1, if_neg h2, if_pos h]

lemma tri3_zero (sup d sub : ℕ → R) {i j : Fin n} (h1 : (j : ℕ) ≠ i) (h2 : (j : ℕ) ≠ i + 1)
    (h3 : (i : ℕ) ≠ j + 1) : tri3 n sup d sub i j = 0 := by
  simp [tri3, h1, h2, h3]

lemma tri3_transpose (sup d sub : ℕ → R) : (tri3 n sup d sub)ᵀ = tri3 n sub d sup := by
  ext i j
  simp only [Matrix.transpose_apply, tri3_apply]
  split_ifs <;> first | (exfalso; omega) | (simp_all) | ring

lemma sum_ite_val_eq' (m : ℕ) (x : Fin n → R) :
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
theorem tri3_sum (sup d sub : ℕ → R) (a : Fin n) (g : ℕ → R) (gm lo : R)
    (h1 : (a : ℕ) + 1 = n → sup a = 0) (h0 : (a : ℕ) = 0 → lo = 0)
    (hlo : 0 < (a : ℕ) → lo = sub ((a : ℕ) - 1) ∧ gm = g ((a : ℕ) - 1)) :
    ∑ j : Fin n, tri3 n sup d sub a j * g j = d a * g a + sup a * g (a + 1) + lo * gm := by
  simp only [tri3_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [sum_ite_val_eq' (a : ℕ) (fun j => d a * g j), sum_ite_val_eq' ((a : ℕ) + 1) (fun j => sup a * g j)]
  have e3 : ∑ j : Fin n, (if (a : ℕ) = j + 1 then sub j * g j else 0) =
      if 0 < (a : ℕ) then lo * gm else 0 := by
    rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
    · rw [if_neg (by omega)]
      exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
    · rw [if_pos h]
      obtain ⟨hl, hg⟩ := hlo h
      have : ∑ j : Fin n, (if (a : ℕ) = j + 1 then sub j * g j else 0) =
          ∑ j : Fin n, (if (j : ℕ) = (a : ℕ) - 1 then sub j * g j else 0) :=
        Finset.sum_congr rfl fun j _ => by
          congr 1; exact propext ⟨fun h2 => by omega, fun h2 => by omega⟩
      rw [this, sum_ite_val_eq' ((a : ℕ) - 1) (fun j => sub j * g j), dif_pos (by omega)]
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

lemma tri3_guard (sup d sub : ℕ → R) :
    tri3 n sup d sub = tri3 n (fun i => if i + 1 < n then sup i else 0) d
      (fun i => if i + 1 < n then sub i else 0) := by
  ext i j
  simp only [tri3_apply]
  have hi := i.2
  have hj := j.2
  split_ifs <;> first | rfl | (exfalso; omega) | skip

/-- Row of a tridiagonal matrix applied to an `ℕ`-indexed vector, with explicit boundary guards. -/
theorem tri3_row (sup d sub : ℕ → R) (g : ℕ → R) (k : Fin n) :
    (tri3 n sup d sub *ᵥ (fun j : Fin n => g j)) k =
      d k * g k + (if (k : ℕ) + 1 < n then sup k * g (k + 1) else 0)
        + (if 0 < (k : ℕ) then sub ((k : ℕ) - 1) * g ((k : ℕ) - 1) else 0) := by
  have h := tri3_sum (n := n) (fun i => if i + 1 < n then sup i else 0) d sub k g
    (g ((k : ℕ) - 1)) (if 0 < (k : ℕ) then sub ((k : ℕ) - 1) else 0)
    (fun h => by simp [h]) (fun h => by simp [h])
    (fun h => by simp [h])
  rw [Matrix.mulVec, dotProduct]
  have e : tri3 n sup d sub = tri3 n (fun i => if i + 1 < n then sup i else 0) d sub := by
    ext i j
    simp only [tri3_apply]
    have hi := i.2
    have hj := j.2
    split_ifs <;> first | rfl | (exfalso; omega) | skip
  rw [e]
  rw [h]
  by_cases h1 : (k : ℕ) + 1 < n <;> by_cases h2 : 0 < (k : ℕ) <;> simp [h1, h2]

end CatalanCore.Bordered.Z1
