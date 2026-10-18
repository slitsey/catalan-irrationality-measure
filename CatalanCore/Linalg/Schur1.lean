module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# One-step Schur complement determinant

For `B : (n+1) × (n+1)` over a field with `B 0 0 ≠ 0`:
`det B = B 0 0 * det (B' - c r / B 0 0)`, where `c` is the first column and `r` the first row.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {n : ℕ}

/-- `diag(a) ⊕ S`. -/
def diagBlock (a : F) (S : Matrix (Fin n) (Fin n) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.of fun j k => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun k' => Fin.cases 0 (fun j' => S j' k') j) k

lemma det_diagBlock (a : F) (S : Matrix (Fin n) (Fin n) F) : (diagBlock a S).det = a * S.det := by
  rw [Matrix.det_succ_column_zero]
  simp [diagBlock, Fin.sum_univ_succ]
  left
  congr 1

/-- Unit lower triangular factor. -/
def schurL (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.of fun i k => if k = 0 then (if i = 0 then 1 else B i 0 / B 0 0) else (if i = k then 1 else 0)

/-- Unit upper triangular factor. -/
def schurR (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.of fun j k => if j = 0 then (if k = 0 then 1 else B 0 k / B 0 0) else (if j = k then 1 else 0)

/-- The Schur complement. -/
def schurS (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => B i.succ j.succ - B i.succ 0 * B 0 j.succ / B 0 0

theorem det_eq_schur (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0) :
    B.det = B 0 0 * (schurS B).det := by
  have hL : (schurL B).det = 1 := by
    have : (schurL B).IsLowerTriangular := by
      intro i k hik
      simp only [schurL, Matrix.of_apply]
      have hk : k ≠ 0 := fun h0 => by subst h0; exact absurd hik (Fin.not_lt_zero _)
      have hik' : i ≠ k := ne_of_lt hik
      simp [hk, hik']
    rw [Matrix.det_of_isLowerTriangular _ this]
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = 0 <;> simp [schurL, hi]
  have hR : (schurR B).det = 1 := by
    have : (schurR B).IsUpperTriangular := by
      intro j k hjk
      simp only [schurR, Matrix.of_apply]
      have hj : j ≠ 0 := fun h0 => by subst h0; exact absurd hjk (Fin.not_lt_zero _)
      have hjk' : j ≠ k := ne_of_gt hjk
      simp [hj, hjk']
    rw [Matrix.det_of_isUpperTriangular this]
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = 0 <;> simp [schurR, hi]
  have hB : B = schurL B * diagBlock (B 0 0) (schurS B) * schurR B := by
    ext i k
    simp only [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun k' => ?_) k
    · simp [schurL, schurR, diagBlock, Fin.sum_univ_succ]
    · simp [schurL, schurR, diagBlock, Fin.sum_univ_succ, schurS, (Fin.succ_ne_zero _).symm]
      field_simp
    · simp [schurL, schurR, diagBlock, Fin.sum_univ_succ, schurS]
      field_simp
    · simp [schurL, schurR, diagBlock, Fin.sum_univ_succ, schurS]
      field_simp
      ring
  have hd := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_mul, hL, hR, det_diagBlock, one_mul, mul_one] at hd
  exact hd

end CatalanCore
