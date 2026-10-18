module

public import CatalanCore.ThmA.Bispectral
public import CatalanCore.Linalg.Tridiag
public import Mathlib.Tactic.LinearCombination

/-!
# The intertwining `T C = C Y`

`Tmat K s` is `K × K`, `Ymat K s` is `s × s` (indexed by `y' = y - 1`), and `Cmat K s` is the
`K × s` Cauchy-type matrix `[1/(a+y)]`, `0 ≤ a < K`, `1 ≤ y ≤ s`.  Over any field in which the
integers `1, …, K+s` are nonzero, `T C = C Y`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {F : Type*} [Field F]

/-- The `K × K` tridiagonal matrix `T_{K,s}`. -/
def Tmat (F : Type*) [Field F] (K s : ℕ) : Matrix (Fin K) (Fin K) F :=
  tri K (fun a => bt (K : F) (s : F) (a : F)) (fun a => Td (K : F) (s : F) (a : F))

/-- The `s × s` tridiagonal matrix `Y_{K,s}`, with row `y'` standing for `y = y' + 1`. -/
def Ymat (F : Type*) [Field F] (K s : ℕ) : Matrix (Fin s) (Fin s) F :=
  tri s (fun y => bb (K : F) (s : F) ((y : F) + 1)) (fun y => Yd (K : F) (s : F) ((y : F) + 1))

/-- The `K × s` matrix `C_s = [1/(a+y)]`, column `y'` standing for `y = y' + 1`. -/
def Cmat (F : Type*) [Field F] (K s : ℕ) : Matrix (Fin K) (Fin s) F :=
  Matrix.of fun a y => 1 / ((a : ℕ) + ((y : ℕ) : F) + 1)

theorem Tmat_mul_Cmat (K s : ℕ) (hF : ∀ n : ℕ, 0 < n → n ≤ K + s → (n : F) ≠ 0) :
    Tmat F K s * Cmat F K s = Cmat F K s * Ymat F K s := by
  ext a y
  have ha := a.2
  have hy := y.2
  set A : F := ((a : ℕ) : F) with hA
  set Y : F := ((y : ℕ) : F) with hY
  have hL : (Tmat F K s * Cmat F K s) a y =
      Td (K : F) (s : F) A * (1 / (A + Y + 1)) + bt (K : F) (s : F) A * (1 / (A + 1 + Y + 1))
        + bt (K : F) (s : F) (A - 1) * (1 / (A - 1 + Y + 1)) := by
    rw [Matrix.mul_apply]
    have := tri_sum (n := K) (fun a => bt (K : F) (s : F) (a : F)) (fun a => Td (K : F) (s : F) (a : F))
      a (fun j => 1 / ((j : F) + Y + 1)) (1 / (A - 1 + Y + 1)) (bt (K : F) (s : F) (A - 1))
      (fun h => by
        have : (K : F) = A + 1 := by
          have h' := congrArg (Nat.cast (R := F)) h.symm
          simpa [hA] using h'
        simp only [bt, this]; ring)
      (fun h => by
        have : A = 0 := by rw [hA, h]; simp
        rw [this, zero_sub, bt_neg_one])
      (fun h => by
        refine ⟨?_, ?_⟩
        · rw [Nat.cast_sub (by omega)]; simp [hA]
        · rw [Nat.cast_sub (by omega)]; simp [hA])
    simpa [Tmat, Cmat, hA, hY, Nat.cast_add, add_assoc] using this
  have hR : (Cmat F K s * Ymat F K s) a y =
      Yd (K : F) (s : F) (Y + 1) * (1 / (A + Y + 1)) + bb (K : F) (s : F) (Y + 1) * (1 / (A + Y + 1 + 1))
        + bb (K : F) (s : F) Y * (1 / (A + Y)) := by
    have hT : ∀ j : Fin s, Ymat F K s j y = Ymat F K s y j := by
      intro j
      have := congrFun (congrFun (tri_transpose (n := s) (fun y : ℕ => bb (K : F) (s : F) ((y : F) + 1))
        (fun y : ℕ => Yd (K : F) (s : F) ((y : F) + 1))) y) j
      simpa [Matrix.transpose_apply, Ymat] using this
    have e : ∑ j, Cmat F K s a j * Ymat F K s j y = ∑ j, Ymat F K s y j * Cmat F K s a j :=
      Finset.sum_congr rfl fun j _ => by rw [hT j, mul_comm]
    rw [Matrix.mul_apply, e]
    have := tri_sum (n := s) (fun y => bb (K : F) (s : F) ((y : F) + 1))
      (fun y => Yd (K : F) (s : F) ((y : F) + 1)) y (fun j => 1 / (A + (j : F) + 1))
      (1 / (A + (Y - 1) + 1)) (bb (K : F) (s : F) Y)
      (fun h => by
        have : (s : F) = Y + 1 := by
          have h' := congrArg (Nat.cast (R := F)) h.symm
          simpa [hY] using h'
        simp only [bb, this]; ring)
      (fun h => by
        have : Y = 0 := by rw [hY, h]; simp
        rw [this, bb_zero])
      (fun h => by
        refine ⟨?_, ?_⟩
        · rw [Nat.cast_sub (by omega)]; simp [hY]
        · rw [Nat.cast_sub (by omega)]; simp [hY])
    simpa [Ymat, Cmat, hA, hY, Nat.cast_add, add_assoc] using this
  rw [hL, hR]
  have n1 : A + Y + 1 ≠ 0 := by
    have := hF ((a : ℕ) + (y : ℕ) + 1) (by omega) (by omega)
    simpa [hA, hY] using this
  have n2 : A + Y + 1 + 1 ≠ 0 := by
    have := hF ((a : ℕ) + (y : ℕ) + 1 + 1) (by omega) (by omega)
    simpa [hA, hY] using this
  by_cases hz : (a : ℕ) = 0 ∧ (y : ℕ) = 0
  · have hA0 : A = 0 := by rw [hA, hz.1]; simp
    have hY0 : Y = 0 := by rw [hY, hz.2]; simp
    have two : (2 : F) ≠ 0 := by
      have := hF 2 (by omega) (by omega)
      simpa using this
    have sp := special_entry (K : F) (s : F)
    rw [hA0, hY0]
    simp only [zero_add, zero_sub, bt_neg_one, bb_zero, zero_mul, add_zero]
    have h2 : (1 : F) + 1 = 2 := by norm_num
    rw [h2]
    field_simp
    linear_combination sp

  · have n3 : A + Y ≠ 0 := by
      have := hF ((a : ℕ) + (y : ℕ)) (by omega) (by omega)
      simpa [hA, hY] using this
    have m0 : A + (Y + 1) ≠ 0 := by rw [← add_assoc]; exact n1
    have m1 : A + (Y + 1) + 1 ≠ 0 := by rw [← add_assoc]; exact n2
    have m2 : A + (Y + 1) - 1 ≠ 0 := by
      have e : A + (Y + 1) - 1 = A + Y := by ring
      rw [e]; exact n3
    have key := bispectral (K : F) (s : F) A (Y + 1) m0 m1 m2
    rw [add_sub_cancel_right] at key
    linear_combination key

lemma Tmat_transpose (K s : ℕ) : (Tmat F K s)ᵀ = Tmat F K s := tri_transpose _ _
lemma Ymat_transpose (K s : ℕ) : (Ymat F K s)ᵀ = Ymat F K s := tri_transpose _ _

/-- (1b): `T` commutes with `N = C Cᵀ`. -/
theorem Tmat_commute_N (K s : ℕ) (hF : ∀ n : ℕ, 0 < n → n ≤ K + s → (n : F) ≠ 0) :
    Commute (Cmat F K s * (Cmat F K s)ᵀ) (Tmat F K s) := by
  have h := Tmat_mul_Cmat (F := F) K s hF
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Tmat_transpose, Ymat_transpose] at h'
  show _ * _ = _ * _
  calc Cmat F K s * (Cmat F K s)ᵀ * Tmat F K s
      = Cmat F K s * ((Cmat F K s)ᵀ * Tmat F K s) := by rw [Matrix.mul_assoc]
    _ = Cmat F K s * (Ymat F K s * (Cmat F K s)ᵀ) := by rw [h']
    _ = (Cmat F K s * Ymat F K s) * (Cmat F K s)ᵀ := by rw [Matrix.mul_assoc]
    _ = (Tmat F K s * Cmat F K s) * (Cmat F K s)ᵀ := by rw [h]
    _ = Tmat F K s * (Cmat F K s * (Cmat F K s)ᵀ) := by rw [Matrix.mul_assoc]

/-- (1b'): `Y` commutes with `M = Cᵀ C`. -/
theorem Ymat_commute_M (K s : ℕ) (hF : ∀ n : ℕ, 0 < n → n ≤ K + s → (n : F) ≠ 0) :
    Commute ((Cmat F K s)ᵀ * Cmat F K s) (Ymat F K s) := by
  have h := Tmat_mul_Cmat (F := F) K s hF
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Tmat_transpose, Ymat_transpose] at h'
  show _ * _ = _ * _
  calc (Cmat F K s)ᵀ * Cmat F K s * Ymat F K s
      = (Cmat F K s)ᵀ * (Cmat F K s * Ymat F K s) := by rw [Matrix.mul_assoc]
    _ = (Cmat F K s)ᵀ * (Tmat F K s * Cmat F K s) := by rw [h]
    _ = ((Cmat F K s)ᵀ * Tmat F K s) * Cmat F K s := by rw [Matrix.mul_assoc]
    _ = (Ymat F K s * (Cmat F K s)ᵀ) * Cmat F K s := by rw [h']
    _ = Ymat F K s * ((Cmat F K s)ᵀ * Cmat F K s) := by rw [Matrix.mul_assoc]

end CatalanCore.ThmA
