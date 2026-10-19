module

public import CatalanCore.Linalg.KrylovV
public import CatalanCore.Linalg.KrylovBorder
public import CatalanCore.Linalg.Cauchy

/-!
# Bordered Krylov determinants (package H3, part 2)

* `bmat_cauchy_det` (L4): `det [W_b | c_{y_1} … c_{y_n}]` for Cauchy columns is the Cauchy
  determinant.
* `bkdet_mul_transpose` (L5, bordering): `u(E Cᵀ, v) = det [W | v | E] · u_{y-space}(Cᵀ E, Cᵀ v)`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F]

/-- **L4.** The bordered matrix of Cauchy columns is a Cauchy matrix. -/
theorem bmat_cauchy_det {m n : ℕ} (θ : F) (bs : Fin m → F) (ys : Fin n → F)
    (hne : ∀ (a : Fin (m + n)) (j : Fin (m + n)),
      θ + ((a : ℕ) : F) + Fin.addCases bs ys j ≠ 0) :
    (bmat (Matrix.of fun (a : Fin (m + n)) (i : Fin m) => 1 / (θ + ((a : ℕ) : F) + bs i))
        (Matrix.of fun (a : Fin (m + n)) (k : Fin n) => 1 / (θ + ((a : ℕ) : F) + ys k))).det =
      (∏ i : Fin (m + n), ∏ j ∈ Finset.Ioi i,
          ((((j : ℕ) : F) - ((i : ℕ) : F)) * (Fin.addCases bs ys j - Fin.addCases bs ys i))) /
        ∏ i : Fin (m + n), ∏ j : Fin (m + n),
          (θ + ((i : ℕ) : F) + Fin.addCases bs ys j) := by
  have h : bmat (Matrix.of fun (a : Fin (m + n)) (i : Fin m) => 1 / (θ + ((a : ℕ) : F) + bs i))
        (Matrix.of fun (a : Fin (m + n)) (k : Fin n) => 1 / (θ + ((a : ℕ) : F) + ys k)) =
      Matrix.of fun (a j : Fin (m + n)) =>
        1 / ((θ + ((a : ℕ) : F)) + Fin.addCases bs ys j) := by
    ext a j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [bmat, add_assoc]
  rw [h, cauchy_det (fun a : Fin (m + n) => θ + ((a : ℕ) : F)) (Fin.addCases bs ys)
    (fun a j => by simpa [add_assoc] using hne a j)]
  congr 1
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1; ring

/-- **L5 (bordering).** -/
theorem bkdet_mul_transpose {m n' : ℕ} (W : Matrix (Fin (m + (n' + 1))) (Fin m) F)
    (E C : Matrix (Fin (m + (n' + 1))) (Fin n') F) (v : Fin (m + (n' + 1)) → F) :
    bkdet W (E * Cᵀ) v =
      (bmat W (Matrix.of fun i j => Fin.cases (v i) (fun j' => E i j') j)).det *
        kdet (Cᵀ * E) (Cᵀ *ᵥ v) := by
  have hpow : ∀ k : ℕ, (E * Cᵀ) ^ (k + 1) = E * (Cᵀ * E) ^ k * Cᵀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  have h : krylovE (E * Cᵀ) v =
      (Matrix.of fun i j => Fin.cases (v i) (fun j' => E i j') j) *
        diagOne (krylov (Cᵀ * E) (Cᵀ *ᵥ v)) := by
    ext i k
    refine Fin.cases ?_ (fun k' => ?_) k
    · simp [krylovE, diagOne, Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [krylovE, Matrix.of_apply, Fin.val_succ, hpow, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      simp [diagOne, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct, krylov_apply]
  have := det_bmat_comb W (Matrix.of fun i j => Fin.cases (v i) (fun j' => E i j') j)
    (diagOne (krylov (Cᵀ * E) (Cᵀ *ᵥ v))) 0
  rw [bkdet, h]
  simpa [det_diagOne, kdet, mul_comm] using this

end CatalanCore
