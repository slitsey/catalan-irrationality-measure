module

public import CatalanCore.Bordered.Z1.CommuteMat

/-!
# Z1.2 (end): lift to `ℚ[X]`; Z1.4 products of off-diagonal entries.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Bordered.Z1

section Map

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

lemma tri3_map {n : ℕ} (f : R →+* S) (sup d sub : ℕ → R) :
    (tri3 n sup d sub).map f = tri3 n (fun k => f (sup k)) (fun k => f (d k)) (fun k => f (sub k)) := by
  ext i j
  simp only [Matrix.map_apply, tri3, Matrix.of_apply]
  split_ifs <;> simp

lemma Dq_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ x : R) : f (Dq s m θ x) = Dq s m (f θ) (f x) := by
  simp [Dq, map_ofNat, map_natCast]

lemma Xp_map (f : R →ₐ[ℚ] S) (s m : ℕ) (θ : R) : (Xp s m θ).map f = Xp s m (f θ) := by
  unfold Xp
  refine (tri3_map (f : R →+* S) _ _ _).trans ?_
  congr 1
  · funext k; simp [qc_map, map_ofNat, map_natCast]
  · funext k; simp [Dq_map]
  · funext k; simp [qc_map, map_ofNat, map_natCast]

end Map

lemma Tmat_eval (s m : ℕ) (q : ℚ) :
    (Tmat s m (X : ℚ[X])).map (Polynomial.eval q) = Tmat s m q := by
  have := Tmat_map (Polynomial.aeval q) s m (X : ℚ[X])
  rw [Polynomial.aeval_X] at this
  simpa [Polynomial.coe_aeval_eq_eval] using this

lemma Xp_eval (s m : ℕ) (q : ℚ) :
    (Xp s m (X : ℚ[X])).map (Polynomial.eval q) = Xp s m q := by
  have := Xp_map (Polynomial.aeval q) s m (X : ℚ[X])
  rw [Polynomial.aeval_X] at this
  simpa [Polynomial.coe_aeval_eq_eval] using this

/-- **Z1.2: `[T, X′] = 0` in `ℚ[X]`.** -/
theorem Tmat_commute_Xp (s m : ℕ) :
    Tmat s m (X : ℚ[X]) * Xp s m (X : ℚ[X]) = Xp s m (X : ℚ[X]) * Tmat s m (X : ℚ[X]) := by
  refine Matrix.ext fun i j => ?_
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Ioi_infinite (0 : ℚ)).mono ?_
  intro q hq
  have hc := Tmat_commute_Xp_rat s m q hq
  have e1 : ∀ A B : Matrix (Fin s) (Fin s) ℚ[X],
      Polynomial.eval q ((A * B) i j) = ((A.map (Polynomial.eval q)) * (B.map (Polynomial.eval q))) i j := by
    intro A B
    simp [Matrix.mul_apply, Polynomial.eval_finset_sum]
  show Polynomial.eval q (((Tmat s m (X : ℚ[X])) * Xp s m (X : ℚ[X])) i j) =
    Polynomial.eval q (((Xp s m (X : ℚ[X])) * Tmat s m (X : ℚ[X])) i j)
  rw [e1, e1, Tmat_eval, Xp_eval, hc]

/-! ### Z1.4 / irreducibility: products of the off-diagonal entries -/

lemma pj_ne (s m k : ℕ) (hk : k + 1 < s) : pj s m k ≠ 0 := by
  unfold pj
  exact div_ne_zero (PiX_ne s m _ (by omega)) (PiX_ne s m _ (by omega))

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `X′_{k,k+1} X′_{k+1,k}` in closed form. -/
theorem Xp_up_mul_low (s m k : ℕ) (θ : R) (hk : k + 1 < s) :
    (-(((k : R) + 1) * ((k : R) + 1 + θ) * ((k : R) + 1 + θ + ((s + m : ℕ) : R)) * ((s : R) - k - 1))
        * qc (pj s m k)) *
      (-(((k : R) + 1) * ((k : R) + 1 + θ) * ((s : R) + 2 * m - k - 1)
        * (((s + m : ℕ) : R) + θ + k + 1)) * qc (1 / pj s m k)) =
    ((k : R) + 1) ^ 2 * ((k : R) + 1 + θ) ^ 2 * ((s : R) - k - 1) * ((s : R) + 2 * m - k - 1)
      * ((k : R) + 1 + θ + ((s + m : ℕ) : R)) ^ 2 := by
  have h : (qc (pj s m k) : R) * qc (1 / pj s m k) = 1 := by
    simp only [qc, ← map_mul]
    rw [mul_one_div_cancel (pj_ne s m k hk)]; simp
  linear_combination (((k : R) + 1) ^ 2 * ((k : R) + 1 + θ) ^ 2 * ((s : R) - k - 1) * ((s : R) + 2 * m - k - 1)
      * ((k : R) + 1 + θ + ((s + m : ℕ) : R)) ^ 2) * h

end CatalanCore.Bordered.Z1
