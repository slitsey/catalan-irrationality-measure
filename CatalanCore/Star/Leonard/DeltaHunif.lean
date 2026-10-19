module

public import CatalanCore.Star.Leonard.DeltaClosed
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Prop hDelta, step (5): the binomial Hankel determinant is the uniform-weight moment Hankel

`∑_a C(a,p) C(K-1-a,q) = C(K,p+q+1)`, so in the monic bases `a^{\underline p}` and
`∏_{k<q}(a-(K-1)+k)` the Gram matrix is `diag(p!) · [C(K,p+q+1)] · diag((-1)^q q!)`; hence
`det[∑_{a<K} a^{p+q}] = ∏ (-1)^q p! q! · det[C(K,p+q+1)]` (`hankel_basis_change` with `ρ = 1`).
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

lemma sum_choose_choose (K : ℕ) : ∀ p q : ℕ,
    ∑ a ∈ range K, a.choose p * (K - 1 - a).choose q = K.choose (p + q + 1) := by
  induction K with
  | zero => intro p q; simp
  | succ K ih =>
    intro p q
    rw [Finset.sum_range_succ]
    cases q with
    | zero =>
      have := ih p 0
      simp only [Nat.choose_zero_right, mul_one] at this ⊢
      rw [this, show p + 0 + 1 = p + 1 from rfl, Nat.choose_succ_succ' K p]
      ring
    | succ q' =>
      have h1 := ih p q'
      have h2 := ih p (q' + 1)
      have : ∑ a ∈ range K, a.choose p * (K + 1 - 1 - a).choose (q' + 1) =
          ∑ a ∈ range K, a.choose p * (K - 1 - a).choose q' +
            ∑ a ∈ range K, a.choose p * (K - 1 - a).choose (q' + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha' := Finset.mem_range.1 ha
        have e : K + 1 - 1 - a = (K - 1 - a) + 1 := by omega
        rw [e, Nat.choose_succ_succ']; ring
      rw [this, h1, h2]
      have e0 : K + 1 - 1 - K = 0 := by omega
      have e1 : p + (q' + 1) + 1 = p + q' + 1 + 1 := by omega
      rw [e0, Nat.choose_zero_succ, mul_zero, add_zero, e1, Nat.choose_succ_succ' K (p + q' + 1)]

section

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

lemma ff_cast (a : ℕ) : ∀ p : ℕ,
    ∏ k ∈ range p, ((a : F) - (k : F)) = (p.factorial : F) * (a.choose p : F) := by
  intro p
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    by_cases h : p ≤ a
    · have := Nat.choose_succ_right_eq a p
      have h2 : ((a - p : ℕ) : F) = (a : F) - (p : F) := Nat.cast_sub h
      have h3 : (a.choose (p + 1) : F) * ((p : F) + 1) = (a.choose p : F) * ((a : F) - p) := by
        rw [← h2]; exact_mod_cast this
      push_cast
      linear_combination (p.factorial : F) * (-h3)
    · have h1 : a.choose p = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : a.choose (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h1, h2]; simp

/-- `a(a-1)…(a-p+1)` as a monic polynomial -/
noncomputable def fallPoly (p : ℕ) : F[X] := ∏ k ∈ range p, (X + C (-(k : F)))

/-- `∏_{k<q} (a - (K-1) + k)` as a monic polynomial -/
noncomputable def psiK (K q : ℕ) : F[X] := ∏ k ∈ range q, (X + C ((k : F) - ((K : F) - 1)))

lemma fallPoly_monic (p : ℕ) : (fallPoly (F := F) p).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _

lemma fallPoly_natDegree (p : ℕ) : (fallPoly (F := F) p).natDegree = p := by
  unfold fallPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma psiK_monic (K q : ℕ) : (psiK (F := F) K q).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _

lemma psiK_natDegree (K q : ℕ) : (psiK (F := F) K q).natDegree = q := by
  unfold psiK
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma fallPoly_eval (p a : ℕ) :
    (fallPoly (F := F) p).eval (a : F) = (p.factorial : F) * (a.choose p : F) := by
  rw [← ff_cast, fallPoly, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun k _ => by simp; ring

lemma psiK_eval (K q a : ℕ) (ha : a < K) :
    (psiK (F := F) K q).eval (a : F) =
      (-1) ^ q * ((q.factorial : F) * ((K - 1 - a).choose q : F)) := by
  rw [← ff_cast, psiK, Polynomial.eval_prod]
  have : ∀ k ∈ range q, (Polynomial.eval (a : F) (X + C ((k : F) - ((K : F) - 1)))) =
      -(((K - 1 - a : ℕ) : F) - (k : F)) := by
    intro k _
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp; ring
  rw [Finset.prod_congr rfl this, Finset.prod_neg, Finset.card_range]

/-- **Step (5):** the moment Hankel determinant of the uniform weight on `{0..K-1}` equals
`∏ (-1)^p p! · ∏ q! · det[C(K,i+j+1)]`. -/
theorem Hunif_eq (K m : ℕ) :
    (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ((a : ℕ) : F) ^ ((p : ℕ) + (q : ℕ))).det =
      (∏ p : Fin m, ((-1 : F) ^ (p : ℕ) * ((p : ℕ).factorial : F))) *
        (∏ q : Fin m, (((q : ℕ).factorial : F))) * (HB K m).det := by
  have h1 := hankel_basis_change (fun _ : Fin K => (1 : F)) (fun p : Fin m => (X : F[X]) ^ (p : ℕ))
    (fun p : Fin m => (X : F[X]) ^ (p : ℕ)) (fun p => monic_X_pow _) (fun p => natDegree_X_pow _)
    (fun p => monic_X_pow _) (fun p => natDegree_X_pow _)
  have h2 := hankel_basis_change (fun _ : Fin K => (1 : F)) (fun p : Fin m => fallPoly (F := F) (p : ℕ))
    (fun q : Fin m => psiK (F := F) K (q : ℕ)) (fun p => fallPoly_monic _)
    (fun p => fallPoly_natDegree _) (fun p => psiK_monic _ _) (fun p => psiK_natDegree _ _)
  have e1 : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ((a : ℕ) : F) ^ ((p : ℕ) + (q : ℕ))) =
      Matrix.of fun (p q : Fin m) => ∑ a : Fin K, (1 : F) * ((X : F[X]) ^ (p : ℕ)).eval ((a : ℕ) : F) *
        ((X : F[X]) ^ (q : ℕ)).eval ((a : ℕ) : F) := by
    ext p q; simp [pow_add]
  have e2 : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, (1 : F) * (fallPoly (F := F) (p : ℕ)).eval ((a : ℕ) : F) *
        (psiK (F := F) K (q : ℕ)).eval ((a : ℕ) : F)) =
      Matrix.diagonal (fun p : Fin m => (((p : ℕ).factorial : F))) * HB K m *
        Matrix.diagonal (fun q : Fin m => (-1 : F) ^ (q : ℕ) * (((q : ℕ).factorial : F))) := by
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, HB]
    have : ∀ a : Fin K, (1 : F) * (fallPoly (F := F) (p : ℕ)).eval ((a : ℕ) : F) *
        (psiK (F := F) K (q : ℕ)).eval ((a : ℕ) : F) =
        ((p : ℕ).factorial : F) * ((-1 : F) ^ (q : ℕ) * ((q : ℕ).factorial : F)) *
          (((a : ℕ).choose p * (K - 1 - (a : ℕ)).choose q : ℕ) : F) := by
      intro a
      rw [fallPoly_eval, psiK_eval K q a a.2]; push_cast; ring
    simp only [this]
    rw [← Finset.mul_sum, ← Nat.cast_sum, Fin.sum_univ_eq_sum_range
      (fun a => a.choose p * (K - 1 - a).choose q) K, sum_choose_choose]
    ring
  calc (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ((a : ℕ) : F) ^ ((p : ℕ) + (q : ℕ))).det
      = (((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ * Matrix.diagonal (fun _ : Fin K => (1 : F))) *
          Vm K m).det := by rw [e1]; exact h1
    _ = (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, (1 : F) *
          (fallPoly (F := F) (p : ℕ)).eval ((a : ℕ) : F) *
          (psiK (F := F) K (q : ℕ)).eval ((a : ℕ) : F)).det := h2.symm
    _ = _ := by
      rw [e2, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
      simp only [Finset.prod_mul_distrib]
      ring

end

end CatalanCore.Star.Leonard
