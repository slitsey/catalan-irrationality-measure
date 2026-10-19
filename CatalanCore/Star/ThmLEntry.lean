module

public import CatalanCore.Star.ThmLKernel
public import CatalanCore.Star.ThmLKrylov

/-!
# Star.ThmLEntry: explicit entries of the adjugate-Krylov matrix

For `H = ∑ₐ ωₐ ν(ζₐ)ν(ζₐ)ᵀ`, `G = ∑_b γ_b ν(ε_b)ν(ε_b)ᵀ`, the matrix `adjKry H G ν_s` has entries
`C[k,i] = ∑_{|A| = n-1-k} ∑_{|B| = k} (-1)^k ωᴬ γᴮ vsq(ζ,A) vsq(ε,B) ∏(ζ-ε)² ∏(s-ζ)∏(s-ε)
          · [X^i] ∏_A (X-ζ) ∏_B (X-ε)`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.ThmL

variable {F : Type*} [Field F]

/-- The ring hom `F → F[z][X]`. -/
noncomputable def cc : F →+* F[X][X] := (Polynomial.C : F[X] →+* F[X][X]).comp Polynomial.C

lemma cc_apply (a : F) : (cc a : F[X][X]) = Polynomial.C (Polynomial.C a) := rfl

lemma lhs_coeff {n : ℕ} (M : Matrix (Fin n) (Fin n) F[X]) (s : F) (i0 : Fin n) :
    ((fun i : Fin n => (cc s) ^ (i : ℕ)) ⬝ᵥ
        (adjugate (M.map (Polynomial.C : F[X] →+* F[X][X])) *ᵥ (fun i : Fin n => (X : F[X][X]) ^ (i : ℕ)))).coeff
      (i0 : ℕ) = ∑ i : Fin n, Polynomial.C (s ^ (i : ℕ)) * adjugate M i i0 := by
  have h : adjugate (M.map (Polynomial.C : F[X] →+* F[X][X])) =
      (adjugate M).map (Polynomial.C : F[X] →+* F[X][X]) :=
    (RingHom.map_adjugate (Polynomial.C : F[X] →+* F[X][X]) M).symm
  rw [h]
  simp only [dotProduct, mulVec, Matrix.map_apply, finsetSum_coeff]
  refine sum_congr rfl fun i _ => ?_
  rw [show cc s ^ (i : ℕ) = Polynomial.C (Polynomial.C (s ^ (i : ℕ))) by simp [cc_apply], coeff_C_mul,
    finsetSum_coeff]
  simp [coeff_C_mul_X_pow, Fin.val_inj]


lemma vsq_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {K : ℕ} (q : Fin K → R)
    (A : Finset (Fin K)) : vsq (fun a => f (q a)) A = f (vsq q A) := by
  simp [vsq, map_prod, map_pow, map_sub]

/-- The scalar coefficient of the `(A,B)` term. -/
noncomputable def entryVal {K r : ℕ} (ω ζ : Fin K → F) (γ ε : Fin r → F) (s : F)
    (A : Finset (Fin K)) (B : Finset (Fin r)) : F :=
  (-1) ^ B.card * (∏ a ∈ A, ω a) * (∏ b ∈ B, γ b) * vsq ζ A * vsq ε B
    * (∏ a ∈ A, ∏ b ∈ B, (ζ a - ε b) ^ 2) * (∏ a ∈ A, (s - ζ a)) * (∏ b ∈ B, (s - ε b))

/-- The `X`-polynomial of the `(A,B)` term. -/
noncomputable def entryPoly {K r : ℕ} (ζ : Fin K → F) (ε : Fin r → F)
    (A : Finset (Fin K)) (B : Finset (Fin r)) : F[X] :=
  (∏ a ∈ A, (X - Polynomial.C (ζ a))) * ∏ b ∈ B, (X - Polynomial.C (ε b))

lemma term_form {K r : ℕ} (ω ζ : Fin K → F) (γ ε : Fin r → F) (s : F)
    (A : Finset (Fin K)) (B : Finset (Fin r)) :
    (∏ a ∈ A, (Polynomial.C (X * Polynomial.C (ω a)) : F[X][X])) *
      (∏ b ∈ B, (Polynomial.C (-Polynomial.C (γ b)) : F[X][X])) *
      vsq (fun a => cc (ζ a)) A * vsq (fun b => cc (ε b)) B *
      (∏ a ∈ A, ∏ b ∈ B, (cc (ζ a) - cc (ε b)) ^ 2) *
      (∏ a ∈ A, (((X : F[X][X]) - cc (ζ a)) * (cc s - cc (ζ a)))) *
      (∏ b ∈ B, (((X : F[X][X]) - cc (ε b)) * (cc s - cc (ε b))))
    = Polynomial.C (X ^ A.card * Polynomial.C (entryVal ω ζ γ ε s A B)) *
        (entryPoly ζ ε A B).map (Polynomial.C : F →+* F[X]) := by
  have h1 : ∏ a ∈ A, (Polynomial.C (X * Polynomial.C (ω a)) : F[X][X])
      = Polynomial.C (X ^ A.card * Polynomial.C (∏ a ∈ A, ω a)) := by
    rw [← map_prod, prod_mul_distrib, prod_const, ← map_prod]
  have h2 : ∏ b ∈ B, (Polynomial.C (-Polynomial.C (γ b)) : F[X][X])
      = Polynomial.C ((-1) ^ B.card * Polynomial.C (∏ b ∈ B, γ b)) := by
    rw [← map_prod]
    congr 1
    have e : ∀ b ∈ B, -(Polynomial.C (γ b) : F[X]) = (-1) * Polynomial.C (γ b) := fun b _ => by ring
    rw [prod_congr rfl e, prod_mul_distrib, prod_const, map_prod]
  have h5 : ∀ {ι : Type} (T : Finset ι) (z : ι → F),
      ∏ a ∈ T, (((X : F[X][X]) - cc (z a)) * (cc s - cc (z a)))
        = cc (∏ a ∈ T, (s - z a)) * ∏ a ∈ T, ((X : F[X][X]) - cc (z a)) := by
    intro ι T z
    rw [prod_mul_distrib, mul_comm, map_prod]
    simp [map_sub]
  have h5a := h5 A ζ
  have h5b := h5 B ε
  have h4 : (∏ a ∈ A, ∏ b ∈ B, (cc (ζ a) - cc (ε b)) ^ 2)
      = cc (∏ a ∈ A, ∏ b ∈ B, (ζ a - ε b) ^ 2) := by
    simp [map_prod, map_pow, map_sub]
  have h7 : (entryPoly ζ ε A B).map (Polynomial.C : F →+* F[X])
      = (∏ a ∈ A, ((X : F[X][X]) - cc (ζ a))) * ∏ b ∈ B, ((X : F[X][X]) - cc (ε b)) := by
    simp [entryPoly, Polynomial.map_mul, Polynomial.map_prod, cc_apply]
  rw [h1, h2, h5a, h5b, h4, h7, vsq_map cc ζ A, vsq_map cc ε B]
  simp only [entryVal, cc_apply, map_mul, map_pow, map_neg, map_one, map_prod, map_sub]
  ring


lemma coeff_term {K r : ℕ} (ω ζ : Fin K → F) (γ ε : Fin r → F) (s : F)
    (A : Finset (Fin K)) (B : Finset (Fin r)) (i N : ℕ) :
    ((Polynomial.C (X ^ A.card * Polynomial.C (entryVal ω ζ γ ε s A B)) *
        (entryPoly ζ ε A B).map (Polynomial.C : F →+* F[X])).coeff i).coeff N
      = if A.card = N then entryVal ω ζ γ ε s A B * (entryPoly ζ ε A B).coeff i else 0 := by
  rw [coeff_C_mul, coeff_map, show (X ^ A.card * Polynomial.C (entryVal ω ζ γ ε s A B) : F[X]) *
    Polynomial.C ((entryPoly ζ ε A B).coeff i) = Polynomial.C (entryVal ω ζ γ ε s A B *
    (entryPoly ζ ε A B).coeff i) * X ^ A.card by rw [map_mul]; ring, coeff_C_mul_X_pow]
  by_cases h : A.card = N
  · simp [h]
  · have h' : N ≠ A.card := fun e => h e.symm
    simp [h, h']

theorem entry_formula {K r n : ℕ} (hn : 1 ≤ n) (ω ζ : Fin K → F) (γ ε : Fin r → F) (s : F)
    (k i : Fin n) :
    adjKry (Matrix.of fun a b : Fin n => ∑ x, ω x * ζ x ^ ((a : ℕ) + b))
        (Matrix.of fun a b : Fin n => ∑ x, γ x * ε x ^ ((a : ℕ) + b)) (fun j => s ^ (j : ℕ)) k i
      = ∑ A ∈ powersetCard (n - 1 - k) (univ : Finset (Fin K)),
        ∑ B ∈ powersetCard k (univ : Finset (Fin r)),
          entryVal ω ζ γ ε s A B * (entryPoly ζ ε A B).coeff i := by
  set Hm : Matrix (Fin n) (Fin n) F := Matrix.of fun a b : Fin n => ∑ x, ω x * ζ x ^ ((a : ℕ) + b)
  set Gm : Matrix (Fin n) (Fin n) F := Matrix.of fun a b : Fin n => ∑ x, γ x * ε x ^ ((a : ℕ) + b)
  have hM : (Matrix.of fun a b : Fin n =>
      ∑ x, (Polynomial.C (X * Polynomial.C (ω x)) : F[X][X]) * (cc (ζ x)) ^ ((a : ℕ) + b)
      + ∑ y, (Polynomial.C (-Polynomial.C (γ y)) : F[X][X]) * (cc (ε y)) ^ ((a : ℕ) + b))
      = (zpen Hm Gm).map (Polynomial.C : F[X] →+* F[X][X]) := by
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.of_apply, Matrix.map_apply, zpen, Hm, Gm, map_sub, map_sum, map_mul, map_pow, map_neg, cc_apply, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => by ring
    · rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun x _ => by ring
  have key := adj_kernel hn (fun x => cc (ζ x)) (fun x => (Polynomial.C (X * Polynomial.C (ω x)) : F[X][X]))
    (fun y => cc (ε y)) (fun y => (Polynomial.C (-Polynomial.C (γ y)) : F[X][X])) X (cc s)
  rw [hM] at key
  simp only [term_form] at key
  have hc := congrArg (fun p : F[X][X] => p.coeff (i : ℕ)) key
  rw [lhs_coeff] at hc
  rw [adjKry_apply]
  have e : (∑ r, Polynomial.C ((fun j : Fin n => s ^ (j : ℕ)) r) * adjugate (zpen Hm Gm) r i)
      = _ := hc
  rw [e]
  simp only [finsetSum_coeff]
  have hk := k.2
  simp only [powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun A _ => ?_
  by_cases hA : A.card = n - 1 - k
  · rw [if_pos hA]
    refine sum_congr rfl fun B _ => ?_
    by_cases hB : B.card = k
    · have c : A.card + B.card = n - 1 := by omega
      rw [if_pos c, coeff_term, if_pos hA, if_pos hB]
    · have c : ¬ (A.card + B.card = n - 1) := by omega
      rw [if_neg c, if_neg hB]; simp
  · rw [if_neg hA]
    refine sum_eq_zero fun B _ => ?_
    by_cases c : A.card + B.card = n - 1
    · rw [if_pos c, coeff_term, if_neg hA]
    · rw [if_neg c]; simp

end CatalanCore.Star.ThmL
