module

public import CatalanCore.Star.ThmLTerm

/-!
# Star.ThmLDeg: degree bounds for the summands `entryVal * [X^i] entryPoly`
-/

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Star.ThmL

section
variable {K r : ℕ} (m S : ℕ) (e : Fin r → ℤ)

/-- Order of the `(A,B)` term (before the `X^i` coefficient). -/
def baseOrd (K m : ℕ) (a b : ℕ) : ℤ := -(2 * m * a : ℤ) + 2 * K * b - 2 * a * b - a

lemma entryPoly_eq (ζ : Fin K → LS) (ε : Fin r → LS) (A : Finset (Fin K)) (B : Finset (Fin r)) :
    entryPoly ζ ε A B
      = ∏ q ∈ A.disjSum B, (X - Polynomial.C (Sum.elim ζ ε q)) := by
  rw [prod_disjSum]; rfl

lemma entryPoly_bound (A : Finset (Fin K)) (B : Finset (Fin r)) (i : ℕ) (hi : i ≤ A.card + B.card) :
    OrdGe (-(min (A.card : ℤ) ((A.card : ℤ) + B.card - i)))
      ((entryPoly (fun a : Fin K => -(theta + ((a : ℕ) : LS))) (fun b => ((e b : ℤ) : LS)) A B).coeff i) := by
  rw [entryPoly_eq]
  have := coeff_prod_bound (Sum.elim (fun a : Fin K => -(theta + ((a : ℕ) : LS)))
      (fun b : Fin r => ((e b : ℤ) : LS))) (Sum.elim (fun _ => 1) (fun _ => 0)) (A.disjSum B)
    (by rintro (q | q) _ <;> simp) (by
      rintro (q | q) hq
      · simpa using (hl_zeta q).1
      · simpa using (hasLead_intCast (e q)).1) i (by simpa using hi)
  simpa [sum_disjSum] using this

lemma entryPoly_lead (A : Finset (Fin K)) (B : Finset (Fin r)) (i : ℕ) (hi : i + A.card = A.card + B.card) :
    HasLead (-(A.card : ℤ)) 1
      ((entryPoly (fun a : Fin K => -(theta + ((a : ℕ) : LS))) (fun b => ((e b : ℤ) : LS)) A B).coeff i) := by
  rw [entryPoly_eq]
  have := coeff_prod_lead (Sum.elim (fun a : Fin K => -(theta + ((a : ℕ) : LS)))
      (fun b : Fin r => ((e b : ℤ) : LS))) (Sum.elim (fun _ => 1) (fun _ => 0)) (A.disjSum B)
    (by rintro (q | q) _ <;> simp) (by
      rintro (q | q) hq
      · simpa using (hl_zeta q).1
      · simpa using (hasLead_intCast (e q)).1)
    (by rintro (q | q) hq h
        · simpa using hl_zeta q
        · simp at h) i (by simpa [sum_disjSum] using hi)
  simpa [sum_disjSum] using this

end
end CatalanCore.Star.ThmL
