module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/PolynomialData.lean
Original SHA256: 04c7f185382d215d021ad126381f5035fa7fed9292fc3de3030ea25115474ce7
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.PolynomialNorm
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Order.Fin.Basic

@[expose] public section

namespace CatalanMeasure.Refinement

open Polynomial

def rationalHorner : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, x => a + x * rationalHorner as x

def coefficientAt (as : List ℚ) (n : ℕ) : ℚ := as[n]?.getD 0

theorem polynomialFromCoeffs_eval (as : List ℚ) (x : ℚ) :
    (polynomialFromCoeffs as).eval x = rationalHorner as x := by
  induction as with
  | nil => simp [polynomialFromCoeffs, rationalHorner]
  | cons a as ih => simp [polynomialFromCoeffs, rationalHorner, ih]

theorem polynomialFromCoeffs_eval_map_real (as : List ℚ) (x : ℚ) :
    ((polynomialFromCoeffs as).map (algebraMap ℚ ℝ)).eval (x : ℝ) =
      (rationalHorner as x : ℝ) := by
  induction as with
  | nil => simp [polynomialFromCoeffs, rationalHorner]
  | cons a as ih => simp [polynomialFromCoeffs, rationalHorner, ih]

theorem polynomialFromCoeffs_coeff (as : List ℚ) (n : ℕ) :
    (polynomialFromCoeffs as).coeff n = coefficientAt as n := by
  induction as generalizing n with
  | nil => simp [polynomialFromCoeffs, coefficientAt]
  | cons a as ih =>
    cases n with
    | zero => simp [polynomialFromCoeffs, coefficientAt]
    | succ n => simp [polynomialFromCoeffs, coefficientAt, coeff_X_mul, ih]

theorem polynomialFromCoeffs_natDegree_le (as : List ℚ) (n : ℕ)
    (hlen : as.length ≤ n + 1) : (polynomialFromCoeffs as).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [polynomialFromCoeffs_coeff]
  have hli : as.length ≤ i := by omega
  simp [coefficientAt, List.getElem?_eq_none hli]

theorem polynomialFromCoeffs_natDegree_eq (as : List ℚ) (n : ℕ)
    (hlen : as.length ≤ n + 1) (hcoeff : coefficientAt as n ≠ 0) :
    (polynomialFromCoeffs as).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomialFromCoeffs_natDegree_le as n hlen)
  rwa [polynomialFromCoeffs_coeff]

theorem polynomialFromCoeffs_leadingCoeff (as : List ℚ) (n : ℕ)
    (hlen : as.length ≤ n + 1) (hcoeff : coefficientAt as n ≠ 0) :
    (polynomialFromCoeffs as).leadingCoeff = coefficientAt as n := by
  rw [Polynomial.leadingCoeff, polynomialFromCoeffs_natDegree_eq as n hlen hcoeff,
    polynomialFromCoeffs_coeff]

theorem ordered_intervals_separated {n : ℕ} {left right : Fin (n + 1) → ℚ}
    (hord : ∀ i, left i ≤ right i)
    (hadj : ∀ i : Fin n, right i.castSucc ≤ left i.succ) :
    ∀ i j, i < j → right i ≤ left j := by
  have hmono : Monotone left := Fin.monotone_iff_le_succ.mpr
    (fun i => (hord i.castSucc).trans (hadj i))
  intro i j hij
  have hi : i.val < n := by have := j.isLt; exact Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ this)
  let k : Fin n := ⟨i.val, hi⟩
  have hk : k.castSucc = i := Fin.ext rfl
  have hkj : k.succ ≤ j := by change i.val + 1 ≤ j.val; exact hij
  rw [← hk]
  exact (hadj k).trans (hmono hkj)

end CatalanMeasure.Refinement

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.rationalHorner
#print axioms CatalanMeasure.Refinement.coefficientAt
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs_eval
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs_eval_map_real
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs_coeff
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs_natDegree_le
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs_natDegree_eq
#print axioms CatalanMeasure.Refinement.polynomialFromCoeffs_leadingCoeff
#print axioms CatalanMeasure.Refinement.ordered_intervals_separated
