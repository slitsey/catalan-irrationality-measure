module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Tactic

/-!
# Short translation-invariant polynomial ratios in prime characteristic

These lemmas use finite root counting and monic division only.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.PolynomialShift

variable {k : Type*} [Field k] {ell : ℕ} [Fact ell.Prime] [CharP k ell]

/-- A polynomial of degree below the characteristic fixed by translation is constant. -/
theorem periodic_lt_char_constant (f : k[X]) (hdeg : f.natDegree < ell)
    (hshift : f.comp (X + 1) = f) : f = C (f.eval 0) := by
  have heval : ∀ j : ℕ, f.eval (j : k) = f.eval 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := congrArg (fun q : k[X] => q.eval (j : k)) hshift
      simpa [eval_comp, Nat.cast_add, Nat.cast_one] using h.trans ih
  apply eq_of_natDegree_lt_card_of_eval_eq f (C (f.eval 0))
    (f := fun j : Fin ell => (j : k))
  · intro a b hab
    apply Fin.ext
    exact CharP.natCast_injOn_Iio k ell a.2 b.2 hab
  · intro j
    simpa using heval j
  · simpa using hdeg

/-- Below twice the characteristic, the only periodic polynomials are affine
in the Artin--Schreier polynomial. -/
theorem periodic_lt_two_char (f : k[X]) (hdeg : f.natDegree < 2 * ell)
    (hshift : f.comp (X + 1) = f) :
    ∃ a b : k, f = C a * (X ^ ell - X) + C b := by
  let D : k[X] := X ^ ell - X
  have hp : ell.Prime := Fact.out
  have hDdeg : D.natDegree = ell := by
    dsimp [D]
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hp.one_lt
  have hDmonic : D.Monic := by
    apply monic_X_pow_sub
    simpa using (show (1 : WithBot ℕ) < (ell : WithBot ℕ) by exact_mod_cast hp.one_lt)
  have hDshift : D.comp (X + 1) = D := by
    dsimp [D]
    simp only [sub_comp, pow_comp, X_comp, add_pow_char, one_pow]
    ring
  have hD1 : D ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hDdeg] at this
    simp at this
    exact hp.ne_zero this
  let q := f /ₘ D
  let r := f %ₘ D
  have hrdeg : r.natDegree < ell := by
    simpa only [r, hDdeg] using natDegree_modByMonic_lt f hDmonic hD1
  have hqdeg : q.natDegree < ell := by
    rw [show q = f /ₘ D from rfl, natDegree_divByMonic f hDmonic, hDdeg]
    omega
  have hdecomp : r + D * q = f := modByMonic_add_div f D
  have hcomp : r.comp (X + 1) + D * q.comp (X + 1) = f := by
    rw [← hDshift, ← mul_comp, ← add_comp, hdecomp, hshift]
  have hrcompdeg : (r.comp (X + 1)).degree < D.degree := by
    change (taylor (1 : k) r).degree < D.degree
    rw [degree_taylor]
    exact (degree_le_natDegree.trans_lt (by rw [degree_eq_natDegree hDmonic.ne_zero, hDdeg]; exact_mod_cast hrdeg))
  have hqr := div_modByMonic_unique (q.comp (X + 1)) (r.comp (X + 1)) hDmonic
    ⟨hcomp, hrcompdeg⟩
  have hqshift : q.comp (X + 1) = q := hqr.1.symm
  have hrshift : r.comp (X + 1) = r := hqr.2.symm
  obtain hqc := periodic_lt_char_constant q hqdeg hqshift
  obtain hrc := periodic_lt_char_constant r hrdeg hrshift
  refine ⟨q.eval 0, r.eval 0, ?_⟩
  rw [← hdecomp, hqc, hrc]
  simp only [eval_C]
  dsimp [D]
  ring

/-- A periodic rational function with denominator degree below the
characteristic has no proper denominator. -/
theorem dvd_of_cross_shift (F P : k[X]) (hP : P ≠ 0)
    (hPdeg : P.natDegree < ell)
    (hshift : F.comp (X + 1) * P = F * P.comp (X + 1)) : P ∣ F := by
  classical
  letI : GCDMonoid k[X] := EuclideanDomain.gcdMonoid _
  let g := GCDMonoid.gcd F P
  let A := F / g
  let B := P / g
  have hg : g ≠ 0 := gcd_ne_zero_of_right hP
  have hF : g * A = F := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left F P)
  have hPb : g * B = P := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right F P)
  have hB : B ≠ 0 := right_div_gcd_ne_zero hP
  have hab : IsCoprime A B := isCoprime_div_gcd_div_gcd hP
  have hgs : g.comp (X + 1) ≠ 0 := by
    change taylor (1 : k) g ≠ 0
    simpa using hg
  have hcross : A.comp (X + 1) * B = A * B.comp (X + 1) := by
    apply mul_left_cancel₀ (mul_ne_zero hgs hg)
    calc
      (g.comp (X + 1) * g) * (A.comp (X + 1) * B) =
          (g * A).comp (X + 1) * (g * B) := by rw [mul_comp]; ring
      _ = (g * A) * (g * B).comp (X + 1) := by rwa [hF, hPb]
      _ = (g.comp (X + 1) * g) * (A * B.comp (X + 1)) := by rw [mul_comp]; ring
  have hdiv : B ∣ B.comp (X + 1) := by
    apply hab.symm.dvd_of_dvd_mul_left
    rw [← hcross]
    exact dvd_mul_left B (A.comp (X + 1))
  have hBshift : B.comp (X + 1) = B := by
    apply (eq_of_dvd_of_natDegree_le_of_leadingCoeff hdiv ?_ ?_).symm
    · change (taylor (1 : k) B).natDegree ≤ B.natDegree
      simp
    · change B.leadingCoeff = (taylor (1 : k) B).leadingCoeff
      simp
  have hBd : B.natDegree < ell := by
    have hle := natDegree_le_of_dvd (show B ∣ P from ⟨g, by rw [← hPb]; ring⟩) hP
    exact hle.trans_lt hPdeg
  have hBc := periodic_lt_char_constant B hBd hBshift
  have hb : B.eval 0 ≠ 0 := by
    intro h
    apply hB
    rw [hBc, h, C_0]
  refine ⟨A * C (B.eval 0)⁻¹, ?_⟩
  calc
    F = g * A := hF.symm
    _ = g * A * (C (B.eval 0) * C (B.eval 0)⁻¹) := by simp [← C_mul, hb]
    _ = (g * B) * (A * C (B.eval 0)⁻¹) := by rw [hBc]; simp only [eval_C]; ring
    _ = P * (A * C (B.eval 0)⁻¹) := by rw [hPb]

/-- The rigidity interface used by the finite-field corank argument. -/
theorem exists_eq_mul_frobenius_sub (F P : k[X]) (hP : P ≠ 0)
    (hPdeg : P.natDegree < ell) (hFdeg : F.natDegree < 2 * ell)
    (hshift : F.comp (X + 1) * P = F * P.comp (X + 1)) :
    ∃ a b : k, F = P * (C a * (X ^ ell - X) + C b) := by
  by_cases hF : F = 0
  · exact ⟨0, 0, by simp [hF]⟩
  obtain ⟨Q, hQ⟩ := dvd_of_cross_shift F P hP hPdeg hshift
  have hPs : P.comp (X + 1) ≠ 0 := by
    change taylor (1 : k) P ≠ 0
    simpa using hP
  have hQs : Q.comp (X + 1) = Q := by
    apply mul_left_cancel₀ (mul_ne_zero hP hPs)
    calc
      (P * P.comp (X + 1)) * Q.comp (X + 1) = (P * Q).comp (X + 1) * P := by
        rw [mul_comp]; ring
      _ = (P * Q) * P.comp (X + 1) := by rwa [← hQ]
      _ = (P * P.comp (X + 1)) * Q := by ring
  have hQd : Q.natDegree < 2 * ell :=
    (natDegree_le_of_dvd (show Q ∣ F from ⟨P, by rw [hQ]; ring⟩) hF).trans_lt hFdeg
  obtain ⟨a, b, hab⟩ := periodic_lt_two_char Q hQd hQs
  exact ⟨a, b, by rw [hQ, hab]⟩

/-- A nonzero numerator with a double zero at a prime-field point cannot
give a periodic short ratio whose denominator is nonzero there. -/
theorem cross_shift_ne_zero (F P : k[X]) (hP : P ≠ 0) (hF : F ≠ 0)
    (hPdeg : P.natDegree < ell) (hFdeg : F.natDegree < 2 * ell)
    (u : k) (hu : u ^ ell = u) (hPu : P.eval u ≠ 0)
    (hFu : F.eval u = 0) (hFdu : F.derivative.eval u = 0) :
    F.comp (X + 1) * P - F * P.comp (X + 1) ≠ 0 := by
  intro hz
  have hcross := sub_eq_zero.mp hz
  obtain ⟨a, b, hab⟩ := exists_eq_mul_frobenius_sub F P hP hPdeg hFdeg hcross
  have hb : b = 0 := by
    have h := hFu
    rw [hab] at h
    simp only [eval_mul, eval_add, eval_C, eval_sub, eval_pow, eval_X, hu,
      sub_self, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hPu
  have hell : (ell : k) = 0 := (CharP.cast_eq_zero_iff k ell ell).2 dvd_rfl
  have ha : a = 0 := by
    have h := hFdu
    rw [hab, hb] at h
    simp [derivative_mul, derivative_add, derivative_sub, derivative_X_pow, hell, hu] at h
    exact h.resolve_left hPu
  apply hF
  simp [hab, ha, hb]

#print axioms exists_eq_mul_frobenius_sub
#print axioms cross_shift_ne_zero

end CatalanCore.PolynomialShift
