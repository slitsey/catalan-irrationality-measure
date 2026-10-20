module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Monomial
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! # Generic three-constraint corank bound

This module has no frame-specific arithmetic. A common polynomial divisor of a
shift Wronskian, one evaluation, and a degree bound force the polynomial kernel
to have dimension at most three.
-/

open Polynomial Module

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k]

/-- The forward-shift cross Wronskian. -/
noncomputable def wronskian (F P : k[X]) : k[X] :=
  F.comp (X + 1) * P - F * P.comp (X + 1)

lemma natDegree_shift (P : k[X]) : (P.comp (X + 1)).natDegree = P.natDegree := by
  rw [natDegree_comp]
  simp

lemma leadingCoeff_shift (P : k[X]) :
    (P.comp (X + 1)).leadingCoeff = P.leadingCoeff := by
  have h : (X + 1 : k[X]).Monic := by simpa using monic_X_add_C (1 : k)
  rw [leadingCoeff_comp (by simp), h.leadingCoeff, one_pow, mul_one]

lemma natDegree_wronskian_lt (F P : k[X]) (hW : wronskian F P ≠ 0) :
    (wronskian F P).natDegree < F.natDegree + P.natDegree := by
  have hF : F ≠ 0 := by intro h; apply hW; simp [wronskian, h]
  have hP : P ≠ 0 := by intro h; apply hW; simp [wronskian, h]
  have hsF : F.comp (X + 1) ≠ 0 := by
    intro h
    have hdeg := leadingCoeff_shift F
    rw [h, leadingCoeff_zero] at hdeg
    exact hF (leadingCoeff_eq_zero.mp hdeg.symm)
  have hsP : P.comp (X + 1) ≠ 0 := by
    intro h
    have hdeg := leadingCoeff_shift P
    rw [h, leadingCoeff_zero] at hdeg
    exact hP (leadingCoeff_eq_zero.mp hdeg.symm)
  have hd : (F.comp (X + 1) * P).natDegree = F.natDegree + P.natDegree := by
    rw [natDegree_mul hsF hP, natDegree_shift]
  have hd' : (F * P.comp (X + 1)).natDegree = F.natDegree + P.natDegree := by
    rw [natDegree_mul hF hsP, natDegree_shift]
  have hlt := degree_sub_lt_left
    (p := F.comp (X + 1) * P) (q := F * P.comp (X + 1))
    (by rw [degree_eq_natDegree (mul_ne_zero hsF hP),
      degree_eq_natDegree (mul_ne_zero hF hsP), hd, hd'])
    (mul_ne_zero hsF hP)
    (by simp only [leadingCoeff_mul, leadingCoeff_shift])
  apply (natDegree_lt_iff_degree_lt hW).2
  simpa only [wronskian, degree_eq_natDegree (mul_ne_zero hsF hP), hd] using hlt

/-- A divisor of at least the polynomial's degree cannot lose a root at which
it is a unit. -/
lemma eq_zero_of_dvd_of_natDegree_le_of_eval (Q W : k[X]) (s : k)
    (hQ : Q.eval s ≠ 0) (hdvd : Q ∣ W)
    (hdeg : W.natDegree ≤ Q.natDegree) (heval : W.eval s = 0) : W = 0 := by
  by_contra hW
  have hQ0 : Q ≠ 0 := by intro h; exact hQ (by simp [h])
  obtain ⟨A, rfl⟩ := hdvd
  have hA : A ≠ 0 := by intro h; exact hW (by simp [h])
  rw [natDegree_mul hQ0 hA] at hdeg
  have hAd : A.natDegree = 0 := by omega
  have heq := eq_C_of_natDegree_eq_zero hAd
  rw [heq, eval_mul, eval_C] at heval
  have hz : A.coeff 0 = 0 := (mul_eq_zero.mp heval).resolve_left hQ
  apply hW
  rw [heq, hz, C_0, mul_zero]

/-- The generic dimension bound behind the finite-field corank argument.
The instance supplies the arithmetic Wronskian divisor and its rigidity. -/
theorem finrank_le_three
    (V : Submodule k k[X]) [FiniteDimensional k V]
    (F : V →ₗ[k] k[X]) (ell n : ℕ) (hn : 3 ≤ n) (s : k) (Q : k[X])
    (hPdeg : ∀ P : V, (P : k[X]).natDegree ≤ n - 1)
    (hFdeg : ∀ P : V, (F P).natDegree ≤ ell + n - 1)
    (hQdeg : Q.natDegree = ell + 2 * n - 5)
    (hQeval : Q.eval s ≠ 0)
    (hdiv : ∀ P : V, Q ∣ wronskian (F P) P)
    (hjump : ∀ P : V, (P : k[X]).eval (s + 1) = 0 →
      (wronskian (F P) P).eval s = 0)
    (hrigid : ∀ P : V, P ≠ 0 → wronskian (F P) P ≠ 0) :
    finrank k V ≤ 3 := by
  classical
  by_contra hdim
  have hdim' : 3 < finrank k V := by omega
  let L : V →ₗ[k] (Fin 3 → k) :=
    { toFun := fun P => ![(P : k[X]).coeff (n - 1),
        (P : k[X]).coeff (n - 2), (P : k[X]).eval (s + 1)]
      map_add' := by intros; ext i; fin_cases i <;> simp
      map_smul' := by intros; ext i; fin_cases i <;> simp }
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hdim')
  obtain ⟨P, hPL, hP⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hL : L P = 0 := hPL
  have hc1 : (P : k[X]).coeff (n - 1) = 0 := congrFun hL 0
  have hc2 : (P : k[X]).coeff (n - 2) = 0 := congrFun hL 1
  have he : (P : k[X]).eval (s + 1) = 0 := congrFun hL 2
  have hd1 := natDegree_le_pred (hPdeg P) hc1
  have hd2 := natDegree_le_pred (show (P : k[X]).natDegree ≤ n - 2 by omega) hc2
  have hPd : (P : k[X]).natDegree ≤ n - 3 := by omega
  have hW := hrigid P hP
  have hwdeg := natDegree_wronskian_lt (F P) (P : k[X]) hW
  have hb := hFdeg P
  have hwd : (wronskian (F P) P).natDegree ≤ Q.natDegree := by
    rw [hQdeg]
    omega
  exact hW (eq_zero_of_dvd_of_natDegree_le_of_eval Q _ s hQeval
    (hdiv P) hwd (hjump P he))

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
