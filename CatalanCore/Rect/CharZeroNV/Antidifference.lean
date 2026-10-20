module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Tactic

@[expose] public section

/-!
# An isolated integer pole obstructs a rational antidifference

This frame-independent algebraic lemma propagates denominator roots in the
positive or negative integer direction. It uses no analytic residues and no
assumption that an interpolating denominator is nonzero at data nodes.
-/

open Polynomial

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K]

noncomputable def shift (p : K[X]) : K[X] := p.comp (X + 1)

omit [CharZero K] in
@[simp] lemma eval_shift (p : K[X]) (x : K) :
    (shift p).eval x = p.eval (x + 1) := by simp [shift]

/-- A denominator has an isolated pole at `-1` in its integer orbit. -/
structure IsolatedIntegerPole (D A : K[X]) : Prop where
  pole : D.eval (-1) = 0
  residue : A.eval (-1) ≠ 0
  nonneg : ∀ n : ℕ, D.eval (n : K) ≠ 0
  negative : ∀ n : ℕ, D.eval (-((n : K) + 2)) ≠ 0

lemma coprime_eval_ne_zero {a b : K[X]} (h : IsCoprime a b)
    {x : K} (hb : b.eval x = 0) : a.eval x ≠ 0 := by
  obtain ⟨s, t, hst⟩ := h
  intro ha
  have he := congrArg (fun p : K[X] => p.eval x) hst
  simp [ha, hb] at he

theorem no_reduced_antidifference {D A a b : K[X]}
    (h : IsolatedIntegerPole D A) (hab : IsCoprime a b) (hb : b ≠ 0) :
    D * (shift a * b - a * shift b) ≠ A * b * shift b := by
  intro heq
  have he (x : K) := congrArg (fun p : K[X] => p.eval x) heq
  have hstart : b.eval (-1) = 0 ∨ b.eval 0 = 0 := by
    have he' := he (-1)
    simp only [eval_mul, eval_sub, eval_shift, h.pole, zero_mul,
      neg_add_cancel] at he'
    rcases mul_eq_zero.mp he'.symm with hprod | hzero
    · exact Or.inl ((mul_eq_zero.mp hprod).resolve_left h.residue)
    · exact Or.inr hzero
  have hroot : ∀ n : ℕ, b.eval (n : K) = 0 ∨ b.eval (-((n : K) + 1)) = 0 := by
    rcases hstart with hneg | hpos
    · have hall : ∀ n : ℕ, b.eval (-((n : K) + 1)) = 0 := by
        intro n
        induction n with
        | zero => simpa using hneg
        | succ n ih =>
          have he' := he (-((n : K) + 2))
          have hs : -((n : K) + 2) + 1 = -((n : K) + 1) := by ring
          simp only [eval_mul, eval_sub, eval_shift, hs, ih, mul_zero,
            sub_zero] at he'
          have hz := (mul_eq_zero.mp ((mul_eq_zero.mp he').resolve_left (h.negative n))).resolve_left
            (coprime_eval_ne_zero hab ih)
          simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hz
      exact fun n => Or.inr (hall n)
    · have hall : ∀ n : ℕ, b.eval (n : K) = 0 := by
        intro n
        induction n with
        | zero => simpa using hpos
        | succ n ih =>
          have he' := he (n : K)
          simp only [eval_mul, eval_sub, eval_shift, ih, mul_zero,
            zero_mul, zero_sub] at he'
          have hz := (mul_eq_zero.mp he').resolve_left (h.nonneg n)
          have hz' := (mul_eq_zero.mp (neg_eq_zero.mp hz)).resolve_left
            (coprime_eval_ne_zero hab ih)
          simpa only [Nat.cast_succ] using hz'
      exact fun n => Or.inl (hall n)
  have hinf : Set.Infinite {x : K | b.IsRoot x} := by
    by_contra hn
    have hf := Set.not_infinite.mp hn
    have hfpos : Set.Finite {n : ℕ | b.eval (n : K) = 0} :=
      hf.preimage (Nat.cast_injective (R := K)).injOn
    have hfneg : Set.Finite {n : ℕ | b.eval (-((n : K) + 1)) = 0} :=
      hf.preimage (by
        intro n _ m _ heq
        exact Nat.cast_injective (R := K) (by simpa using neg_injective heq))
    have hu : Set.Finite (Set.univ : Set ℕ) := by
      apply (hfpos.union hfneg).subset
      intro n _
      exact hroot n
    exact Set.infinite_univ hu
  exact hb (b.eq_zero_of_infinite_isRoot hinf)

/-- Clearing a rational antidifference is impossible, even before cancellation
of common factors in its numerator and denominator. -/
theorem no_antidifference {D A : K[X]} (h : IsolatedIntegerPole D A)
    (a b : K[X]) (hb : b ≠ 0) :
    D * (shift a * b - a * shift b) ≠ A * b * shift b := by
  classical
  let g := GCDMonoid.gcd a b
  have hg : g ≠ 0 := gcd_ne_zero_of_right hb
  let a₀ := a / g
  let b₀ := b / g
  have ha : g * a₀ = a := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hb' : g * b₀ = b := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right _ _)
  have hcp : IsCoprime a₀ b₀ := isCoprime_div_gcd_div_gcd hb
  have hb₀ : b₀ ≠ 0 := right_div_gcd_ne_zero hb
  have hsg : shift g ≠ 0 := by
    intro hz
    have hback := congrArg (fun p : K[X] => p.comp (X - 1)) hz
    have hid : (shift g).comp (X - 1) = g := by
      simp only [shift, comp_assoc, add_comp, X_comp, one_comp]
      convert g.comp_X using 1; congr 1; ring
    rw [hid, zero_comp] at hback
    exact hg hback
  intro heq
  apply no_reduced_antidifference h hcp hb₀
  apply mul_left_cancel₀ (mul_ne_zero hg hsg)
  calc
    (g * shift g) * (D * (shift a₀ * b₀ - a₀ * shift b₀)) =
        D * (shift a * b - a * shift b) := by
      rw [← ha, ← hb']
      simp only [shift, mul_comp]
      ring
    _ = A * b * shift b := heq
    _ = (g * shift g) * (A * b₀ * shift b₀) := by
      rw [← hb']
      simp only [shift, mul_comp]
      ring

end CatalanCore.Rect.CharZeroNV
