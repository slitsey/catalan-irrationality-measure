module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ComputeDegree

/-!
# Z0.10: confluent Lagrange / double-pole residue identity

For distinct nodes `x a` (`a : ι`, `N = |ι|`) and `deg G + 2 ≤ 2 N`:
`∑ a, (G'(x a) - 2 G(x a) ∑_{b ≠ a} (x a - x b)⁻¹) * (∏_{b ≠ a} (x a - x b))⁻² = 0`.
Proof by Hermite interpolation.
-/

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Bordered

variable {F : Type*} [Field F]

/-- A polynomial vanishing to first order at `c` (value and derivative) is divisible by
`(X - c)²`. -/
lemma sq_dvd_of_eval (p : F[X]) (c : F) (h0 : p.eval c = 0) (h1 : p.derivative.eval c = 0) :
    (X - C c) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.2 h0
  have hd : p.derivative = q + (X - C c) * q.derivative := by
    rw [hq, derivative_mul]; simp
  rw [hd] at h1
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at h1
  obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.2 h1
  exact ⟨r, by rw [hq, hr]; ring⟩

section Node

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Logarithmic derivative of a node polynomial. -/
lemma eval_derivative_prod_X_sub_C (x : ι → F) (a : ι) :
    ∀ s : Finset ι, a ∉ s → (∀ b ∈ s, x a ≠ x b) →
      (∏ b ∈ s, (X - C (x b))).derivative.eval (x a)
        = (∏ b ∈ s, (x a - x b)) * ∑ b ∈ s, (x a - x b)⁻¹ := by
  intro s
  induction s using Finset.induction_on with
  | empty => intros; simp
  | insert c s hc ih =>
    intro ha hne
    have hac : x a ≠ x c := hne c (mem_insert_self _ _)
    have has : a ∉ s := fun h => ha (mem_insert_of_mem h)
    have ih' := ih has (fun b hb => hne b (mem_insert_of_mem hb))
    rw [Finset.prod_insert hc, derivative_mul, Finset.prod_insert hc, Finset.sum_insert hc]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, one_mul, ih']
    have h1 : x a - x c ≠ 0 := sub_ne_zero.2 hac
    have h2 : eval (x a) (∏ b ∈ s, (X - C (x b))) = ∏ b ∈ s, (x a - x b) := by
      simp [eval_prod]
    rw [h2]
    field_simp

/-- **Z0.10.** Confluent Lagrange / double-pole residue identity. -/
theorem sum_res_sq_eq_zero (x : ι → F) (hx : Function.Injective x)
    (G : F[X]) (hG : G.natDegree + 2 ≤ 2 * Fintype.card ι) :
    ∑ a, (G.derivative.eval (x a) - 2 * G.eval (x a) * ∑ b ∈ univ.erase a, (x a - x b)⁻¹)
      * ((∏ b ∈ univ.erase a, (x a - x b))⁻¹) ^ 2 = 0 := by
  set N := Fintype.card ι with hNdef
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · omega
  set q : ι → F[X] := fun a => ∏ b ∈ univ.erase a, (X - C (x b)) with hq
  set h : ι → F[X] := fun a => q a ^ 2 with hh
  set P : ι → F := fun a => ∏ b ∈ univ.erase a, (x a - x b) with hP
  set S : ι → F := fun a => ∑ b ∈ univ.erase a, (x a - x b)⁻¹ with hS
  have hqmon : ∀ a, (q a).Monic := fun a => monic_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)
  have hqdeg : ∀ a, (q a).natDegree = N - 1 := by
    intro a
    rw [hq]; simp only
    rw [natDegree_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)]
    simp [Finset.card_erase_of_mem, hNdef]
  have hhmon : ∀ a, (h a).Monic := fun a => (hqmon a).pow 2
  have hhdeg : ∀ a, (h a).natDegree = 2 * (N - 1) := by
    intro a; rw [hh]; simp only [natDegree_pow, hqdeg]
  have hPne : ∀ a, P a ≠ 0 := by
    intro a
    rw [hP]; simp only
    refine Finset.prod_ne_zero_iff.2 fun b hb => sub_ne_zero.2 fun hab => ?_
    exact (Finset.mem_erase.1 hb).1 (hx hab).symm
  have hqev : ∀ a, (q a).eval (x a) = P a := by
    intro a; simp [hq, hP, eval_prod]
  have hqd : ∀ a, (q a).derivative.eval (x a) = P a * S a := by
    intro a
    exact eval_derivative_prod_X_sub_C x a (univ.erase a) (Finset.notMem_erase _ _)
      (fun b hb => fun hab => (Finset.mem_erase.1 hb).1 (hx hab).symm)
  have hhev : ∀ a, (h a).eval (x a) = P a ^ 2 := by
    intro a; simp [hh, eval_pow, hqev]
  have hhd : ∀ a, (h a).derivative.eval (x a) = 2 * (P a ^ 2 * S a) := by
    intro a
    simp only [hh, derivative_sq, eval_mul, eval_C, hqev, hqd]
    ring
  have hvan : ∀ a b, b ≠ a → (h b).eval (x a) = 0 ∧ (h b).derivative.eval (x a) = 0 := by
    intro a b hba
    have : (q b).eval (x a) = 0 := by
      simp only [hq, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hba.symm, mem_univ a⟩) (sub_self _)
    refine ⟨by simp [hh, this], ?_⟩
    simp [hh, derivative_sq, this]
  set β : ι → F := fun a => G.eval (x a) / P a ^ 2 with hβ
  set α : ι → F := fun a => (G.derivative.eval (x a) - β a * (2 * (P a ^ 2 * S a))) / P a ^ 2 with hα
  set Lp : ι → F[X] := fun a => C (α a) * (X - C (x a)) + C (β a) with hLp
  set E : F[X] := G - ∑ a, Lp a * h a with hE
  have hEval : ∀ a, E.eval (x a) = 0 := by
    intro a
    rw [hE, eval_sub, eval_finsetSum, Finset.sum_eq_single a]
    · simp only [hLp, eval_mul, eval_add, eval_C, eval_sub, eval_X, sub_self, mul_zero, zero_add,
        hhev, hβ]
      field_simp [hPne a]
      ring
    · intro b _ hba; rw [eval_mul, (hvan a b hba).1, mul_zero]
    · intro h'; exact absurd (mem_univ a) h'
  have hEder : ∀ a, E.derivative.eval (x a) = 0 := by
    intro a
    rw [hE, derivative_sub, derivative_sum, eval_sub, eval_finsetSum, Finset.sum_eq_single a]
    · simp only [hLp, derivative_mul, derivative_add, derivative_C, derivative_sub, derivative_X,
        eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero, zero_add, hhev, hhd,
        sub_zero, mul_one, zero_mul, add_zero, hα]
      field_simp [hPne a]
      ring
    · intro b _ hba
      rw [derivative_mul, eval_add, eval_mul, eval_mul, (hvan a b hba).1, (hvan a b hba).2]
      simp
    · intro h'; exact absurd (mem_univ a) h'
  have hdvd : ∀ a, (X - C (x a)) ^ 2 ∣ E := fun a => sq_dvd_of_eval E (x a) (hEval a) (hEder a)
  have hcop : (↑(univ : Finset ι) : Set ι).Pairwise
      (Function.onFun IsCoprime fun a => (X - C (x a)) ^ 2) := by
    intro a _ b _ hab
    have := (pairwise_coprime_X_sub_C hx hab)
    exact this.pow
  have hdvd' : ∏ a, (X - C (x a)) ^ 2 ∣ E := Finset.prod_dvd_of_coprime hcop (fun a _ => hdvd a)
  have hLdeg : ∀ a, (Lp a).natDegree ≤ 1 := by
    intro a; simp only [hLp]; compute_degree
  have hEdeg : E.natDegree < 2 * N := by
    have h1 : (∑ a, Lp a * h a).natDegree ≤ 2 * N - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
      refine (natDegree_mul_le).trans ?_
      rw [hhdeg]; have := hLdeg a; omega
    have h2 := natDegree_sub_le G (∑ a, Lp a * h a)
    rw [hE]
    omega
  have hE0 : E = 0 := by
    by_contra hne
    have h1 := natDegree_le_of_dvd hdvd' hne
    have h2 : (∏ a, (X - C (x a)) ^ 2 : F[X]).natDegree = 2 * N := by
      rw [natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow 2)]
      simp [natDegree_pow, hNdef, mul_comm]
    omega
  have hLform : ∀ a, Lp a = C (α a) * X + C (β a - α a * x a) := by
    intro a; simp only [hLp, map_sub, map_mul]; ring
  have hk : 2 * N - 1 = 2 * (N - 1) + 1 := by omega
  have hcoef : ∀ a, (Lp a * h a).coeff (2 * N - 1) = α a := by
    intro a
    have e1 : (h a).coeff (2 * (N - 1)) = 1 := by
      rw [← hhdeg a]; exact (hhmon a).coeff_natDegree
    have e2 : (h a).coeff (2 * (N - 1) + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hhdeg]; exact Nat.lt_succ_self _)
    rw [hk, hLform, add_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_C_mul, e1, e2]
    ring
  have hsum : ∑ a, α a = 0 := by
    have h1 : E.coeff (2 * N - 1) = 0 := by rw [hE0]; simp
    rw [hE, coeff_sub, finsetSum_coeff, coeff_eq_zero_of_natDegree_lt (by omega)] at h1
    simp only [hcoef] at h1
    simpa using h1
  rw [← hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hα, hβ, hP, hS]
  have := hPne a
  simp only [hP] at this
  field_simp

/-- **Z0.10 (simple poles).** `∑ₐ G(xₐ) / ∏_{b≠a}(xₐ - x_b) = 0` for `deg G + 2 ≤ N`. -/
theorem sum_res_eq_zero (x : ι → F) (hx : Function.Injective x)
    (G : F[X]) (hG : G.natDegree + 2 ≤ Fintype.card ι) :
    ∑ a, G.eval (x a) * (∏ b ∈ univ.erase a, (x a - x b))⁻¹ = 0 := by
  set N := Fintype.card ι with hNdef
  set q : ι → F[X] := fun a => ∏ b ∈ univ.erase a, (X - C (x b)) with hq
  set P : ι → F := fun a => ∏ b ∈ univ.erase a, (x a - x b) with hP
  have hqmon : ∀ a, (q a).Monic := fun a => monic_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)
  have hqdeg : ∀ a, (q a).natDegree = N - 1 := by
    intro a
    rw [hq]; simp only
    rw [natDegree_prod_of_monic _ _ (fun b _ => monic_X_sub_C _)]
    simp [Finset.card_erase_of_mem, hNdef]
  have hPne : ∀ a, P a ≠ 0 := by
    intro a
    rw [hP]; simp only
    refine Finset.prod_ne_zero_iff.2 fun b hb => sub_ne_zero.2 fun hab => ?_
    exact (Finset.mem_erase.1 hb).1 (hx hab).symm
  have hqev : ∀ a, (q a).eval (x a) = P a := by
    intro a; simp [hq, hP, eval_prod]
  have hqvan : ∀ a c, a ≠ c → (q a).eval (x c) = 0 := by
    intro a c hac
    simp only [hq, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hac.symm, mem_univ c⟩) (sub_self _)
  set E : F[X] := G - ∑ a, C (G.eval (x a) / P a) * q a with hE
  have hEv : ∀ c, E.eval (x c) = 0 := by
    intro c
    rw [hE, eval_sub, eval_finsetSum, Finset.sum_eq_single c]
    · simp [hqev, hPne c]
    · intro b _ hbc; rw [eval_mul, hqvan b c hbc, mul_zero]
    · intro h'; exact absurd (mem_univ c) h'
  have hN2 : 2 ≤ N := by omega
  have hEdeg : E.natDegree < N := by
    have h1 : (∑ a, C (G.eval (x a) / P a) * q a).natDegree ≤ N - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [hqdeg]
    have h2 := natDegree_sub_le G (∑ a, C (G.eval (x a) / P a) * q a)
    rw [hE]; omega
  have hE0 : E = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero E hx hEv hEdeg
  have h1 : E.coeff (N - 1) = 0 := by rw [hE0]; simp
  rw [hE, coeff_sub, finsetSum_coeff, coeff_eq_zero_of_natDegree_lt (by omega)] at h1
  have hc : ∀ a, (C (G.eval (x a) / P a) * q a).coeff (N - 1) = G.eval (x a) / P a := by
    intro a
    rw [coeff_C_mul, ← hqdeg a, (hqmon a).coeff_natDegree, mul_one]
  simp only [hc] at h1
  simpa [div_eq_mul_inv] using h1

end Node

end CatalanCore.Bordered
