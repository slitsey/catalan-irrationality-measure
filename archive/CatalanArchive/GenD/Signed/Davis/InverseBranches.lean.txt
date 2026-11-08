module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/InverseBranches.lean
Original SHA256: 443b2e8c1e2d2d43680baae6132d21d7f9300c6f01307ea126c9d59762373a85
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Analytic.GapWeights
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# Real inverse branches certified by alternating controls

An exact finite certificate supplies `m` ordered, disjoint open intervals.
The polynomial values at their endpoints lie strictly beyond opposite ends
of `[-1,1]`. The intermediate value theorem supplies one root of `P - y` in
each interval. Degree `m` makes this the complete root list and makes every
root simple. Compactness then supplies a uniform positive derivative bound.

All endpoint and polynomial inequalities are hypotheses of a finite data
record. No numerical root finder, continuity of a chosen inverse branch, or
optimality assertion is used.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev Finset Set

noncomputable section

theorem factorization_of_distinct_roots {p : ℝ[X]} {m : ℕ}
    (hp : p ≠ 0) (hdeg : p.natDegree = m)
    (τ : Fin m → ℝ) (hτ : Function.Injective τ)
    (heval : ∀ i, p.eval (τ i) = 0) :
    p = C p.leadingCoeff * ∏ i : Fin m, (X - C (τ i)) := by
  classical
  let s : Finset ℝ := univ.image τ
  have hcard : s.card = m := by
    simpa only [s, card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective (s := (univ : Finset (Fin m))) hτ
  have hroots : p.roots = s.val :=
    roots_eq_of_natDegree_le_card_of_ne_zero
      (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact heval i)
      (by rw [hdeg, hcard]) hp
  have hcount : p.roots.card = p.natDegree := by
    rw [hroots, Finset.card_val, hcard, hdeg]
  have hf := C_leadingCoeff_mul_prod_multiset_X_sub_C hcount
  rw [hroots, ← Finset.prod_eq_multiset_prod] at hf
  have hprod : (∏ x ∈ s, (X - C x)) = ∏ i : Fin m, (X - C (τ i)) := by
    dsimp [s]
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact hτ hij
  rw [hprod] at hf
  exact hf.symm

theorem derivative_ne_zero_of_distinct_nodal {p : ℝ[X]} {m : ℕ}
    {τ : Fin m → ℝ} {c : ℝ}
    (hτ : Function.Injective τ) (hc : c ≠ 0)
    (hp : p = C c * ∏ i : Fin m, (X - C (τ i))) (i : Fin m) :
    (derivative p).eval (τ i) ≠ 0 := by
  classical
  have he := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := (univ : Finset (Fin m))) (v := τ) (mem_univ i)
  rw [Lagrange.eval_nodal, Lagrange.nodal_eq] at he
  rw [hp, derivative_C_mul, eval_mul, eval_C, he]
  apply mul_ne_zero hc
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h => (mem_erase.mp hj).1 (hτ h).symm)

/-- The endpoints may include the outer endpoints `-1` or `1`, but every
open branch interval lies in the desired support and avoids zero. -/
structure InverseBranchCertificate (p : ℝ[X]) (m : ℕ) (G : ℝ → Prop) where
  left : Fin m → ℝ
  right : Fin m → ℝ
  ordered : ∀ i, left i < right i
  separated : ∀ i j, i < j → right i ≤ left j
  support : ∀ i x, x ∈ Ioo (left i) (right i) →
    x ∈ Ioo (-1 : ℝ) 1 ∧ x ≠ 0 ∧ G x
  alternating : ∀ i,
    (p.eval (left i) < -1 ∧ 1 < p.eval (right i)) ∨
    (p.eval (right i) < -1 ∧ 1 < p.eval (left i))

namespace InverseBranchCertificate

variable {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
variable (cert : InverseBranchCertificate p m G)

theorem exists_root (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (i : Fin m) :
    ∃ x ∈ Ioo (cert.left i) (cert.right i), p.eval x = y := by
  rcases cert.alternating i with h | h
  · apply intermediate_value_Ioo (cert.ordered i).le p.continuousOn
    exact ⟨lt_of_lt_of_le h.1 hy.1, lt_of_le_of_lt hy.2 h.2⟩
  · apply intermediate_value_Ioo' (cert.ordered i).le p.continuousOn
    exact ⟨lt_of_lt_of_le h.1 hy.1, lt_of_le_of_lt hy.2 h.2⟩

def root (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (i : Fin m) : ℝ :=
  Classical.choose (cert.exists_root y hy i)

theorem root_mem (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (i : Fin m) :
    cert.root y hy i ∈ Ioo (cert.left i) (cert.right i) :=
  (Classical.choose_spec (cert.exists_root y hy i)).1

theorem eval_root (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (i : Fin m) :
    p.eval (cert.root y hy i) = y :=
  (Classical.choose_spec (cert.exists_root y hy i)).2

theorem root_support (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (i : Fin m) :
    cert.root y hy i ∈ Ioo (-1 : ℝ) 1 ∧ cert.root y hy i ≠ 0 ∧
      G (cert.root y hy i) :=
  cert.support i _ (cert.root_mem y hy i)

theorem root_injective (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
    Function.Injective (cert.root y hy) := by
  intro i j hij
  have hi := cert.root_mem y hy i
  have hj := cert.root_mem y hy j
  rcases lt_trichotomy i j with h | h | h
  · have hs := cert.separated i j h
    linarith only [hi.2, hj.1, hs, hij]
  · exact h
  · have hs := cert.separated j i h
    linarith only [hi.1, hj.2, hs, hij]

theorem sub_C_ne_zero (hdeg : p.natDegree = m) (hm : 0 < m) (y : ℝ) :
    p - C y ≠ 0 := by
  intro hz
  have hd := congrArg Polynomial.natDegree hz
  rw [natDegree_sub_C, hdeg, natDegree_zero] at hd
  omega

theorem sub_C_factorization (hdeg : p.natDegree = m) (hm : 0 < m)
    (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
    p - C y = C (p - C y).leadingCoeff *
      ∏ i : Fin m, (X - C (cert.root y hy i)) := by
  apply factorization_of_distinct_roots (sub_C_ne_zero hdeg hm y)
    (by rw [natDegree_sub_C, hdeg]) _ (cert.root_injective y hy)
  intro i
  rw [eval_sub, eval_C, cert.eval_root y hy i, sub_self]

/-- Every preimage of the closed target interval is one of the certified
roots. This also bounds the full preimage set, not merely the chosen roots. -/
theorem eq_root_of_eval_mem (hdeg : p.natDegree = m) (hm : 0 < m)
    (x : ℝ) (hx : p.eval x ∈ Icc (-1 : ℝ) 1) :
    ∃ i : Fin m, x = cert.root (p.eval x) hx i := by
  classical
  have hc : (p - C (p.eval x)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (sub_C_ne_zero hdeg hm _)
  have hz : (p - C (p.eval x)).eval x = 0 := by simp
  rw [cert.sub_C_factorization hdeg hm (p.eval x) hx,
    eval_mul, eval_C, eval_prod] at hz
  have hzprod := (mul_eq_zero.mp hz).resolve_left hc
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hzprod
  exact ⟨i, by simpa only [eval_sub, eval_X, eval_C, sub_eq_zero] using hi⟩

include cert in
theorem derivative_ne_zero (hdeg : p.natDegree = m) (hm : 0 < m)
    (x : ℝ) (hx : p.eval x ∈ Icc (-1 : ℝ) 1) :
    (derivative p).eval x ≠ 0 := by
  obtain ⟨i, hi⟩ := cert.eq_root_of_eval_mem hdeg hm x hx
  have hc : (p - C (p.eval x)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (sub_C_ne_zero hdeg hm _)
  have hder := derivative_ne_zero_of_distinct_nodal
    (cert.root_injective (p.eval x) hx) hc
    (cert.sub_C_factorization hdeg hm (p.eval x) hx) i
  simpa only [derivative_sub, derivative_C, sub_zero, ← hi] using hder

/-- A single fixed positive derivative bound works for every inverse branch
and every target value in `[-1,1]`. -/
theorem exists_derivative_lower (hdeg : p.natDegree = m) (hm : 0 < m) :
    ∃ d : ℝ, 0 < d ∧ ∀ (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (i : Fin m),
      d ≤ |(derivative p).eval (cert.root y hy i)| := by
  let s : Set ℝ := Icc (-1 : ℝ) 1 ∩ p.eval ⁻¹' Icc (-1 : ℝ) 1
  have hs : IsCompact s :=
    isCompact_Icc.inter_right (isClosed_Icc.preimage p.continuous)
  let i : Fin m := ⟨0, hm⟩
  have hz : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hne : s.Nonempty := by
    refine ⟨cert.root 0 hz i, ?_⟩
    constructor
    · exact Ioo_subset_Icc_self (cert.root_support 0 hz i).1
    · change p.eval (cert.root 0 hz i) ∈ Icc (-1 : ℝ) 1
      rw [cert.eval_root 0 hz i]
      exact hz
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne (derivative p).continuous.abs.continuousOn
  refine ⟨|(derivative p).eval x|, abs_pos.mpr (cert.derivative_ne_zero hdeg hm x hx.2), ?_⟩
  intro y hy j
  apply hmin
  constructor
  · exact Ioo_subset_Icc_self (cert.root_support y hy j).1
  · change p.eval (cert.root y hy j) ∈ Icc (-1 : ℝ) 1
    rw [cert.eval_root y hy j]
    exact hy

end InverseBranchCertificate

end
end Analytic
end CatalanMeasure.GenD

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.GenD.Analytic.factorization_of_distinct_roots
#print axioms CatalanMeasure.GenD.Analytic.derivative_ne_zero_of_distinct_nodal
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.exists_root
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.root
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.root_mem
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.eval_root
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.root_support
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.root_injective
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.sub_C_ne_zero
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.sub_C_factorization
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.eq_root_of_eval_mem
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.derivative_ne_zero
#print axioms CatalanMeasure.GenD.Analytic.InverseBranchCertificate.exists_derivative_lower
