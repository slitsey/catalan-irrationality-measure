module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/InverseImageNodes.lean
Original SHA256: f7e650f486b8fea342238b4e1e14f1d2263beac6ad93cb70ff5a9538d9f900f4
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.InverseBranches
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Chebyshev compositions of a certified inverse-branch polynomial

This supplies exactly `K*m` simple real roots of `T_K(P)`, their support,
and a derivative lower bound. The independent deletion lemma then retains
the desired `d*N` roots.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev Finset Set

noncomputable section

def inverseImagePolynomial (p : ℝ[X]) (K : ℕ) : ℝ[X] :=
  (T ℝ (K : ℤ)).comp p

def inverseImageNodePair {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (K : ℕ) (i : Fin K × Fin m) : ℝ :=
  cert.root (CatalanMeasure.chebX K i.1)
    (Ioo_subset_Icc_self (CatalanMeasure.chebX_mem i.1)) i.2

def inverseImageNodes {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (K : ℕ) : Fin (K * m) → ℝ :=
  inverseImageNodePair cert K ∘
    (finProdFinEquiv : Fin K × Fin m ≃ Fin (K * m)).symm

theorem inverseImageNodePair_eval {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (K : ℕ) (i : Fin K × Fin m) :
    p.eval (inverseImageNodePair cert K i) = CatalanMeasure.chebX K i.1 :=
  cert.eval_root _ _ _

theorem inverseImageNodePair_injective {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (K : ℕ) :
    Function.Injective (inverseImageNodePair cert K) := by
  intro i j hij
  have he := congrArg p.eval hij
  rw [inverseImageNodePair_eval, inverseImageNodePair_eval] at he
  have hfirst := CatalanMeasure.chebX_injective K he
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  dsimp only at hfirst
  subst j₁
  apply Prod.ext
  · rfl
  · exact cert.root_injective _ _ hij

theorem inverseImageNodes_injective {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (K : ℕ) :
    Function.Injective (inverseImageNodes cert K) :=
  (inverseImageNodePair_injective cert K).comp
    (finProdFinEquiv : Fin K × Fin m ≃ Fin (K * m)).symm.injective

theorem inverseImageNodes_support {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (K : ℕ) (i : Fin (K * m)) :
    inverseImageNodes cert K i ∈ Ioo (-1 : ℝ) 1 ∧
      inverseImageNodes cert K i ≠ 0 ∧ G (inverseImageNodes cert K i) :=
  cert.root_support _
    (Ioo_subset_Icc_self (CatalanMeasure.chebX_mem
      ((finProdFinEquiv : Fin K × Fin m ≃ Fin (K * m)).symm i).1)) _

theorem inverseImagePolynomial_natDegree {p : ℝ[X]} {m : ℕ}
    (hdeg : p.natDegree = m) (K : ℕ) :
    (inverseImagePolynomial p K).natDegree = K * m := by
  rw [inverseImagePolynomial, natDegree_comp, natDegree_T, Int.natAbs_natCast, hdeg]

theorem inverseImagePolynomial_eval_node {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) {K : ℕ} (hK : 0 < K)
    (i : Fin (K * m)) :
    (inverseImagePolynomial p K).eval (inverseImageNodes cert K i) = 0 := by
  let j := (finProdFinEquiv : Fin K × Fin m ≃ Fin (K * m)).symm i
  change ((T ℝ (K : ℤ)).comp p).eval (inverseImageNodePair cert K j) = 0
  rw [eval_comp, inverseImageNodePair_eval, CatalanMeasure.T_eq_nodal hK,
    eval_mul, eval_C, eval_prod]
  apply mul_eq_zero_of_right
  exact prod_eq_zero (mem_univ j.1) (by simp)

theorem inverseImagePolynomial_factorization {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G)
    (hdeg : p.natDegree = m) (hm : 0 < m) {K : ℕ} (hK : 0 < K) :
    inverseImagePolynomial p K = C (inverseImagePolynomial p K).leadingCoeff *
      ∏ i : Fin (K * m), (X - C (inverseImageNodes cert K i)) := by
  have hp : inverseImagePolynomial p K ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    rw [inverseImagePolynomial_natDegree hdeg, natDegree_zero] at hd
    exact (Nat.ne_of_gt (Nat.mul_pos hK hm)) hd
  exact factorization_of_distinct_roots hp (inverseImagePolynomial_natDegree hdeg K)
    _ (inverseImageNodes_injective cert K) (inverseImagePolynomial_eval_node cert hK)

theorem inverseImagePolynomial_derivative_ge {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) {d : ℝ}
    (hd : ∀ (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (j : Fin m),
      d ≤ |(derivative p).eval (cert.root y hy j)|)
    (K : ℕ) (i : Fin (K * m)) :
    d * K ≤ |(derivative (inverseImagePolynomial p K)).eval (inverseImageNodes cert K i)| := by
  let j := (finProdFinEquiv : Fin K × Fin m ≃ Fin (K * m)).symm i
  have hroot := hd (CatalanMeasure.chebX K j.1)
    (Ioo_subset_Icc_self (CatalanMeasure.chebX_mem j.1)) j.2
  have hcheb := cheb_derivative_eval_ge j.1
  change d * K ≤ |(derivative ((T ℝ (K : ℤ)).comp p)).eval
    (inverseImageNodePair cert K j)|
  rw [derivative_comp, eval_mul, eval_comp, inverseImageNodePair_eval, abs_mul]
  exact mul_le_mul hroot hcheb (Nat.cast_nonneg K) (abs_nonneg _)

theorem inverseImagePolynomial_derivative_uniform {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) {d : ℝ} (hd0 : 0 < d)
    (hd : ∀ (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) (j : Fin m),
      d ≤ |(derivative p).eval (cert.root y hy j)|)
    {K : ℕ} (hK : 0 < K) (i : Fin (K * m)) :
    d ≤ |(derivative (inverseImagePolynomial p K)).eval (inverseImageNodes cert K i)| := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hmul := mul_le_mul_of_nonneg_left hK1 hd0.le
  have hmul' : d ≤ d * K := by simpa using hmul
  exact hmul'.trans (inverseImagePolynomial_derivative_ge cert hd K i)

/-- A convenient elementary bound with no choice of complex square root. -/
theorem norm_chebyshev_eval_le_simple (K : ℕ) (z : ℂ) :
    ‖(T ℂ (K : ℤ)).eval z‖ ≤ (2 * ‖z‖ + 1) ^ K := by
  induction K using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [Nat.cast_one, T_one, eval_X, pow_one]
    linarith only [norm_nonneg z]
  | more n h₀ h₁ =>
    have he : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
    rw [he, T_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat]
    have hcast : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    calc
      _ ≤ 2 * ‖z‖ * ‖(T ℂ ((n + 1 : ℕ) : ℤ)).eval z‖ +
          ‖(T ℂ (n : ℤ)).eval z‖ := by
        simpa only [norm_mul, Complex.norm_ofNat] using
          norm_sub_le (2 * z * (T ℂ ((n + 1 : ℕ) : ℤ)).eval z)
            ((T ℂ (n : ℤ)).eval z)
      _ ≤ 2 * ‖z‖ * (2 * ‖z‖ + 1) ^ (n + 1) + (2 * ‖z‖ + 1) ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₀
      _ = (2 * ‖z‖ + 1) ^ (n + 2) - 2 * ‖z‖ * (2 * ‖z‖ + 1) ^ n := by
        simp only [pow_succ]
        ring
      _ ≤ (2 * ‖z‖ + 1) ^ (n + 2) := sub_le_self _ (by positivity)

theorem inverseImagePolynomial_norm_le {p : ℝ[X]} (K : ℕ) (z : ℂ) :
    ‖((inverseImagePolynomial p K).map (algebraMap ℝ ℂ)).eval z‖ ≤
      (2 * ‖(p.map (algebraMap ℝ ℂ)).eval z‖ + 1) ^ K := by
  rw [inverseImagePolynomial, Polynomial.map_comp, Chebyshev.map_T, eval_comp]
  exact norm_chebyshev_eval_le_simple K _

end
end Analytic
end CatalanMeasure.GenD

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial
#print axioms CatalanMeasure.GenD.Analytic.inverseImageNodePair
#print axioms CatalanMeasure.GenD.Analytic.inverseImageNodes
#print axioms CatalanMeasure.GenD.Analytic.inverseImageNodePair_eval
#print axioms CatalanMeasure.GenD.Analytic.inverseImageNodePair_injective
#print axioms CatalanMeasure.GenD.Analytic.inverseImageNodes_injective
#print axioms CatalanMeasure.GenD.Analytic.inverseImageNodes_support
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_natDegree
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_eval_node
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_factorization
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_derivative_ge
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_derivative_uniform
#print axioms CatalanMeasure.GenD.Analytic.norm_chebyshev_eval_le_simple
#print axioms CatalanMeasure.GenD.Analytic.inverseImagePolynomial_norm_le
