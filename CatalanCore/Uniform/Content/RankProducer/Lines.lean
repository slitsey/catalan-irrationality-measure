module

public import CatalanCore.Uniform.Content.RankProducer.Price
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Module CatalanCore.Uniform.Content.Hybrid
open scoped Classical

/-- One exhibited nonzero common vector is enough for an intersection lower bound. -/
theorem one_le_finrank_inf_of_mem {K : Type*} [Field K]
    (V W : Submodule K (K × K)) (v : K × K) (hv : v ≠ 0)
    (hV : v ∈ V) (hW : v ∈ W) : 1 ≤ finrank K ↥(V ⊓ W) := by
  have hle : Submodule.span K {v} ≤ V ⊓ W :=
    (Submodule.span_singleton_le_iff_mem _ _).2 ⟨hV, hW⟩
  calc 1 = finrank K ↥(Submodule.span K {v}) := (finrank_span_singleton hv).symm
       _ ≤ finrank K ↥(V ⊓ W) := Submodule.finrank_mono hle

/-- The alternating determinant recognizes every nonzero line in a two-dimensional field space. -/
theorem mem_span_of_omega_eq_zero {K : Type*} [Field K] (v w : K × K)
    (hv : v ≠ 0) (horth : omegaL v w = 0) :
    w ∈ Submodule.span K {v} := by
  rw [omegaL_apply] at horth
  apply Submodule.mem_span_singleton.2
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := by
      intro h2
      exact hv (Prod.ext h1 h2)
    have hw1 : w.1 = 0 := by
      have hmul : v.2 * w.1 = 0 := by
        simpa only [h1, zero_mul, zero_sub, neg_eq_zero] using horth
      exact (mul_eq_zero.mp hmul).resolve_left h2
    refine ⟨w.2 / v.2, ?_⟩
    apply Prod.ext
    · change w.2 / v.2 * v.1 = w.1
      simp only [h1, mul_zero, hw1]
    · change w.2 / v.2 * v.2 = w.2
      exact div_mul_cancel₀ _ h2
  · refine ⟨w.1 / v.1, ?_⟩
    apply Prod.ext
    · change w.1 / v.1 * v.1 = w.1
      exact div_mul_cancel₀ _ h1
    · change w.1 / v.1 * v.2 = w.2
      calc _ = (w.1 * v.2) / v.1 := by ring
           _ = w.2 := (div_eq_iff h1).2 (by linear_combination -horth)

variable (p : ℕ) [Fact p.Prime]

/-- A nonzero killed column load lying in the chosen subspace supplies one unit of mc. -/
theorem one_le_col_intersection (c : FibreCert)
    (V : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (d : ℕ) (hd : d ∈ c.kc) (hne : castV p (c.cload d) ≠ 0)
    (hV : castV p (c.cload d) ∈ V) :
    1 ≤ finrank (RatFunc (ZMod p)) ↥(V ⊓ Ucol p c) := by
  apply one_le_finrank_inf_of_mem V (Ucol p c) _ hne hV
  apply Submodule.subset_span
  exact ⟨d, hd, rfl⟩

/-- Explicit orthogonality to the killed row loads supplies one unit of mr. -/
theorem one_le_row_intersection (c : FibreCert)
    (V : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)))
    (v : RatFunc (ZMod p) × RatFunc (ZMod p)) (hne : v ≠ 0) (hV : v ∈ V)
    (horth : ∀ d ∈ c.kr, omegaL (castV p (c.rload d)) v = 0) :
    1 ≤ finrank (RatFunc (ZMod p)) ↥(V ⊓ Urow p c) := by
  apply one_le_finrank_inf_of_mem V (Urow p c) v hne hV
  simpa only [Urow, Submodule.mem_iInf, LinearMap.mem_ker] using horth

#print axioms mem_span_of_omega_eq_zero
#print axioms one_le_col_intersection
#print axioms one_le_row_intersection
end CatalanCore.Uniform.Content.RankProducer
