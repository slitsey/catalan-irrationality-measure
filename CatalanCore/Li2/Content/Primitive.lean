module

public import CatalanCore.Li2.Family
public import CatalanCore.Li2.Content.Assembly
public import CatalanCore.Uniform.Measure.NV0
public import Mathlib.RingTheory.Polynomial.ScaleRoots

@[expose] public section
set_option Elab.async false
open Polynomial Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port.Unified

/-! Primitive integer family: denominator-one content and D+cRate decay, following LC40. -/
namespace CatalanCore.Li2.Content

theorem primitiveFamily_scaled_Q (z : ℚ) (n : ℕ) :
    (CatalanCore.Li2.primitiveFamily z).Q n =
      C (ParameterFamily.dtilde z n) * (CatalanCore.Li2.li2Family z).Q n := by
  exact ParameterFamily.P_eq_dtilde_Qtilde z n

private theorem integerPolyClearDraft (P : ℤ[X]) (d : ℕ) (hd : P.natDegree ≤ d)
    (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ)^d * (P.map (algebraMap ℤ ℚ)).eval ((p : ℚ)/q) = z := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  let R := P.scaleRoots q
  have hpq : (algebraMap ℤ ℚ) q * ((p : ℚ)/q) = (algebraMap ℤ ℚ) p := by
    change (q : ℚ) * ((p : ℚ)/q) = (p : ℚ)
    field_simp
  have heq : (q : ℚ)^P.natDegree * (P.map (algebraMap ℤ ℚ)).eval ((p : ℚ)/q) = ((R.eval p : ℤ) : ℚ) := by
    have h := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ ℚ) ((p : ℚ)/q) q
    rw [hpq, Polynomial.eval₂_at_apply] at h
    rw [Polynomial.eval₂_eq_eval_map] at h
    change ((R.eval p : ℤ) : ℚ) =
      (q : ℚ)^P.natDegree * (P.map (algebraMap ℤ ℚ)).eval ((p : ℚ)/q) at h
    exact h.symm
  refine ⟨q^(d-P.natDegree) * R.eval p, ?_⟩
  calc
    (q : ℚ)^d * (P.map (algebraMap ℤ ℚ)).eval ((p : ℚ)/q) =
        (q : ℚ)^(d-P.natDegree) * ((q : ℚ)^P.natDegree *
          (P.map (algebraMap ℤ ℚ)).eval ((p : ℚ)/q)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hd]
    _ = (q : ℚ)^(d-P.natDegree) * ((R.eval p : ℤ) : ℚ) := by rw [heq]
    _ = ((q^(d-P.natDegree) * R.eval p : ℤ) : ℚ) := by push_cast; rfl

theorem primitive_content (z : ℚ) :
    CatalanCore.Uniform.HasScaledContent (CatalanCore.Li2.primitiveFamily z)
      CatalanCore.Li2.scale 0 := by
  refine ⟨fun _ => 1, fun _ => Nat.one_pos, ?_, ?_⟩
  · intro (n : ℕ) hn p q hq
    obtain ⟨w, hw⟩ := integerPolyClearDraft (ParameterFamily.P z n) (2*n)
      (ParameterFamily.P_natDegree_le z n) p q hq
    refine ⟨w, ?_⟩
    simpa only [CatalanCore.Li2.primitiveFamily, PolyFamily.evalQ, Nat.cast_one, mul_one] using hw
  · intro ε hε
    refine ⟨0, fun n _ _ => ?_⟩
    simp only [Nat.cast_one, Real.log_one, zero_add]
    positivity

end CatalanCore.Li2.Content
#print axioms CatalanCore.Li2.Content.primitiveFamily_scaled_Q
#print axioms CatalanCore.Li2.Content.primitive_content

namespace CatalanCore.Li2.Content

theorem primitive_decay (a b : ℤ) (hb : 0 < b) (hab : IsCoprime a b)
    (ha : a ≠ 0) (hablt : |a| < b) (D rho : ℝ)
    (hD : CatalanCore.Uniform.HasScaledDecay
      (CatalanCore.Li2.li2Family (lam a b)) CatalanCore.Li2.scale D rho) :
    CatalanCore.Uniform.HasScaledDecay
      (CatalanCore.Li2.primitiveFamily (lam a b)) CatalanCore.Li2.scale
      (D + CatalanCore.Li2.cRate a b) rho := by
  intro ε hε
  obtain ⟨R1, h1⟩ := hD (ε/2) (by linarith)
  obtain ⟨R2, h2⟩ := Filter.eventually_atTop.mp (content_rate a b hb hab ha hablt (ε/2) (by linarith))
  refine ⟨max R1 R2, ?_⟩
  intro (n : ℕ) hn hr t ht
  change |t| ≤ Real.exp (-(rho+ε)*(n:ℝ)) at ht
  change |(CatalanCore.Li2.primitiveFamily (lam a b)).evalR n (CatalanCore.Li2.value (lam a b)+t)| ≤
    Real.exp (-((D + CatalanCore.Li2.cRate a b)-ε)*(n:ℝ)^2)
  by_cases hQ : ParameterFamily.Qtilde (lam a b) n = 0
  · have h0 : (CatalanCore.Li2.primitiveFamily (lam a b)).Q n = 0 := by
      rw [primitiveFamily_scaled_Q]
      change C (ParameterFamily.dtilde (lam a b) n) * ParameterFamily.Qtilde (lam a b) n = 0
      rw [hQ, mul_zero]
    change |((CatalanCore.Li2.primitiveFamily (lam a b)).Q n).aeval _| ≤ _
    rw [h0, map_zero, abs_zero]
    exact (Real.exp_pos _).le
  · have hw : |t| ≤ Real.exp (-(rho+ε/2)*(n:ℝ)) :=
      ht.trans (Real.exp_le_exp.mpr (by have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _; nlinarith))
    have hdec := h1 n hn (le_trans (le_max_left _ _) hr) t hw
    have hlog := h2 n (le_trans (le_max_right _ _) hr) hQ
    have hm : (0:ℝ) < (ParameterFamily.dtilde (lam a b) n : ℝ) := by
      exact_mod_cast ParameterFamily.dtilde_pos (lam a b) n
    have hmle : (ParameterFamily.dtilde (lam a b) n : ℝ) ≤
        Real.exp (-(CatalanCore.Li2.cRate a b-ε/2)*(n:ℝ)^2) := by
      calc
        (ParameterFamily.dtilde (lam a b) n : ℝ) =
            Real.exp (Real.log (ParameterFamily.dtilde (lam a b) n : ℝ)) := (Real.exp_log hm).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlog
    have hev := congrArg (fun F : ℚ[X] => F.aeval (CatalanCore.Li2.value (lam a b)+t))
      (primitiveFamily_scaled_Q (lam a b) n)
    simp only [map_mul, aeval_C] at hev
    change (CatalanCore.Li2.primitiveFamily (lam a b)).evalR n (CatalanCore.Li2.value (lam a b)+t) =
      (ParameterFamily.dtilde (lam a b) n : ℝ) *
        (CatalanCore.Li2.li2Family (lam a b)).evalR n (CatalanCore.Li2.value (lam a b)+t) at hev
    rw [hev, abs_mul, abs_of_pos hm]
    calc
      (ParameterFamily.dtilde (lam a b) n : ℝ) *
          |(CatalanCore.Li2.li2Family (lam a b)).evalR n (CatalanCore.Li2.value (lam a b)+t)| ≤
          Real.exp (-(CatalanCore.Li2.cRate a b-ε/2)*(n:ℝ)^2) *
            Real.exp (-(D-ε/2)*(n:ℝ)^2) :=
        mul_le_mul hmle hdec (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-((D + CatalanCore.Li2.cRate a b)-ε)*(n:ℝ)^2) := by
        rw [← Real.exp_add]
        congr 1
        ring

end CatalanCore.Li2.Content
#print axioms CatalanCore.Li2.Content.primitive_decay
