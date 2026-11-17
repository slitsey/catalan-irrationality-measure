/-
Portions adapted from Tang, dtq1997/li2-half-irrationality, revision
950ee9d53914e1afb89c8f835a8bca6ccfaa0108, Apache-2.0.
See CatalanCore/Li2/Port/LICENSE and NOTICE. Changes: arbitrary valuation loss f.
-/
module

public import CatalanCore.Li2.Content.Local
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P042
public import CatalanCore.Li2.Port.Unified.Modular.Base.DecayThreeAdic

@[expose] public section

open Polynomial Finset Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port

namespace CatalanCore.Li2.Content
open Port.Unified.Proofs.Arithmetic

private theorem recurrence_VG_f (p : ℕ) [Fact p.Prime] (r f : ℚ)
    (M J : ℕ → ℚ) (hf : 0 ≤ f) (hr : Apery.VG p r (-f))
    (h0 : M 0 = r) (hrec : ∀ k, M (k + 1) = r * (M k + J k))
    (hJ : ∀ k, Apery.VG p (J k) 0) (k : ℕ) :
    Apery.VG p (M k) (-((k : ℚ) + 1) * f) := by
  induction k with
  | zero => simpa only [h0, Nat.cast_zero, zero_add, neg_one_mul] using hr
  | succ k ih =>
    have hj : Apery.VG p (J k) (-((k : ℚ) + 1) * f) :=
      (hJ k).mono (by nlinarith [Nat.cast_nonneg (α := ℚ) k])
    rw [hrec]
    convert hr.mul (ih.add hj) using 1 <;> push_cast <;> ring

theorem binomMoment_VG_f (p : ℕ) [Fact p.Prime] (z f : ℚ)
    (h1 : z ≠ 1) (hf : 0 ≤ f) (hr : Port.Li2.VG p (z / (1 - z)) (-f)) (k : ℕ) :
    Port.Li2.VG p (binomMoment z k) (-((k : ℚ) + 1) * f) := by
  refine recurrence_VG_f p (z / (1 - z)) f (binomMoment z)
    (fun k => (Port.Li2.binomPoly (k + 1)).eval 1) hf hr (binomMoment_zero z) ?_ ?_ k
  · intro k
    have hden : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).mpr
    have hs := binomMoment_succ z h1 k
    nlinarith
  · intro k
    exact Port.Li2.binomPoly_eval_int_VG p (k + 1) 1

theorem parameterG_VG_f (p : ℕ) [Fact p.Prime] (z f : ℚ)
    (h1 : z ≠ 1) (hf : 0 ≤ f) (hr : Port.Li2.VG p (z / (1 - z)) (-f))
    {g : ℚ[X]} {d : ℕ} (hg : g.natDegree ≤ d) (r : ℚ)
    (hv : ∀ i ≤ d, Port.Li2.VG p (g.eval (i : ℚ)) r) :
    Port.Li2.VG p (Port.Li2.parameterG z g) (r - ((d : ℚ) + 1) * f) := by
  rw [parameterG_newton z hg]
  apply Apery.VG.sum
  intro k hk
  have hk' : k ≤ d := by simp at hk; omega
  have hc := Port.Li2.newtonCoeff_VG p 0 r k
    (fun i hi => by simpa using hv i (hi.trans hk'))
  refine (hc.mul (binomMoment_VG_f p z f h1 hf hr k)).mono ?_
  have hkq : (k : ℚ) ≤ d := by exact_mod_cast hk'
  nlinarith

theorem parameterU_VG_f (p : ℕ) [Fact p.Prime] (z f : ℚ)
    (h1 : z ≠ 1) (hf : 0 ≤ f) (hr : Port.Li2.VG p (z / (1 - z)) (-f))
    {q : ℚ[X]} {d : ℕ} (hq : q.natDegree ≤ d) (r : ℚ)
    (hv : ∀ m : ℤ, Port.Li2.VG p (q.eval (m : ℚ)) r) :
    Port.Li2.VG p (Port.Li2.parameterU z q)
      (r - (Nat.log p d : ℚ) - ((d : ℚ) + 1) * f) := by
  unfold Port.Li2.parameterU
  have hdeg : (derivative (X * q)).natDegree ≤ d := by
    refine (natDegree_derivative_le _).trans ?_
    have hm := natDegree_mul_le (p := (X : ℚ[X])) (q := q)
    rw [natDegree_X] at hm
    omega
  apply parameterG_VG_f p z f h1 hf hr hdeg
  intro i _
  have hd := Port.Li2.derivative_eval_VG p hq r hv (i : ℤ)
  rw [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X]
  have hq' : Port.Li2.VG p (q.eval (i : ℚ)) (r - (Nat.log p d : ℚ)) := by
    have h := hv (i : ℤ)
    push_cast at h
    exact h.mono (by have := (Nat.cast_nonneg (Nat.log p d) : (0 : ℚ) ≤ _); linarith)
  push_cast at hd
  simpa using hq'.add ((Apery.VG.natCast (p := p) i).mul hd |>.mono (by simp))

theorem gramU_entry_VG_f (p : ℕ) [Fact p.Prime] (z f : ℚ)
    (h1 : z ≠ 1) (hf : 0 ≤ f) (hr : Port.Li2.VG p (z / (1 - z)) (-f))
    {n : ℕ} (hn : 1 ≤ n) {a b : ℕ} (ha : a < 2 * n) (hb : b < 2 * n) :
    Port.Li2.VG p (Port.Li2.parameterU z (Port.Li2.gramNum n a b /ₘ Port.Li2.D (4 * n)))
      (-2 * L p n - f * phi n (a + b)) := by
  by_cases hab : a + b < n
  · rw [Port.Li2.gramQuot_eq_zero hab, Port.Li2.parameterU_zero]
    exact Apery.VG.zero _
  · have hu := parameterU_VG_f p z f h1 hf hr
      (Port.Li2.gramQuot_natDegree_le n a b)
      (-(Nat.log p (3*n+a+b) : ℚ)) (Port.Li2.gramQuot_eval_VG p n a b)
    have hlog1 : (Nat.log p (3*n+a+b) : ℚ) ≤ L p n := by
      dsimp [L]
      exact_mod_cast Nat.log_mono_right (b := p) (by omega : 3*n+a+b ≤ 7*n-2)
    have hlog2 : (Nat.log p (3*n+a+b-4*n) : ℚ) ≤ L p n := by
      dsimp [L]
      exact_mod_cast Nat.log_mono_right (b := p) (by omega : 3*n+a+b-4*n ≤ 7*n-2)
    have hphi : phi n (a+b) = ((3*n+a+b-4*n : ℕ) : ℚ) + 1 := by
      dsimp [phi]
      rw [Nat.cast_sub (by omega)]
      push_cast
      have h : (n : ℚ) ≤ a+b := by exact_mod_cast (by omega : n ≤ a+b)
      rw [max_eq_left (by linarith)]
      ring
    exact hu.mono (by rw [hphi]; nlinarith)

end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.binomMoment_VG_f
#print axioms CatalanCore.Li2.Content.parameterG_VG_f
#print axioms CatalanCore.Li2.Content.parameterU_VG_f
#print axioms CatalanCore.Li2.Content.gramU_entry_VG_f
