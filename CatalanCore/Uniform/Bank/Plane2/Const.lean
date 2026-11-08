module

public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Content.Sweep.Cells
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section
set_option Elab.async false

/-!
# The one-term datum of ζ(3) and its constant (lane H, wave Z; ledger N6, Z01)

The datum `F(z) = ψ′(z + 1)`: one shift `s = 1`, `a = 0`, `b = 1` (order 2, `d = 2`).  Its Löwner sequences are
the `(fS 1 0, eS 1 0)` of the sweep (`Sweep.Cells`, the one-term case `u = 0`), and its constant
`ξ = F′(0) = ψ″(1)` is `-2 ζ(3)`: `Datum.xi` is `-2 ∑ 1/(n+1)³` and `ζ(3) = (riemannZeta 3).re` is that series
(`riemannZeta_three_re`, O11).
-/

namespace CatalanCore.Uniform.Bank.Plane2

open CatalanCore CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep Finset

/-- The datum of `ψ′(z + 1)`: the single shift `1` with `a = 0`, `b = 1`. -/
@[reducible] def zeta3Datum : Datum where
  n := 1
  hn := by norm_num
  s := ![1]
  a := ![0]
  b := ![1]
  hs := by intro i; fin_cases i; norm_num
  hinj := by intro i j _; exact Subsingleton.elim i j
  hab := by intro i; fin_cases i; exact Or.inr (by norm_num)
  hbal := by simp

theorem zeta3Datum_f : zeta3Datum.f = fS 1 0 := by
  funext t
  unfold Datum.f fS
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Datum.delta, T1, T2]

theorem zeta3Datum_e : zeta3Datum.e = eS 1 0 := by
  funext t
  unfold Datum.e eS
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Datum.delta1, U1, U2]

/-- `ζ(3)` as the series `∑ 1/(n+1)³`. -/
theorem riemannZeta_three_re : (riemannZeta 3).re = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3 := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) := Real.summable_one_div_nat_pow.2 (by norm_num)
  have e : ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ 3 = ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast; rfl
  have h3 : (riemannZeta 3) = ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    have := h
    rw [e] at this
    simpa using this
  rw [h3, Complex.ofReal_re, hs.tsum_eq_zero_add]
  simp

/-- The constant of the datum: `ξ = ψ″(1) = -2 ζ(3)`. -/
theorem zeta3Datum_xi : zeta3Datum.xi = -2 * (riemannZeta 3).re := by
  rw [riemannZeta_three_re]
  unfold Datum.xi hurwitzTail3
  simp

end CatalanCore.Uniform.Bank.Plane2

#print axioms CatalanCore.Uniform.Bank.Plane2.zeta3Datum_f
#print axioms CatalanCore.Uniform.Bank.Plane2.zeta3Datum_e
#print axioms CatalanCore.Uniform.Bank.Plane2.zeta3Datum_xi
