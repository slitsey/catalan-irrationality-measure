module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.LinearAlgebra.Dimension.Finite
@[expose] public section
set_option Elab.async false

/-!
# The polynomial-valued kernel family of Theorem A

For a polynomial `P` of degree `< dh` over `F_p` (`2 dh < p`) put `G_P = ∑_{e<p} P(e) X^e`.

* `dvd_gOf`  : `(X-1)^dh ∣ G_P` (the Taylor coefficients of `G_P` at `1` are `∑_e P(e) C(e,d)`,
  sums over `F_p` of polynomials of degree `< p - 1`).
* `famSpace` : the polynomials `P` of degree `< dh` vanishing at the positions outside `[lo, hi)`;
  `finrank_famSpace_ge : dh + (hi - lo) ≤ dim + p`.
* `gOf_coeff` : `G_P` is supported in `[lo, hi)` for `P ∈ famSpace`.
* `gOf_injective` : `P ↦ G_P` is injective on polynomials of degree `< dh ≤ p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Polynomial Module Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `P ↦ ∑_{e<p} P(e) X^e`. -/
def gOf (p : ℕ) [Fact p.Prime] : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] where
  toFun P := ∑ e ∈ range p, C (P.eval (e : ZMod p)) * X ^ e
  map_add' P Q := by
    simp only [eval_add, C_add, add_mul, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [Polynomial.smul_eq_C_mul, RingHom.id_apply, eval_mul, eval_C, C_mul, Finset.mul_sum,
      mul_assoc]

theorem gOf_apply (P : (ZMod p)[X]) :
    gOf p P = ∑ e ∈ range p, C (P.eval (e : ZMod p)) * X ^ e := rfl

theorem gOf_coeff (P : (ZMod p)[X]) (e : ℕ) :
    (gOf p P).coeff e = if e < p then P.eval (e : ZMod p) else 0 := by
  rw [gOf_apply, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases h : e < p
  · rw [if_pos h, Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hn; exact absurd (mem_range.mpr h) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : e ≠ b := by have := mem_range.mp hb; omega
    simp [this]

/-- Sum over `range p` equals the sum over `ZMod p`. -/
theorem sum_range_eq_sum_zmod (f : ZMod p → ZMod p) :
    ∑ e ∈ range p, f (e : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_bij (fun e _ => (e : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a ha b hb hab
    have h1 := mem_range.mp ha
    have h2 := mem_range.mp hb
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
  · intro x _
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intro _ _; rfl

/-- Sum of a polynomial of degree `< p - 1` over `F_p` vanishes. -/
theorem sum_eval_zmod (f : (ZMod p)[X]) (hf : f.natDegree + 1 < p) :
    ∑ e ∈ range p, f.eval (e : ZMod p) = 0 := by
  rw [sum_range_eq_sum_zmod (fun x => f.eval x)]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := mem_range.mp hi
  simp_rw [← Finset.mul_sum]
  have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by rw [ZMod.card]; omega)
  rw [this, mul_zero]

theorem eval_descPochhammer_mul_choose (d e : ℕ) :
    ((d.factorial : ℕ) : ZMod p) * (e.choose d : ZMod p) =
      (descPochhammer (ZMod p) d).eval (e : ZMod p) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast; rfl

/-- The Taylor coefficients of `G_P` at `1`. -/
theorem taylor_coeff_gOf (P : (ZMod p)[X]) (d : ℕ) :
    ((gOf p P).comp (X + C 1)).coeff d =
      ∑ e ∈ range p, P.eval (e : ZMod p) * (e.choose d : ZMod p) := by
  rw [gOf_apply, Polynomial.sum_comp, finset_sum_coeff]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_comp, C_comp, X_pow_comp, coeff_C_mul]
  congr 1
  have := coeff_X_add_one_pow (ZMod p) e d
  simpa using this

/-- **Divisibility.**  `(X-1)^dh ∣ G_P` for `deg P < dh`, `2 dh < p`. -/
theorem dvd_gOf {dh : ℕ} (hdh : 2 * dh < p) (P : (ZMod p)[X]) (hP : P.degree < dh) :
    (X - 1 : (ZMod p)[X]) ^ dh ∣ gOf p P := by
  have h1 : (X - 1 : (ZMod p)[X]) = X - C 1 := by simp
  rw [h1, X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro d hd
  rw [taylor_coeff_gOf]
  have hfac : ((d.factorial : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff _ _).mp h
    have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp this
    omega
  apply (mul_right_inj' hfac).mp
  rw [mul_zero, Finset.mul_sum]
  have hnd : P = 0 ∨ P.natDegree < dh := by
    by_cases h0 : P = 0
    · exact Or.inl h0
    · right
      rw [degree_eq_natDegree h0] at hP
      exact_mod_cast hP
  rcases hnd with h0 | hnd
  · subst h0; simp
  have hdeg : (P * descPochhammer (ZMod p) d).natDegree + 1 < p := by
    have := natDegree_mul_le (p := P) (q := descPochhammer (ZMod p) d)
    rw [descPochhammer_natDegree] at this
    omega
  have := sum_eval_zmod _ hdeg
  rw [← this]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [eval_mul, ← eval_descPochhammer_mul_choose]
  ring

/-- Positions outside `[lo, hi)` below `p`. -/
def zset (p lo hi : ℕ) : Finset ℕ := (range p).filter fun e => e < lo ∨ hi ≤ e

theorem card_zset {lo hi : ℕ} (hlh : lo ≤ hi) (hhp : hi ≤ p) : (zset p lo hi).card = lo + (p - hi) := by
  have : zset p lo hi = range lo ∪ Ico hi p := by
    ext e
    simp only [zset, mem_filter, mem_range, mem_union, mem_Ico]
    omega
  rw [this, card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [mem_range, mem_Ico] at h1 h2
    omega

instance (dh : ℕ) : FiniteDimensional (ZMod p) (degreeLT (ZMod p) dh) :=
  LinearEquiv.finiteDimensional (degreeLTEquiv (ZMod p) dh).symm

theorem finrank_degreeLT (dh : ℕ) : finrank (ZMod p) (degreeLT (ZMod p) dh) = dh := by
  rw [LinearEquiv.finrank_eq (degreeLTEquiv (ZMod p) dh)]
  simp

/-- Evaluation at the positions outside `[lo, hi)`. -/
def evalZ (p dh lo hi : ℕ) [Fact p.Prime] :
    degreeLT (ZMod p) dh →ₗ[ZMod p] (zset p lo hi → ZMod p) :=
  LinearMap.pi fun e => (Polynomial.leval ((e.1 : ℕ) : ZMod p)).comp (Submodule.subtype _)

/-- The polynomials of degree `< dh` vanishing outside the positions `[lo, hi)`. -/
def famSpace (p dh lo hi : ℕ) [Fact p.Prime] : Submodule (ZMod p) (degreeLT (ZMod p) dh) :=
  LinearMap.ker (evalZ p dh lo hi)

theorem mem_famSpace {dh lo hi : ℕ} (a : degreeLT (ZMod p) dh) :
    a ∈ famSpace p dh lo hi ↔ ∀ e, e < p → (e < lo ∨ hi ≤ e) → (a : (ZMod p)[X]).eval (e : ZMod p) = 0 := by
  unfold famSpace evalZ
  rw [LinearMap.mem_ker]
  constructor
  · intro h e he hout
    have := congrFun h ⟨e, by simp [zset, he, hout]⟩
    simpa using this
  · intro h
    funext e
    have := mem_filter.mp e.2
    simpa using h e.1 (mem_range.mp this.1) this.2

theorem finrank_famSpace_ge {dh lo hi : ℕ} (hlh : lo ≤ hi) (hhp : hi ≤ p) :
    dh + (hi - lo) ≤ finrank (ZMod p) (famSpace p dh lo hi) + p := by
  have h1 := (evalZ p dh lo hi).finrank_range_add_finrank_ker
  have h2 := Submodule.finrank_le (LinearMap.range (evalZ p dh lo hi))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, card_zset hlh hhp] at h2
  rw [finrank_degreeLT] at h1
  unfold famSpace
  omega

/-- `G_P` is supported in `[lo, hi)` when `P` vanishes outside. -/
theorem gOf_coeff_supp {dh lo hi : ℕ} (a : famSpace p dh lo hi) (e : ℕ)
    (he : (gOf p (a.1 : (ZMod p)[X])).coeff e ≠ 0) : lo ≤ e ∧ e < hi := by
  rw [gOf_coeff] at he
  by_cases hep : e < p
  · rw [if_pos hep] at he
    by_contra hc
    apply he
    exact (mem_famSpace a.1).mp a.2 e hep (by omega)
  · rw [if_neg hep] at he; exact absurd rfl he

theorem gOf_injective {dh : ℕ} (hdh : dh ≤ p) (P : (ZMod p)[X]) (hP : P.degree < dh)
    (h0 : gOf p P = 0) : P = 0 := by
  have hev : ∀ x : ZMod p, P.eval x = 0 := by
    intro x
    have := congrArg (fun G => G.coeff x.val) h0
    simp only [gOf_coeff, coeff_zero, if_pos (ZMod.val_lt x), ZMod.natCast_zmod_val] at this
    exact this
  by_cases h : P = 0
  · exact h
  · exfalso
    have hnd : P.natDegree < dh := by
      rw [degree_eq_natDegree h] at hP
      exact_mod_cast hP
    have := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun x : ZMod p => x)
      (fun _ _ h => h) hev (by rw [ZMod.card]; omega)
    exact h this

end
end CatalanMeasure.GenD.Uniform.W.Lucas
