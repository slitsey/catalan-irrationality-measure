module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import CatalanCore.Zeta5.Local.Pullback

@[expose] public section

/-!
# Row ZC03: the reflection and shift identities for `τ` and `τ_X`

(Section II, (I2) of INTEGRALITY-CONTENT.)  With `L(x^d) = B_d` (`Lb`), `τ(P) = L(P''')/24` (`tau`)
and `τ_X(A / ∏_{r ∈ Pl} (x - r)) = tauX A Pl`:

* `Lb_shift` (ported, `BinomBasis`): `L(Q(x+1)) - L(Q) = Q'(0)`;
* `Lb_comp_neg_sub_one`: `L(Q(-1-x)) = L(Q)`;
* `tau_comp_neg_sub_one`: `τ(P(-1-x)) = -τ(P)`;   `tau_shift`: `τ(P(x+1)) - τ(P) = P⁗(0)/24`;
* `tauX_of_decomp`: a polynomial partial-fraction decomposition of the numerator determines `tauX`;
* `tauX_reflect`: `τ_X(g(-1-x)) = -τ_X(g(x))` for `g = A / ∏_{r ∈ Pl} (x-r)`;
* `tauX_shift`: `τ_X(g(x+1) - g(x)) = g⁗(0)/24` for `g` regular at `0` (`0 ∉ Pl`), with
  `g⁗(0)/24` the coefficient of `x⁴` in the Taylor series of `g` at `0`.

Both rational-function identities are stated on numerators over an explicit pole set (any finite
`Pl ⊆ ℤ`; a numerator vanishing at a pole is allowed, its residue is then `0`).
-/

open Finset Polynomial

namespace Apery

/-! ### Partial-fraction data determines `tauX` -/

lemma prod_erase_sub_ne_zero (Pl : Finset ℤ) (r : ℤ) : ∏ s ∈ Pl.erase r, ((r : ℚ) - s) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun s hs => by
    rw [Finset.mem_erase] at hs
    exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm)

lemma natDegree_prod_erase_le (Pl : Finset ℤ) {r : ℤ} (hr : r ∈ Pl) :
    (∏ s ∈ Pl.erase r, (X - C (s : ℚ))).natDegree ≤ Pl.card - 1 := by
  rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_sub_C _]
  rw [Finset.sum_congr rfl fun (s : ℤ) _ => natDegree_X_sub_C ((s : ℤ) : ℚ)]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem hr]

/-- If the numerator `A` equals `Q * ∏(x - r) + ∑_r ρ_r ∏_{s ≠ r} (x - s)`, then `Q` is its
polynomial part and `ρ_r` are its residues. -/
theorem decomp_unique (Pl : Finset ℤ) (A Q : ℚ[X]) (ρ : ℤ → ℚ)
    (h : A = Q * piPl Pl + ∑ r ∈ Pl, C (ρ r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ))) :
    polyPart A Pl = Q ∧ ∀ r ∈ Pl, resP A Pl r = ρ r := by
  constructor
  · unfold polyPart
    refine (div_modByMonic_unique Q (∑ r ∈ Pl, C (ρ r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)))
      (piPl_monic _) ⟨by rw [h]; ring, ?_⟩).1
    rw [degree_eq_natDegree (piPl_monic _).ne_zero, natDegree_piPl]
    rcases Nat.eq_zero_or_pos Pl.card with h0 | hpos
    · have : Pl = ∅ := Finset.card_eq_zero.mp h0
      subst this
      simp
    · refine degree_le_natDegree.trans_lt ?_
      have : (∑ r ∈ Pl, C (ρ r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ))).natDegree ≤ Pl.card - 1 :=
        natDegree_sum_le_of_forall_le _ _ fun r hr =>
          (natDegree_C_mul_le _ _).trans (natDegree_prod_erase_le Pl hr)
      exact_mod_cast Nat.lt_of_le_of_lt this (by omega)
  · intro r hr
    unfold resP
    have hpi : (piPl Pl).eval (r : ℚ) = 0 := by
      unfold piPl; rw [eval_prod]
      exact Finset.prod_eq_zero hr (by simp)
    have hA : A.eval (r : ℚ) = ρ r * ∏ s ∈ Pl.erase r, ((r : ℚ) - s) := by
      rw [h, eval_add, eval_mul, hpi, mul_zero, zero_add, eval_finsetSum,
        Finset.sum_eq_single r]
      · simp [eval_prod]
      · intro r' hr' hne
        rw [eval_mul, eval_prod]
        have : ∏ s ∈ Pl.erase r', ((r : ℚ) - (s : ℚ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hr⟩) (by simp)
        simp only [eval_sub, eval_X, eval_C]
        rw [this, mul_zero]
      · intro hnot; exact absurd hr hnot
    rw [hA, mul_div_assoc, div_self (prod_erase_sub_ne_zero Pl r), mul_one]

/-- `tauX` from partial-fraction data. -/
theorem tauX_of_decomp (Pl : Finset ℤ) (A Q : ℚ[X]) (ρ : ℤ → ℚ)
    (h : A = Q * piPl Pl + ∑ r ∈ Pl, C (ρ r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ))) :
    tauX A Pl = C (tau Q) + ∑ r ∈ Pl, C (ρ r) * (C (H5 (dd r)) - X) := by
  obtain ⟨h1, h2⟩ := decomp_unique Pl A Q ρ h
  unfold tauX
  rw [h1]
  congr 1
  exact Finset.sum_congr rfl fun r hr => by rw [h2 r hr]

/-! ### The Bernoulli functional under `x ↦ -1-x` and `x ↦ x+1` -/

lemma Lb_X_add_one_pow (n : ℕ) :
    Lb ((X + 1 : ℚ[X]) ^ n) = _root_.bernoulli n + if n = 1 then 1 else 0 := by
  rw [add_pow, Lb_sum]
  simp only [one_pow, mul_one]
  have e : ∀ k ∈ range (n + 1), Lb (X ^ k * (n.choose k : ℚ[X])) =
      (n.choose k : ℚ) * _root_.bernoulli k := by
    intro k _
    rw [show (X ^ k * (n.choose k : ℚ[X])) = C (n.choose k : ℚ) * X ^ k by
      rw [mul_comm]; simp, Lb_C_mul, Lb_X_pow]
  rw [Finset.sum_congr rfl e, Finset.sum_range_succ, _root_.sum_bernoulli, Nat.choose_self]
  simp only [Nat.cast_one, one_mul]
  ring

/-- `L(Q(-1-x)) = L(Q)`. -/
theorem Lb_comp_neg_sub_one (Q : ℚ[X]) : Lb (Q.comp (-X - 1)) = Lb Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [add_comp, Lb_add, Lb_add, hP, hQ]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, Lb_C_mul, Lb_C_mul, Lb_X_pow]
    congr 1
    have e : (-X - 1 : ℚ[X]) ^ n = C ((-1 : ℚ) ^ n) * (X + 1) ^ n := by
      rw [show (-X - 1 : ℚ[X]) = C (-1) * (X + 1) by simp; ring, mul_pow, ← C_pow]
    rw [e, Lb_C_mul, Lb_X_add_one_pow]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp
      · norm_num [_root_.bernoulli_one]
    · simp only [show n ≠ 1 by omega, ↓reduceIte, add_zero]
      rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow, one_mul]
      · rw [_root_.bernoulli_eq_zero_of_odd ho (by omega)]; simp

lemma iterate_derivative_comp_neg_sub_one (P : ℚ[X]) (k : ℕ) :
    derivative^[k] (P.comp (-X - 1)) = (-1) ^ k * (derivative^[k] P).comp (-X - 1) := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
    have hd : derivative (P.comp (-X - 1)) = -(derivative P).comp (-X - 1) := by
      rw [derivative_comp]; simp
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hd, iterate_derivative_neg, ih]
    ring

/-- **ZC03, reflection (polynomial form)**: `τ(P(-1-x)) = -τ(P)`. -/
theorem tau_comp_neg_sub_one (P : ℚ[X]) : tau (P.comp (-X - 1)) = -tau P := by
  unfold tau
  rw [iterate_derivative_comp_neg_sub_one, show ((-1 : ℚ[X]) ^ 3) = C (-1) by simp; norm_num,
    Lb_C_mul, Lb_comp_neg_sub_one]
  ring

/-- **ZC03, shift (polynomial form)**: `τ(P(x+1)) - τ(P) = P⁗(0)/24`. -/
theorem tau_shift (P : ℚ[X]) :
    tau (P.comp (X + 1)) - tau P = (derivative^[4] P).eval 0 / 24 := by
  have h3 : derivative^[3] (P.comp (X + 1)) = (derivative^[3] P).comp (X + 1) := by
    have : ∀ k (Q : ℚ[X]), derivative^[k] (Q.comp (X + 1)) = (derivative^[k] Q).comp (X + 1) := by
      intro k
      induction k with
      | zero => intro Q; simp
      | succ k ih =>
        intro Q
        have hd : derivative (Q.comp (X + 1)) = (derivative Q).comp (X + 1) := by
          rw [derivative_comp]; simp
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hd, ih]
    exact this 3 P
  unfold tau
  rw [h3, ← sub_div, Lb_shift]
  have : derivative^[4] P = derivative (derivative^[3] P) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Function.iterate_succ_apply']
  rw [this]

/-! ### Reflection of rational functions -/

lemma sum_comp' {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (q : ℚ[X]) :
    (∑ i ∈ s, f i).comp q = ∑ i ∈ s, (f i).comp q := by
  simp

/-- The reflection `r ↦ -1 - r` of the integer poles. -/
def refl (r : ℤ) : ℤ := -1 - r

lemma refl_refl (r : ℤ) : refl (refl r) = r := by unfold refl; ring

lemma refl_injective : Function.Injective refl := fun a b h => by unfold refl at h; omega

lemma dd_refl (r : ℤ) : dd (refl r) = dd r := by
  unfold dd refl; split_ifs <;> omega

lemma prod_image_refl (S : Finset ℤ) :
    ∏ s ∈ S.image refl, (X - C (s : ℚ)) =
      C ((-1 : ℚ) ^ S.card) * (∏ s ∈ S, (X - C (s : ℚ))).comp (-X - 1) := by
  rw [Finset.prod_image (fun a _ b _ h => refl_injective h), Polynomial.prod_comp,
    show C ((-1 : ℚ) ^ S.card) = ∏ _s ∈ S, C (-1 : ℚ) by rw [Finset.prod_const, map_pow],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [refl, sub_comp, X_comp, C_comp]
  push_cast
  simp only [C_sub, C_neg, C_1]
  ring

/-- The numerator of `g(-1-x)` over the poles `-1-r`, where `g = A / ∏_{r ∈ Pl}(x - r)`. -/
noncomputable def reflNum (Pl : Finset ℤ) (A : ℚ[X]) : ℚ[X] :=
  C ((-1 : ℚ) ^ Pl.card) * A.comp (-X - 1)

/-- **ZC03, reflection**: `τ_X(g(-1-x)) = -τ_X(g(x))` for `g = A / ∏_{r ∈ Pl} (x - r)`. -/
theorem tauX_reflect (A : ℚ[X]) (Pl : Finset ℤ) :
    tauX (reflNum Pl A) (Pl.image refl) = -tauX A Pl := by
  have hA := partial_fractionsP A Pl
  set Q := polyPart A Pl with hQ
  set ρ : ℤ → ℚ := resP A Pl with hρ
  have hpi : piPl (Pl.image refl) = C ((-1 : ℚ) ^ Pl.card) * (piPl Pl).comp (-X - 1) := by
    unfold piPl; exact prod_image_refl Pl
  have hdec : reflNum Pl A = Q.comp (-X - 1) * piPl (Pl.image refl) +
      ∑ r' ∈ Pl.image refl, C (-ρ (refl r')) * ∏ s ∈ (Pl.image refl).erase r', (X - C (s : ℚ)) := by
    rw [Finset.sum_image (fun a _ b _ h => refl_injective h), hpi]
    have hterm : ∀ r ∈ Pl, C (-ρ (refl (refl r))) *
        ∏ s ∈ (Pl.image refl).erase (refl r), (X - C (s : ℚ)) =
        C ((-1 : ℚ) ^ Pl.card) * (C (ρ r) * (∏ s ∈ Pl.erase r, (X - C (s : ℚ))).comp (-X - 1)) := by
      intro r hr
      rw [refl_refl, ← Finset.image_erase refl_injective, prod_image_refl,
        Finset.card_erase_of_mem hr]
      have hc : 1 ≤ Pl.card := Finset.card_pos.mpr ⟨r, hr⟩
      obtain ⟨m, hm⟩ : ∃ m, Pl.card = m + 1 := ⟨Pl.card - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ]
      simp only [map_mul, map_neg, map_one]
      ring
    rw [Finset.sum_congr rfl hterm, reflNum]
    conv_lhs => rw [hA]
    rw [add_comp, mul_comp, sum_comp', mul_add, Finset.mul_sum]
    simp only [mul_comp, C_comp]
    ring
  have hT : tauX A Pl = C (tau Q) + ∑ r ∈ Pl, C (ρ r) * (C (H5 (dd r)) - X) := rfl
  rw [tauX_of_decomp _ _ _ _ hdec, tau_comp_neg_sub_one,
    Finset.sum_image (fun a _ b _ h => refl_injective h), hT]
  simp only [refl_refl, dd_refl, C_neg]
  rw [neg_add]
  congr 1
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun r _ => by ring

end Apery
