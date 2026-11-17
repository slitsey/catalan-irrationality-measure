module

public import CatalanCore.Content.ShiftLemma
public import CatalanCore.Content.WeightedDet
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# `CatalanCore.Content.ContentLaw`: generic mod-`p` / mod-`p²` lemmas for the Lai content law

Theorem side, no Lai numbers (content notes `N9-LAI-CONTENT-2026-11-16.md`,
`N9-LAI-CONTENT-EXACT-2026-11-16.md`).  Parts, in order:

* `Faulhaber`: the Faulhaber bridge `∑_{s<p} G(s) = p y`, `y ≡ ∫G` (closes Lemma SH with `ShiftLemma`);
* `FactorialMod`: `∏(cp+i) ≡ e!(1+cpH_e)`, `(-1)^m C(p-1,m) ≡ 1 - pH_m`, digit factorials mod `p²`
  (the ingredients of Lemmas G and R);
* `AntonGranville`: two-digit Kummer + Anton–Granville unit parts (Lemma N items 1-2, content Lemma 2.3);
* `Hankel`: Lemma H (generic local Hankel matrices are regular);
* `Greedy`: Lemmas S and T (greedy shape; the identity `2d + |N| + 2 = p(2q₆ - 3q₂ - 2 - λ)`).
-/

section PartFaulhaber
/-!
# The Faulhaber bridge modulo `p²` (content note, Theorem E2 step 7, Lemma SH)

For `G` of degree `≤ p - 2` over any commutative ring `R`:

  `∑_{s<p} G(s) = p · y`   with   `y ≡ ∑_{m<p} G(m) H_m  (mod p)`

(`faulhaber_bridge`).  The common value is `∫G`.  No Bernoulli number is used: the integers
`y_e = (∑_{s<p} s^e)/p` and the residues `z_e = ∑_{s<p} s^e H_s ∈ 𝔽_p` satisfy the same triangular
recursion `∑_{k≤e} C(e+1, k) w_k = [e = 0]` (from `∑_{s<p} ((s+1)^{e+1} - s^{e+1}) = p^{e+1}` and by
summation by parts for `H_s`), whose leading coefficient `e + 1` is a unit for `e ≤ p - 2`.
-/

open Finset Polynomial CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Content

variable {p : ℕ} [hp : Fact p.Prime]

/-- Power sum `S_e = ∑_{s<p} s^e` over `ℤ`. -/
def psum (p e : ℕ) : ℤ := ∑ s ∈ range p, (s : ℤ) ^ e

/-- `z_e = ∑_{s<p} s^e H_s ∈ 𝔽_p`. -/
def zsum (p : ℕ) [Fact p.Prime] (e : ℕ) : ZMod p :=
  ∑ s ∈ range p, ((s : ℕ) : ZMod p) ^ e * harm p s

lemma psum_zero : psum p 0 = p := by simp [psum]

lemma psum_cast (e : ℕ) : ((psum p e : ℤ) : ZMod p) = ∑ s ∈ range p, ((s : ℕ) : ZMod p) ^ e := by
  simp [psum]

lemma psum_dvd (e : ℕ) (he : e ≤ p - 2) : (p : ℤ) ∣ psum p e := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, psum_cast]
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0; simp
  · exact sum_range_pow p e (by have := hp.out.two_le; omega)

/-- `y_e = S_e / p`. -/
def ysum (p e : ℕ) : ℤ := psum p e / p

lemma psum_eq (e : ℕ) (he : e ≤ p - 2) : psum p e = p * ysum p e := by
  unfold ysum
  exact (Int.mul_ediv_cancel' (psum_dvd e he)).symm

/-- `∑_{k ≤ e} C(e+1,k) S_k = p^{e+1}`. -/
lemma psum_rec (e : ℕ) :
    ∑ k ∈ range (e + 1), ((e + 1).choose k : ℤ) * psum p k = (p : ℤ) ^ (e + 1) := by
  have h1 : ∑ s ∈ range p, (((s + 1 : ℕ) : ℤ) ^ (e + 1) - (s : ℤ) ^ (e + 1)) = (p : ℤ) ^ (e + 1) := by
    have := Finset.sum_range_sub (fun s : ℕ => ((s : ℕ) : ℤ) ^ (e + 1)) p
    simpa using this
  rw [← h1]
  have h2 : ∀ s : ℕ, (((s + 1 : ℕ) : ℤ) ^ (e + 1) - (s : ℤ) ^ (e + 1)) =
      ∑ k ∈ range (e + 1), ((e + 1).choose k : ℤ) * (s : ℤ) ^ k := by
    intro s
    have := add_pow (s : ℤ) 1 (e + 1)
    push_cast
    rw [this, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
    rw [add_sub_cancel_right]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  simp only [h2]
  rw [Finset.sum_comm]
  simp [psum, Finset.mul_sum]

/-- recursion for the residues `y_e` -/
lemma ysum_rec (e : ℕ) (he : e ≤ p - 2) :
    ∑ k ∈ range (e + 1), (((e + 1).choose k : ℕ) : ZMod p) * ((ysum p k : ℤ) : ZMod p) =
      if e = 0 then 1 else 0 := by
  have h := psum_rec (p := p) e
  have hk : ∀ k ∈ range (e + 1), ((e + 1).choose k : ℤ) * psum p k =
      (p : ℤ) * (((e + 1).choose k : ℤ) * ysum p k) := by
    intro k hk
    have := psum_eq (p := p) k (by have := Finset.mem_range.1 hk; omega)
    rw [this]; ring
  rw [Finset.sum_congr rfl hk, ← Finset.mul_sum] at h
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    simp only [zero_add, range_one, sum_singleton, Nat.choose_zero_right, Nat.cast_one, one_mul,
      pow_one, if_true] at h ⊢
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have : ysum p 0 = 1 := by
      have := mul_left_cancel₀ hp0 (h.trans (mul_one _).symm)
      exact this
    simp [this]
  · have hdiv : (p : ℤ) * ∑ k ∈ range (e + 1), ((e + 1).choose k : ℤ) * ysum p k = (p : ℤ) * (p : ℤ) ^ e := by
      rw [h]; ring
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have h3 := mul_left_cancel₀ hp0 hdiv
    have h4 : ((∑ k ∈ range (e + 1), ((e + 1).choose k : ℤ) * ysum p k : ℤ) : ZMod p) = 0 := by
      rw [h3]; push_cast
      have : (p : ZMod p) = 0 := ZMod.natCast_self p
      rw [this]; exact zero_pow (by omega)
    push_cast at h4
    simpa [Nat.pos_iff_ne_zero.1 hpos] using h4

lemma abel_step (F : ℕ → ZMod p) (h0 : F 0 = 0) (hpF : F p = 0) :
    ∑ s ∈ range p, (F (s + 1) - F s) * harm p s = - ∑ s ∈ range p, F (s + 1) * (((s + 1 : ℕ) : ZMod p))⁻¹ := by
  have e1 : ∀ s ∈ range p, (F (s + 1) - F s) * harm p s =
      F (s + 1) * harm p (s + 1) - F s * harm p s - F (s + 1) * (((s + 1 : ℕ) : ZMod p))⁻¹ := by
    intro s _
    rw [harm_succ]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h2 : ∑ x ∈ range p, F (x + 1) * harm p (x + 1) - ∑ x ∈ range p, F x * harm p x = 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun s => F s * harm p s) p]
    simp [hpF, h0]
  linear_combination h2

lemma zsum_rec (e : ℕ) (he : e ≤ p - 2) :
    ∑ k ∈ range (e + 1), (((e + 1).choose k : ℕ) : ZMod p) * zsum p k = if e = 0 then 1 else 0 := by
  set F : ℕ → ZMod p := fun m => ((m : ℕ) : ZMod p) ^ (e + 1) with hF
  have hF0 : F 0 = 0 := by simp [hF]
  have hFp : F p = 0 := by simp [hF, ZMod.natCast_self]
  have key := abel_step (p := p) F hF0 hFp
  have hl : ∀ s ∈ range p, (F (s + 1) - F s) * harm p s =
      ∑ k ∈ range (e + 1), (((e + 1).choose k : ℕ) : ZMod p) * (((s : ℕ) : ZMod p) ^ k * harm p s) := by
    intro s _
    have := add_pow (((s : ℕ) : ZMod p)) 1 (e + 1)
    simp only [hF]
    push_cast
    rw [this, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
    rw [add_sub_cancel_right, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [Finset.sum_congr rfl hl, Finset.sum_comm] at key
  have hl2 : ∑ k ∈ range (e + 1), (((e + 1).choose k : ℕ) : ZMod p) * zsum p k =
      ∑ k ∈ range (e + 1), ∑ s ∈ range p,
        (((e + 1).choose k : ℕ) : ZMod p) * (((s : ℕ) : ZMod p) ^ k * harm p s) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [zsum, Finset.mul_sum]
  rw [hl2, key]
  -- the right side
  have hr : ∑ s ∈ range p, F (s + 1) * (((s + 1 : ℕ) : ZMod p))⁻¹ =
      ∑ s ∈ range (p - 1), (((s + 1 : ℕ) : ZMod p)) ^ e := by
    have hr1 : range p = range ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp.out.one_le]
    rw [hr1, Finset.sum_range_succ]
    have hlast : F (p - 1 + 1) = 0 := by
      rw [Nat.sub_add_cancel hp.out.one_le]; exact hFp
    rw [hlast, zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_range.1 hs
    have hne := cast_succ_ne_zero p (j := s) (by have := hp.out.two_le; omega)
    simp only [hF]
    rw [pow_succ, mul_assoc, mul_comm _ ((((s + 1 : ℕ) : ZMod p))⁻¹), inv_mul_cancel₀ hne, mul_one]
  rw [hr]
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    simp only [pow_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, if_true]
    rw [Nat.cast_sub hp.out.one_le, ZMod.natCast_self]; simp
  · have h := sum_range_pow p e (by omega)
    rw [sum_shift p (fun m => ((m : ℕ) : ZMod p) ^ e) (by simp [Nat.pos_iff_ne_zero.1 hpos])
      hp.out.one_le] at h
    simp only [Nat.pos_iff_ne_zero.1 hpos, if_false]
    rw [show (∑ s ∈ range (p - 1), (((s + 1 : ℕ) : ZMod p)) ^ e) = 0 from h]
    simp

/-- the two recursions give `y_e ≡ z_e (mod p)` for `e ≤ p - 2`. -/
theorem ysum_eq_zsum (e : ℕ) (he : e ≤ p - 2) : ((ysum p e : ℤ) : ZMod p) = zsum p e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    have h1 := ysum_rec (p := p) e he
    have h2 := zsum_rec (p := p) e he
    rw [Finset.sum_range_succ] at h1 h2
    simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one] at h1 h2
    have hlow : ∑ k ∈ range e, (((e + 1).choose k : ℕ) : ZMod p) * ((ysum p k : ℤ) : ZMod p) =
        ∑ k ∈ range e, (((e + 1).choose k : ℕ) : ZMod p) * zsum p k := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [ih k (Finset.mem_range.1 hk) (by have := Finset.mem_range.1 hk; omega)]
    have hu : ((e : ZMod p) + 1) ≠ 0 := by
      have := cast_succ_ne_zero p (j := e) (by have := hp.out.two_le; omega)
      simpa using this
    apply mul_left_cancel₀ hu
    rw [hlow] at h1
    linear_combination h1 - h2

/-- **Faulhaber bridge.**  For `G` over any commutative ring `R` of degree `≤ p - 2`, there is
`y ∈ R` with `∑_{s<p} G(s) = p y` whose image in every characteristic-`p` quotient is `∫G`. -/
theorem faulhaber_bridge {R : Type*} [CommRing R] (G : R[X]) (hdeg : G.natDegree ≤ p - 2) :
    ∃ y : R, ∑ s ∈ range p, G.eval ((s : ℕ) : R) = (p : R) * y ∧
      ∀ (K : Type*) [CommRing K] [CharP K p] (π : R →+* K), π y = harmSum p (G.map π) := by
  have hN : G.natDegree < p - 1 := by have := hp.out.two_le; omega
  refine ⟨∑ e ∈ range (p - 1), G.coeff e * ((ysum p e : ℤ) : R), ?_, ?_⟩
  · have e1 : ∀ s ∈ range p, G.eval ((s : ℕ) : R) = ∑ e ∈ range (p - 1), G.coeff e * ((s : ℕ) : R) ^ e :=
      fun s _ => eval_eq_sum_range' hN _
    rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have h := psum_eq (p := p) e (by have := Finset.mem_range.1 he; omega)
    have h' : ((psum p e : ℤ) : R) = (p : R) * ((ysum p e : ℤ) : R) := by
      have := congrArg (fun z : ℤ => (z : R)) h
      simpa using this
    have h'' : ∑ s ∈ range p, ((s : ℕ) : R) ^ e = ((psum p e : ℤ) : R) := by simp [psum]
    calc ∑ s ∈ range p, G.coeff e * ((s : ℕ) : R) ^ e
        = G.coeff e * ∑ s ∈ range p, ((s : ℕ) : R) ^ e := by rw [Finset.mul_sum]
      _ = (p : R) * (G.coeff e * ((ysum p e : ℤ) : R)) := by rw [h'', h']; ring
  · intro K _ _ π
    have hNm : (G.map π).natDegree < p - 1 := lt_of_le_of_lt (natDegree_map_le) hN
    unfold harmSum
    have e1 : ∀ s ∈ range p, (G.map π).eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p s) =
        ∑ e ∈ range (p - 1), π (G.coeff e) *
          ZMod.castHom (dvd_refl p) K (((s : ℕ) : ZMod p) ^ e * harm p s) := by
      intro s _
      rw [eval_eq_sum_range' hNm, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp [coeff_map, map_mul, map_pow, map_natCast]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [← Finset.mul_sum, map_mul]
    congr 1
    have h := ysum_eq_zsum (p := p) e (by have := Finset.mem_range.1 he; omega)
    have : ((ysum p e : ℤ) : K) = ZMod.castHom (dvd_refl p) K ((ysum p e : ℤ) : ZMod p) := by simp
    simp only [map_intCast]
    rw [this, h]
    simp [zsum, map_sum]

end CatalanCore.Content
end PartFaulhaber

section PartFactorialMod
/-!
# Factorials modulo `p²` (content note, Lemmas G and R)

* `prod_shift_mod`: `∏_{i=1}^{e} (c p + i) ≡ e! (1 + c p H_e)  (mod p²)` for `e < p`.
* `choose_reflect_mod`: `(-1)^m C(p-1, m) ≡ 1 - p H_m  (mod p²)` for `m < p`.
* `fact_digits_mod`: for `m = c p + e` with `e < p`,
  `m! ≡ p^c c! (p-1)!^c e! (1 + c p H_e)`  modulo `p^{c+2}`, in the form used for `E_ℓ(s)`:
  the unit part `m!/p^c ≡ c! ((p-1)!)^c e! (1 + c p H_e)  (mod p²)` for `c < p`.
-/

open Finset CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Content

variable {p : ℕ} [hp : Fact p.Prime]

/-- Harmonic number in `ZMod (p²)`. -/
def Hz (p : ℕ) (m : ℕ) : ZMod (p ^ 2) := ∑ i ∈ range m, (((i + 1 : ℕ) : ZMod (p ^ 2)))⁻¹

lemma isUnit_cast_p2 {i : ℕ} (h1 : 1 ≤ i) (h2 : i < p) : IsUnit ((i : ℕ) : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega))).symm

lemma pp_sq : ((p : ℕ) : ZMod (p ^ 2)) * ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
  rw [← Nat.cast_mul, ← pow_two]; exact ZMod.natCast_self _

lemma Hz_succ (m : ℕ) : Hz p (m + 1) = Hz p m + (((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹ := by
  unfold Hz; rw [Finset.sum_range_succ]

lemma Hz_zero : Hz p 0 = 0 := by simp [Hz]

/-- `∏_{i=1}^{e} (c p + i) ≡ e! (1 + c p H_e)` modulo `p²`, for `e < p`. -/
theorem prod_shift_mod (c e : ℕ) (he : e < p) :
    (((∏ i ∈ range e, (c * p + (i + 1)) : ℕ)) : ZMod (p ^ 2)) =
      ((e.factorial : ℕ) : ZMod (p ^ 2)) * (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Hz p e) := by
  induction e with
  | zero => simp [Hz_zero]
  | succ e ih =>
    have he' : e < p := by omega
    have hu := isUnit_cast_p2 (p := p) (i := e + 1) (by omega) he
    have hinv : ((e + 1 : ℕ) : ZMod (p ^ 2)) * (((e + 1 : ℕ) : ZMod (p ^ 2)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hu
    rw [Finset.prod_range_succ, Nat.cast_mul, ih he', Hz_succ, Nat.factorial_succ, Nat.cast_mul]
    have hs := pp_sq (p := p)
    push_cast at hinv ⊢
    set P : ZMod (p ^ 2) := (p : ZMod (p ^ 2))
    set I : ZMod (p ^ 2) := ((e : ZMod (p ^ 2)) + 1)⁻¹
    have hinv' : ((e : ZMod (p ^ 2)) + 1) * I = 1 := hinv
    have key : ((c : ZMod (p ^ 2)) * P + ((e : ZMod (p ^ 2)) + 1)) =
        ((e : ZMod (p ^ 2)) + 1) * (1 + (c : ZMod (p ^ 2)) * P * I) := by
      linear_combination (-(c : ZMod (p ^ 2)) * P) * hinv'
    rw [key]
    linear_combination ((((e.factorial : ℕ) : ZMod (p ^ 2))) * ((e : ZMod (p ^ 2)) + 1) * (c : ZMod (p ^ 2)) ^ 2 *
      (Hz p e) * I) * hs

/-- `(-1)^m C(p-1, m) ≡ 1 - p H_m` modulo `p²`, for `m < p`. -/
theorem choose_reflect_mod (m : ℕ) (hm : m < p) :
    (-1 : ZMod (p ^ 2)) ^ m * (((p - 1).choose m : ℕ) : ZMod (p ^ 2)) = 1 - (p : ZMod (p ^ 2)) * Hz p m := by
  induction m with
  | zero => simp [Hz_zero]
  | succ m ih =>
    have hm' : m < p := by omega
    have hu := isUnit_cast_p2 (p := p) (i := m + 1) (by omega) hm
    have hinv : ((m + 1 : ℕ) : ZMod (p ^ 2)) * (((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hu
    have hch : (((p - 1).choose (m + 1) : ℕ) : ZMod (p ^ 2)) * ((m : ZMod (p ^ 2)) + 1) =
        (((p - 1).choose m : ℕ) : ZMod (p ^ 2)) * (((p - 1 - m : ℕ)) : ZMod (p ^ 2)) := by
      have := Nat.choose_succ_right_eq (p - 1) m
      exact_mod_cast congrArg (fun z : ℕ => (z : ZMod (p ^ 2))) this
    have hsub : (((p - 1 - m : ℕ)) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - ((m : ZMod (p ^ 2)) + 1) := by
      have : p - 1 - m + (m + 1) = p := by omega
      have h2 := congrArg (fun z : ℕ => (z : ZMod (p ^ 2))) this
      simp only [Nat.cast_add, Nat.cast_one] at h2
      linear_combination h2
    rw [Hz_succ]
    push_cast at hinv ⊢
    set P : ZMod (p ^ 2) := (p : ZMod (p ^ 2))
    set I : ZMod (p ^ 2) := ((m : ZMod (p ^ 2)) + 1)⁻¹
    set Cm : ZMod (p ^ 2) := (((p - 1).choose m : ℕ) : ZMod (p ^ 2))
    set Cn : ZMod (p ^ 2) := (((p - 1).choose (m + 1) : ℕ) : ZMod (p ^ 2))
    have hinv' : ((m : ZMod (p ^ 2)) + 1) * I = 1 := hinv
    have hs := pp_sq (p := p)
    rw [hsub] at hch
    -- Cn = Cm (P - (m+1)) I
    have hCn : Cn = Cm * (P - ((m : ZMod (p ^ 2)) + 1)) * I := by
      linear_combination (-Cn) * hinv' + I * hch
    rw [hCn]
    have ih' : (-1 : ZMod (p ^ 2)) ^ m * Cm = 1 - P * Hz p m := ih hm'
    calc (-1 : ZMod (p ^ 2)) ^ (m + 1) * (Cm * (P - ((m : ZMod (p ^ 2)) + 1)) * I)
        = ((-1 : ZMod (p ^ 2)) ^ m * Cm) * (-(P - ((m : ZMod (p ^ 2)) + 1)) * I) := by ring
      _ = (1 - P * Hz p m) * (-(P - ((m : ZMod (p ^ 2)) + 1)) * I) := by rw [ih']
      _ = 1 - P * (Hz p m + I) := by
        linear_combination (1 - P * Hz p m) * hinv' + (Hz p m * I) * hs

/-- Reduction of `Hz` to the residue harmonic number. -/
lemma Hz_cast (m : ℕ) (hm : m < p) :
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (Hz p m) = harm p m := by
  induction m with
  | zero => simp [Hz_zero, harm_zero]
  | succ m ih =>
    rw [Hz_succ, harm_succ, map_add, ih (by omega)]
    congr 1
    have hu := isUnit_cast_p2 (p := p) (i := m + 1) (by omega) hm
    have hinv : ((m + 1 : ℕ) : ZMod (p ^ 2)) * (((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hu
    have h2 := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) hinv
    rw [map_mul, map_one] at h2
    simp only [map_natCast] at h2
    exact eq_inv_of_mul_eq_one_right h2


lemma factorial_add_prod (a k : ℕ) : (a + k).factorial = a.factorial * ∏ i ∈ range k, (a + (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, ih, Finset.prod_range_succ]
    rw [show a + k + 1 = a + (k + 1) by ring]
    ring

lemma p_mul_eq_zero_of_cast_zero (x : ZMod (p ^ 2))
    (h : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) x = 0) : (p : ZMod (p ^ 2)) * x = 0 := by
  have hx : x = ((x.val : ℕ) : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val x).symm
  have h1 : (((x.val : ℕ) : ZMod p)) = 0 := by
    have := h
    rw [hx] at this
    simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨k, hk⟩ := h1
  rw [hx, hk]
  push_cast
  have := pp_sq (p := p)
  linear_combination (k : ZMod (p ^ 2)) * this

/-- `(c p)! = p^c w` with `w ≡ c! ((p-1)!)^c` modulo `p²`. -/
lemma fact_mul_p_mod (h3 : 3 ≤ p) (c : ℕ) :
    ∃ w : ℕ, (c * p).factorial = p ^ c * w ∧
      (w : ZMod (p ^ 2)) = (c.factorial : ZMod (p ^ 2)) * ((p - 1).factorial : ZMod (p ^ 2)) ^ c := by
  induction c with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ c ih =>
    obtain ⟨w, hw, hwc⟩ := ih
    have hp1 : 1 ≤ p := hp.out.one_le
    have hfac : ((c + 1) * p).factorial =
        (c * p).factorial * ((∏ i ∈ range (p - 1), (c * p + (i + 1))) * ((c + 1) * p)) := by
      have h := factorial_add_prod (c * p) p
      rw [show (c + 1) * p = c * p + p by ring, h]
      have hr : range p = range ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp1]
      rw [hr, Finset.prod_range_succ]
      congr 2
      rw [show c * p + (p - 1 + 1) = c * p + p by rw [Nat.sub_add_cancel hp1]]
    refine ⟨w * ((c + 1) * ∏ i ∈ range (p - 1), (c * p + (i + 1))), ?_, ?_⟩
    · rw [hfac, hw]; ring
    · have hP := prod_shift_mod (p := p) c (p - 1) (by omega)
      have hH : (p : ZMod (p ^ 2)) * Hz p (p - 1) = 0 := by
        apply p_mul_eq_zero_of_cast_zero
        rw [Hz_cast (p := p) (p - 1) (by omega)]
        exact harm_top h3
      rw [Nat.cast_mul, Nat.cast_mul, hwc, hP, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have : (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Hz p (p - 1) = (c : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * Hz p (p - 1)) := by ring
      rw [this, hH]
      ring

/-- **Unit part of a factorial** with two base-`p` digits: for `m = c p + e`, `e < p`,
`m! = p^c w` with `w ≡ c! ((p-1)!)^c e! (1 + c p H_e)` modulo `p²`. -/
theorem fact_digits_mod (h3 : 3 ≤ p) (c e : ℕ) (he : e < p) :
    ∃ w : ℕ, (c * p + e).factorial = p ^ c * w ∧
      (w : ZMod (p ^ 2)) = (c.factorial : ZMod (p ^ 2)) * ((p - 1).factorial : ZMod (p ^ 2)) ^ c *
        (e.factorial : ZMod (p ^ 2)) * (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Hz p e) := by
  obtain ⟨w, hw, hwc⟩ := fact_mul_p_mod (p := p) h3 c
  refine ⟨w * ∏ i ∈ range e, (c * p + (i + 1)), ?_, ?_⟩
  · rw [factorial_add_prod, hw]; ring
  · rw [Nat.cast_mul, hwc, prod_shift_mod (p := p) c e he]
    ring

end CatalanCore.Content
end PartFactorialMod

section PartAntonGranville
/-!
# Two-digit Anton–Granville (content note, Lemma N, items 1 and 2; Lemma 2.3)

For `m < p²` write `m = c p + e` with `0 ≤ e < p`.  The unit part of `m!` modulo `p` is
`fu m = (-1)^c c! e!`, and `m! = p^c w` with `w ≡ fu m`.  Hence for `a = k + b` (all three `< p²`)

  `C(a, k) = p^{⌊a/p⌋ - ⌊k/p⌋ - ⌊b/p⌋} · u`  with  `u · fu k · fu b ≡ fu a  (mod p)`

(`choose_unit_part`); this is Kummer's theorem for two digits together with the Anton–Granville
unit part, which are what Lemma N consumes.
-/

open Finset

namespace CatalanCore.Content

open Nat ZMod in
/-- **Wilson's lemma** (proof copied from `Mathlib.NumberTheory.Wilson`, which is not built here). -/
theorem wilson (p : ℕ) [Fact p.Prime] : (((p - 1).factorial : ℕ) : ZMod p) = -1 := by
  refine
    calc
      (((p - 1).factorial : ℕ) : ZMod p) = ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)),
          FiniteField.prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  symm
  refine Finset.prod_bij (fun a _ => (a : ZMod p).val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico, ← Nat.succ_sub hp, Nat.add_one_sub_one]
    constructor
    · apply Nat.pos_of_ne_zero; rw [← @ZMod.val_zero p]
      intro h; apply Units.ne_zero a (ZMod.val_injective p h)
    · exact ZMod.val_lt _
  · intro _ _ _ _ h; rw [Units.ext_iff]; exact ZMod.val_injective p h
  · intro b hb
    rw [Finset.mem_Ico, Nat.succ_le_iff, ← Nat.succ_sub hp, Nat.add_one_sub_one, Nat.pos_iff_ne_zero] at hb
    refine ⟨Units.mk0 b ?_, Finset.mem_univ _, ?_⟩
    · intro h; apply hb.1; apply_fun ZMod.val at h
      simpa only [ZMod.val_cast_of_lt hb.right, ZMod.val_zero] using h
    · simp only [ZMod.val_cast_of_lt hb.right, Units.val_mk0]
  · rintro a -; simp only [ZMod.cast_id, ZMod.natCast_val]

variable {p : ℕ} [hp : Fact p.Prime]

/-- Unit part of `m!` modulo `p` (two base-`p` digits). -/
def fu (p m : ℕ) : ZMod p := (-1) ^ (m / p) * ((m / p).factorial : ZMod p) * ((m % p).factorial : ZMod p)

lemma fu_ne_zero (m : ℕ) (hm : m < p ^ 2) : fu p m ≠ 0 := by
  have hc : m / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using hm
  have he : m % p < p := Nat.mod_lt _ hp.out.pos
  unfold fu
  have h1 : ((m / p).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp.out]; omega
  have h2 : ((m % p).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp.out]; omega
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1) h2

/-- `m! = p^{⌊m/p⌋} w` with `w ≡ fu m` (mod `p`), for `p ≥ 3`. -/
theorem fact_unit (h3 : 3 ≤ p) (m : ℕ) (hm : m < p ^ 2) :
    ∃ w : ℕ, m.factorial = p ^ (m / p) * w ∧ ((w : ℕ) : ZMod p) = fu p m := by
  obtain ⟨w, hw, hwc⟩ := fact_digits_mod (p := p) h3 (m / p) (m % p) (Nat.mod_lt _ hp.out.pos)
  refine ⟨w, by rw [← hw, Nat.div_add_mod' m p], ?_⟩
  have h2 := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) hwc
  simp only [map_natCast, map_mul, map_pow, map_add, map_one] at h2
  have hw1 : (((p - 1).factorial : ℕ) : ZMod p) = -1 := wilson p
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  rw [h2, hw1, hp0]
  unfold fu
  ring

/-- **Two-digit Kummer + Anton–Granville.** -/
theorem choose_unit_part (h3 : 3 ≤ p) (k b : ℕ) (hab : k + b < p ^ 2) :
    ∃ u : ℕ, (k + b).choose k = p ^ ((k + b) / p - k / p - b / p) * u ∧
      ((u : ℕ) : ZMod p) * fu p k * fu p b = fu p (k + b) := by
  have hk : k < p ^ 2 := by omega
  have hb : b < p ^ 2 := by omega
  obtain ⟨wa, ha, hac⟩ := fact_unit h3 (k + b) hab
  obtain ⟨wk, hk', hkc⟩ := fact_unit h3 k hk
  obtain ⟨wb, hb', hbc⟩ := fact_unit h3 b hb
  have hsup : k / p + b / p ≤ (k + b) / p := by
    rw [Nat.le_div_iff_mul_le hp.out.pos]
    have := Nat.div_mul_le_self k p
    have := Nat.div_mul_le_self b p
    nlinarith
  have hrel : (k + b).factorial = (k + b).choose k * k.factorial * b.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + b by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact h.symm
  rw [ha, hk', hb'] at hrel
  -- cancel the common power of p
  have hpos : 0 < p ^ (k / p + b / p) := pow_pos hp.out.pos _
  have hexp : p ^ ((k + b) / p) = p ^ (k / p + b / p) * p ^ ((k + b) / p - k / p - b / p) := by
    rw [← pow_add]; congr 1; omega
  have hrel2 : wa * p ^ ((k + b) / p - k / p - b / p) = (k + b).choose k * (wk * wb) := by
    have h := hrel
    rw [hexp] at h
    have h' : p ^ (k / p + b / p) * (wa * p ^ ((k + b) / p - k / p - b / p)) =
        p ^ (k / p + b / p) * ((k + b).choose k * (wk * wb)) := by
      calc _ = p ^ (k / p + b / p) * p ^ ((k + b) / p - k / p - b / p) * wa := by ring
        _ = _ := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  -- p^v divides C * (wk * wb) and is coprime to wk wb
  have hwk : Nat.Coprime p wk := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out, ← ZMod.natCast_eq_zero_iff, hkc]
    exact fu_ne_zero k hk
  have hwb : Nat.Coprime p wb := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out, ← ZMod.natCast_eq_zero_iff, hbc]
    exact fu_ne_zero b hb
  have hcop : Nat.Coprime (p ^ ((k + b) / p - k / p - b / p)) (wk * wb) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hwk hwb)
  have hdvd : p ^ ((k + b) / p - k / p - b / p) ∣ (k + b).choose k := by
    have : p ^ ((k + b) / p - k / p - b / p) ∣ (k + b).choose k * (wk * wb) :=
      ⟨wa, by rw [← hrel2]; ring⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, hu, ?_⟩
  have hpv : 0 < p ^ ((k + b) / p - k / p - b / p) := pow_pos hp.out.pos _
  have hfin : wa = u * (wk * wb) := by
    have : p ^ ((k + b) / p - k / p - b / p) * wa =
        p ^ ((k + b) / p - k / p - b / p) * (u * (wk * wb)) := by
      calc _ = wa * p ^ ((k + b) / p - k / p - b / p) := by ring
        _ = (k + b).choose k * (wk * wb) := hrel2
        _ = _ := by rw [hu]; ring
    exact Nat.eq_of_mul_eq_mul_left hpv this
  have := congrArg (fun z : ℕ => (z : ZMod p)) hfin
  simp only [Nat.cast_mul] at this
  rw [hac, hkc, hbc] at this
  rw [this]; ring

end CatalanCore.Content
end PartAntonGranville

section PartHankel
/-!
# Generic local Hankel matrices are regular (content note, Lemma H)

Let `x : ι → F` be injective nodes in a field `F` and `m : ι → ℕ` multiplicities in `{0, 1, 2}`,
`μ = ∑ m`.  The functional `𝓛(φ) = ∑_{m = 2} φ'(x) + ∑_{m = 1} φ(x)` has an invertible Hankel matrix
`(𝓛(y^{i+j}))_{i,j<μ}` (`hankel_det_ne_zero`).  Consequently the Hankel determinant of the generic
functional `𝓛_T(φ) = ∑_ℓ [T^v_ℓ φ(x_ℓ) + T^u_ℓ φ'(x_ℓ)]` is a nonzero polynomial in the
indeterminates `T` (`hankel_generic_ne_zero`), for `μ ≤ 2L`, whenever the `x_ℓ` are distinct.
-/

open Finset Polynomial

namespace CatalanCore.Content

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The functional with node multiplicities `m ∈ {0,1,2}`. -/
noncomputable def Lfun (x : ι → F) (m : ι → ℕ) : F[X] →ₗ[F] F where
  toFun φ := ∑ l, if m l = 2 then φ.derivative.eval (x l) else if m l = 1 then φ.eval (x l) else 0
  map_add' φ ψ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  map_smul' c φ := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp [Polynomial.smul_eq_C_mul, Polynomial.derivative_C_mul]

lemma Lfun_apply (x : ι → F) (m : ι → ℕ) (φ : F[X]) :
    Lfun x m φ = ∑ l, if m l = 2 then φ.derivative.eval (x l) else if m l = 1 then φ.eval (x l) else 0 := rfl

lemma term_zero_of_dvd {a : F} {h : F[X]} {k : ℕ} (hk : k ≤ 2) (hd : (X - C a) ^ k ∣ h) :
    (k = 2 → h.derivative.eval a = 0) ∧ (k = 1 → h.eval a = 0) := by
  obtain ⟨g, rfl⟩ := hd
  refine ⟨fun h2 => ?_, fun h1 => ?_⟩
  · subst h2
    simp [derivative_mul, derivative_pow]
  · subst h1
    simp

/-- The product polynomial `ω = ∏ (X - x_ℓ)^{m_ℓ}`. -/
noncomputable def omegaP (x : ι → F) (m : ι → ℕ) : F[X] := ∏ l, (X - C (x l)) ^ m l

lemma omegaP_natDegree (x : ι → F) (m : ι → ℕ) : (omegaP x m).natDegree = ∑ l, m l := by
  unfold omegaP
  rw [natDegree_prod_of_monic _ _ (fun l _ => (monic_X_sub_C _).pow _)]
  simp [natDegree_pow]

lemma omegaP_monic (x : ι → F) (m : ι → ℕ) : (omegaP x m).Monic :=
  monic_prod_of_monic _ _ (fun l _ => (monic_X_sub_C _).pow _)

/-- If `φ·ψ` is `𝓛`-null for every `ψ` of degree `< μ`, then `ω ∣ φ`. -/
theorem omega_dvd_of_null (x : ι → F) (hx : Function.Injective x) (m : ι → ℕ)
    (hm : ∀ l, m l ≤ 2) (φ : F[X])
    (hnull : ∀ ψ : F[X], ψ.natDegree < ∑ l, m l → Lfun x m (φ * ψ) = 0) :
    omegaP x m ∣ φ := by
  classical
  -- jets vanish at each node
  have hjet : ∀ l₀, 1 ≤ m l₀ → φ.eval (x l₀) = 0 ∧ (m l₀ = 2 → φ.derivative.eval (x l₀) = 0) := by
    intro l₀ hl₀
    set G : F[X] := ∏ l ∈ univ.erase l₀, (X - C (x l)) ^ m l with hG
    have hGmon : G.Monic := monic_prod_of_monic _ _ (fun l _ => (monic_X_sub_C _).pow _)
    have hGdeg : G.natDegree = (∑ l, m l) - m l₀ := by
      rw [hG, natDegree_prod_of_monic _ _ (fun l _ => (monic_X_sub_C _).pow _)]
      simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
      have := Finset.sum_erase_add univ m (Finset.mem_univ l₀)
      omega
    have hr : G.eval (x l₀) ≠ 0 := by
      rw [hG, eval_prod, Finset.prod_ne_zero_iff]
      intro l hl
      have hne : x l₀ ≠ x l := fun h => (Finset.ne_of_mem_erase hl) (hx h).symm
      simp [sub_ne_zero.2 hne]
    -- the other nodes see `φ ψ` vanish to order `m l`
    have hother : ∀ ψ : F[X], G ∣ ψ → ∀ l ∈ univ.erase l₀,
        (if m l = 2 then (φ * ψ).derivative.eval (x l) else if m l = 1 then (φ * ψ).eval (x l) else 0) = 0 := by
      intro ψ hψ l hl
      have hd : (X - C (x l)) ^ m l ∣ φ * ψ :=
        Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ hl).trans hψ) φ
      have := term_zero_of_dvd (hm l) hd
      split_ifs with h2 h1
      · exact this.1 h2
      · exact this.2 h1
      · rfl
    have hsplit : ∀ ψ : F[X], Lfun x m (φ * ψ) =
        (if m l₀ = 2 then (φ * ψ).derivative.eval (x l₀) else if m l₀ = 1 then (φ * ψ).eval (x l₀) else 0) +
        ∑ l ∈ univ.erase l₀, (if m l = 2 then (φ * ψ).derivative.eval (x l)
          else if m l = 1 then (φ * ψ).eval (x l) else 0) := by
      intro ψ
      rw [Lfun_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ l₀)]
    by_cases h2 : m l₀ = 2
    · -- double node: ψ = G·(a + b (X - x₀))
      have hdeg : ∀ a b : F, (G * (C a + C b * (X - C (x l₀)))).natDegree < ∑ l, m l := by
        intro a b
        have h1 : (C a + C b * (X - C (x l₀))).natDegree ≤ 1 := by
          refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
          refine (natDegree_mul_le).trans ?_
          simp
        have hGne : G ≠ 0 := hGmon.ne_zero
        have h3 := natDegree_mul_le (p := G) (q := C a + C b * (X - C (x l₀)))
        have h4 : (∑ l, m l) - m l₀ + 1 < ∑ l, m l := by
          have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l₀)
          omega
        omega
      have hnl : ∀ a b : F, Lfun x m (φ * (G * (C a + C b * (X - C (x l₀))))) =
          φ.derivative.eval (x l₀) * (G.eval (x l₀) * a) +
          φ.eval (x l₀) * (G.derivative.eval (x l₀) * a + G.eval (x l₀) * b) := by
        intro a b
        rw [hsplit, Finset.sum_eq_zero (hother _ (dvd_mul_right _ _))]
        simp only [h2, if_true, add_zero, derivative_mul, derivative_add, derivative_C, zero_add,
          derivative_X, derivative_sub, sub_zero, mul_one, eval_mul, eval_add, eval_C, eval_sub,
          eval_X, sub_self, mul_zero]
      have e1 := hnull _ (hdeg 0 1)
      have e2 := hnull _ (hdeg 1 0)
      rw [hnl] at e1 e2
      simp at e1 e2
      have hφ0 : φ.eval (x l₀) = 0 := by
        rcases e1 with h | h
        · exact h
        · exact absurd h hr
      refine ⟨hφ0, fun _ => ?_⟩
      rw [hφ0] at e2
      simp at e2
      rcases e2 with h | h
      · exact h
      · exact absurd h hr
    · have h1 : m l₀ = 1 := by have := hm l₀; omega
      have hdeg : G.natDegree < ∑ l, m l := by
        have := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l₀)
        omega
      have e := hnull G hdeg
      rw [hsplit, Finset.sum_eq_zero (hother _ dvd_rfl)] at e
      simp only [h1, h2, if_false, if_true, add_zero, eval_mul] at e
      have : φ.eval (x l₀) = 0 := by
        rcases mul_eq_zero.1 e with h | h
        · exact h
        · exact absurd h hr
      exact ⟨this, fun h => absurd h h2⟩
  -- assemble divisibility
  unfold omegaP
  refine Finset.prod_dvd_of_coprime ?_ (fun l _ => ?_)
  · intro a _ b _ hab
    exact ((Polynomial.pairwise_coprime_X_sub_C hx) hab).pow
  · by_cases h0 : m l = 0
    · simp [h0]
    obtain ⟨j1, j2⟩ := hjet l (by omega)
    by_cases h2 : m l = 2
    · rw [h2]
      have hd1 : (X - C (x l)) ∣ φ := dvd_iff_isRoot.2 j1
      obtain ⟨ψ, hψ⟩ := hd1
      have hz : ψ.eval (x l) = 0 := by
        have := j2 h2
        rw [hψ] at this
        simpa [derivative_mul] using this
      obtain ⟨κ, hκ⟩ := dvd_iff_isRoot.2 hz
      exact ⟨κ, by rw [hψ, hκ]; ring⟩
    · have h1 : m l = 1 := by have := hm l; omega
      rw [h1, pow_one]
      exact dvd_iff_isRoot.2 j1

/-- No nonzero `φ` of degree `< μ` is `𝓛`-null. -/
theorem null_eq_zero (x : ι → F) (hx : Function.Injective x) (m : ι → ℕ) (hm : ∀ l, m l ≤ 2)
    (φ : F[X]) (hφ : φ.natDegree < ∑ l, m l)
    (hnull : ∀ ψ : F[X], ψ.natDegree < ∑ l, m l → Lfun x m (φ * ψ) = 0) : φ = 0 := by
  have hd := omega_dvd_of_null x hx m hm φ hnull
  refine eq_zero_of_dvd_of_natDegree_lt hd ?_
  rwa [omegaP_natDegree]

/-- **Lemma H at the special point.** -/
theorem hankel_det_ne_zero (x : ι → F) (hx : Function.Injective x) (m : ι → ℕ) (hm : ∀ l, m l ≤ 2)
    (μ : ℕ) (hμ : μ = ∑ l, m l) :
    (Matrix.of fun i j : Fin μ => Lfun x m ((X : F[X]) ^ ((i : ℕ) + (j : ℕ)))).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set φ : F[X] := ∑ j : Fin μ, C (v j) * X ^ (j : ℕ) with hφ
  have hφdeg : φ.natDegree < μ ∨ φ = 0 := by
    by_cases h0 : φ = 0
    · exact Or.inr h0
    refine Or.inl ?_
    rw [hφ]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := μ - 1) ?_) ?_
    · intro j _
      refine (natDegree_C_mul_X_pow_le _ _).trans ?_
      have := j.2; omega
    · by_contra hcon
      have hμ0 : μ = 0 := by omega
      subst hμ0
      exact hv0 (funext (fun j => j.elim0))
  have hrow : ∀ i : Fin μ, Lfun x m ((X : F[X]) ^ (i : ℕ) * φ) = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hφ, Finset.mul_sum, map_sum]
    rw [← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show (X : F[X]) ^ (i : ℕ) * (C (v j) * X ^ (j : ℕ)) = (v j) • X ^ ((i : ℕ) + (j : ℕ)) by
      rw [smul_eq_C_mul, pow_add]; ring, map_smul, smul_eq_mul]
    ring
  have hnull : ∀ ψ : F[X], ψ.natDegree < ∑ l, m l → Lfun x m (φ * ψ) = 0 := by
    intro ψ hψ
    rw [← hμ] at hψ
    have hψs : ψ = ∑ i ∈ range μ, C (ψ.coeff i) * X ^ i := by
      conv_lhs => rw [as_sum_range' ψ μ hψ]
      exact Finset.sum_congr rfl (fun i _ => C_mul_X_pow_eq_monomial.symm)
    rw [hψs, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    have := hrow ⟨i, hi'⟩
    rw [show φ * (C (ψ.coeff i) * X ^ i) = (ψ.coeff i) • ((X : F[X]) ^ i * φ) by
      rw [smul_eq_C_mul]; ring, map_smul, this, smul_zero]
  have hφ0 : φ = 0 := by
    rcases hφdeg with h | h
    · exact null_eq_zero x hx m hm φ (by rwa [← hμ]) hnull
    · exact h
  apply hv0
  funext j
  have hc : φ.coeff (j : ℕ) = v j := by
    rw [hφ, finset_sum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have : (j : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  rw [← hc, hφ0]; simp


lemma exists_mult (L : ℕ) : ∀ μ : ℕ, μ ≤ 2 * L → ∃ m : Fin L → ℕ, (∀ l, m l ≤ 2) ∧ ∑ l, m l = μ := by
  induction L with
  | zero => intro μ h; exact ⟨fun l => l.elim0, fun l => l.elim0, by simp; omega⟩
  | succ L ih =>
    intro μ h
    obtain ⟨m, hm, hs⟩ := ih (μ - 2) (by omega)
    refine ⟨Fin.cons (min 2 μ) m, ?_, ?_⟩
    · intro l
      refine Fin.cases ?_ (fun l => ?_) l
      · simp
      · simpa using hm l
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hs]; omega

/-- **Lemma H.**  The Hankel determinant of the generic local functional is a nonzero polynomial
in the node constants `T`, for any `μ ≤ 2L` and distinct nodes. -/
theorem hankel_generic_ne_zero (L μ : ℕ) (hμ : μ ≤ 2 * L) (x : Fin L → F)
    (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin μ => ∑ l : Fin L,
      (MvPolynomial.X (l, true) * MvPolynomial.C (x l ^ ((i : ℕ) + (j : ℕ))) +
       MvPolynomial.X (l, false) *
         MvPolynomial.C ((((i : ℕ) + (j : ℕ) : ℕ) : F) * x l ^ ((i : ℕ) + (j : ℕ) - 1))) :
        Matrix (Fin μ) (Fin μ) (MvPolynomial (Fin L × Bool) F)).det ≠ 0 := by
  obtain ⟨m, hm, hs⟩ := exists_mult L μ hμ
  intro h0
  set τ : Fin L × Bool → F := fun lb => if lb.2 = true then (if m lb.1 = 1 then 1 else 0)
    else (if m lb.1 = 2 then 1 else 0) with hτ
  have key := RingHom.map_det (MvPolynomial.eval τ) (Matrix.of fun i j : Fin μ => ∑ l : Fin L,
      (MvPolynomial.X (l, true) * MvPolynomial.C (x l ^ ((i : ℕ) + (j : ℕ))) +
       MvPolynomial.X (l, false) *
         MvPolynomial.C ((((i : ℕ) + (j : ℕ) : ℕ) : F) * x l ^ ((i : ℕ) + (j : ℕ) - 1))) :
        Matrix (Fin μ) (Fin μ) (MvPolynomial (Fin L × Bool) F))
  rw [h0, map_zero] at key
  have hmat : (MvPolynomial.eval τ).mapMatrix (Matrix.of fun i j : Fin μ => ∑ l : Fin L,
      (MvPolynomial.X (l, true) * MvPolynomial.C (x l ^ ((i : ℕ) + (j : ℕ))) +
       MvPolynomial.X (l, false) *
         MvPolynomial.C ((((i : ℕ) + (j : ℕ) : ℕ) : F) * x l ^ ((i : ℕ) + (j : ℕ) - 1))) :
        Matrix (Fin μ) (Fin μ) (MvPolynomial (Fin L × Bool) F)) =
      Matrix.of fun i j : Fin μ => Lfun x m ((X : F[X]) ^ ((i : ℕ) + (j : ℕ))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_add,
      map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Lfun_apply, derivative_X_pow, eval_mul,
      eval_pow, eval_X, eval_C, eval_natCast, hτ]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have := hm l
    by_cases h2 : m l = 2
    · simp [h2]
    · by_cases h1 : m l = 1
      · simp [h1]
      · simp [h1, h2]
  rw [hmat] at key
  exact hankel_det_ne_zero x hx m hm μ hs.symm key.symm

/-- the nodes `x_ℓ = -(ℓ+1)` are distinct in characteristic `p > L`. -/
lemma nodes_injective {K : Type*} [Field K] (p : ℕ) [CharP K p] (L : ℕ) (hL : L ≤ p) :
    Function.Injective (fun l : Fin L => -(((l : ℕ) + 1 : ℕ) : K)) := by
  intro a b h
  have h' : (((a : ℕ) + 1 : ℕ) : K) = (((b : ℕ) + 1 : ℕ) : K) := neg_inj.1 h
  rw [CharP.natCast_eq_natCast K p] at h'
  have ha := a.2; have hb := b.2
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' 1 h') (by omega) (by omega)

end CatalanCore.Content
end PartHankel

section PartGreedy
/-!
# The greedy shape of the Lai content law (content note, Lemmas S and T)

For `√(8n) < p < 3n` (`8n < p²`, `p < 3n`) write `6n = q₆ p + r₆`, `2n = q₂ p + r₂`.  Residue `s < p`
has class constant `σ(s) ∈ {0, 2, 3, 5}` (classes A, C, B, D) and `L_s ∈ {q₆, q₆ - 1}` nodes;
its `j`-th index costs `inc s j = 2j - 6 + σ(s) + 3[j > 2 L_s]`.  `lam` is the largest of the `3n`
smallest increments, `mu s` the number of indices of `s` below it, `d = 3n - ∑ mu`.

* `lemmaS`: (i) `0 ≤ λ`; (ii) `2 μ_s + σ(s) = λ + 4 + [s ∈ N]`; (iii) a tie residue has
  `μ_s + 1 ≤ 2 L_s` (so no index `j > 2L` is used).
* `lemmaT`: `2d + |N| + 2 = p (2 q₆ - 3 q₂ - 2 - λ)`.

Everything is natural-number / integer arithmetic; the counts are exact (no truncation: `j ≤ 3n`
loses nothing because no residue uses more than `2 L_s ≤ 3n` indices below the cut).
-/

open Finset

namespace CatalanCore.Content

section Greedy

variable (n p : ℕ)

def r6 : ℕ := 6 * n % p
def q6 : ℕ := 6 * n / p
def r2 : ℕ := 2 * n % p
def q2 : ℕ := 2 * n / p

/-- class constant `σ(s)`: A `0`, C `2`, B `3`, D `5`. -/
def sig (s : ℕ) : ℕ := (if s ≤ r6 n p then 0 else 2) + (if p - r2 n p ≤ s then 3 else 0)

/-- number of nodes `L_s` of the residue `s`. -/
def Lc (s : ℕ) : ℕ := if s ≤ r6 n p then q6 n p else q6 n p - 1

/-- the increment of the `j`-th index of the residue `s`. -/
def inc (s j : ℕ) : ℤ := 2 * (j : ℤ) - 6 + (sig n p s : ℤ) + (if 2 * Lc n p s < j then 3 else 0)

/-- number of indices `j ≤ 3n` of `s` with increment `≤ t`. -/
def cntRes (s : ℕ) (t : ℤ) : ℕ := ((Icc 1 (3 * n)).filter (fun j => inc n p s j ≤ t)).card

def cnt (t : ℤ) : ℕ := ∑ s ∈ range p, cntRes n p s t

lemma cnt_mono {t t' : ℤ} (h : t ≤ t') : cnt n p t ≤ cnt n p t' := by
  unfold cnt cntRes
  refine Finset.sum_le_sum (fun s _ => Finset.card_le_card ?_)
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

lemma cnt_exists (hp : 1 ≤ p) : ∃ k : ℕ, 3 * n ≤ cnt n p ((k : ℤ) - 4) := by
  refine ⟨6 * n + 20, ?_⟩
  have hsig : ∀ s, sig n p s ≤ 5 := by intro s; unfold sig; split_ifs <;> omega
  have : ∀ s ∈ range p, cntRes n p s (((6 * n + 20 : ℕ) : ℤ) - 4) = 3 * n := by
    intro s _
    unfold cntRes
    have : (Icc 1 (3 * n)).filter (fun j => inc n p s j ≤ (((6 * n + 20 : ℕ) : ℤ) - 4)) = Icc 1 (3 * n) := by
      apply Finset.filter_true_of_mem
      intro j hj
      have hj' := Finset.mem_Icc.1 hj
      have := hsig s
      unfold inc
      split_ifs <;> push_cast <;> omega
    rw [this]; simp
  unfold cnt
  rw [Finset.sum_congr rfl this]
  simp
  nlinarith

/-- the least `t ≥ -4` with `cnt t ≥ 3n`. -/
noncomputable def lam : ℤ :=
  open Classical in
  if h : ∃ k : ℕ, 3 * n ≤ cnt n p ((k : ℤ) - 4) then (Nat.find h : ℤ) - 4 else 0

lemma lam_spec (hp : 1 ≤ p) (hn : 1 ≤ n) : 3 * n ≤ cnt n p (lam n p) ∧ ∀ t < lam n p, cnt n p t < 3 * n := by
  classical
  have h := cnt_exists n p hp
  have hl : lam n p = (Nat.find h : ℤ) - 4 := by unfold lam; simp [h]
  constructor
  · rw [hl]; exact Nat.find_spec h
  · intro t ht
    by_contra hcon
    push_neg at hcon
    rw [hl] at ht
    by_cases ht4 : t < -4
    · have : cnt n p t = 0 := by
        unfold cnt cntRes
        refine Finset.sum_eq_zero (fun s _ => ?_)
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j hj
        have hsig : sig n p s ≥ 0 := Nat.zero_le _
        have hj' := (Finset.mem_Icc.1 hj).1
        unfold inc; split_ifs <;> push_cast <;> omega
      omega
    · have hk : 0 ≤ t + 4 := by omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hk
      have hkt : t = (k : ℤ) - 4 := by omega
      have := Nat.find_min' h (m := k) (by rw [← hkt]; exact hcon)
      omega

/-- the number of indices of `s` strictly below the cut. -/
noncomputable def mu (s : ℕ) : ℕ := cntRes n p s (lam n p - 1)

end Greedy

section Arith

variable {n p : ℕ}

/-- standing hypotheses: `√(8n) < p < 3n`. -/
structure Rng (n p : ℕ) : Prop where
  h8 : 8 * n < p ^ 2
  h3 : p < 3 * n

lemma Rng.p5 (h : Rng n p) : 5 ≤ p := by
  by_contra hc
  push_neg at hc
  have h8 := h.h8; have h3 := h.h3
  rw [pow_two] at h8
  have hp2 : p * p ≤ 4 * p := Nat.mul_le_mul_right p (by omega)
  omega

lemma Rng.n2 (h : Rng n p) : 2 ≤ n := by
  have := h.p5; have := h.h3; omega

lemma qr6 (n p : ℕ) (hp : 0 < p) : 6 * n = q6 n p * p + r6 n p := by
  unfold q6 r6; exact (Nat.div_add_mod' (6 * n) p).symm

lemma qr2 (n p : ℕ) (hp : 0 < p) : 2 * n = q2 n p * p + r2 n p := by
  unfold q2 r2; exact (Nat.div_add_mod' (2 * n) p).symm

lemma r6_lt (n p : ℕ) (hp : 0 < p) : r6 n p < p := Nat.mod_lt _ hp
lemma r2_lt (n p : ℕ) (hp : 0 < p) : r2 n p < p := Nat.mod_lt _ hp

lemma Rng.q6_ge (h : Rng n p) : 2 ≤ q6 n p := by
  unfold q6
  rw [Nat.le_div_iff_mul_le (by have := h.p5; omega)]
  have := h.h3; omega

/-- `2p + r₆ + r₂ ≤ 8n` and `r₆ + 1 + p < 3n + r₂`. -/
lemma Rng.arith (h : Rng n p) : 2 * p + r6 n p + r2 n p ≤ 8 * n ∧ r6 n p + 1 + p < 3 * n + r2 n p := by
  have hp := h.p5; have h3 := h.h3; have hn := h.n2
  have a6 := qr6 n p (by omega); have a2 := qr2 n p (by omega)
  have b6 := r6_lt n p (by omega); have b2 := r2_lt n p (by omega)
  by_cases hA : p ≤ 2 * n
  · constructor
    · omega
    · by_cases h0 : r2 n p = 0
      · have : r6 n p = 0 := by
          unfold r6; rw [show 6 * n = 3 * (2 * n) by ring, Nat.mul_mod]
          have : 2 * n % p = 0 := h0
          rw [this]; simp
        omega
      · by_cases hB : 2 * p ≤ 3 * n
        · omega
        · -- 3n/2 < p ≤ 2n: q₆ = 3, r₂ = 2n - p
          have hq : q6 n p = 3 := by
            unfold q6
            apply Nat.div_eq_of_lt_le <;> nlinarith
          have hq2 : q2 n p = 1 := by
            unfold q2
            apply Nat.div_eq_of_lt_le <;> nlinarith
          rw [hq] at a6; rw [hq2] at a2
          omega
  · push_neg at hA
    have hq : q6 n p = 2 := by
      have := Rng.q6_ge h
      have hle : q6 n p < 3 := by
        by_contra hc; push_neg at hc; nlinarith
      omega
    have hq2 : q2 n p = 0 := by
      by_contra hc
      have : 1 ≤ q2 n p := Nat.pos_of_ne_zero hc
      nlinarith
    rw [hq] at a6; rw [hq2] at a2
    omega

lemma sig_le (n p s : ℕ) : sig n p s ≤ 5 := by unfold sig; split_ifs <;> omega

/-- per-residue count, valid for `-1 ≤ t ≤ 4 q₆ - 7`. -/
lemma cntRes_formula (h : Rng n p) {s : ℕ} (t : ℤ) (ht1 : -1 ≤ t) (ht2 : t ≤ 4 * (q6 n p : ℤ) - 7) :
    cntRes n p s t = ((t + 6 - (sig n p s : ℤ)) / 2).toNat := by
  have hq := h.q6_ge
  have hp := h.p5
  have a6 := qr6 n p (by omega)
  have h5q : 5 * q6 n p ≤ 6 * n := by
    have := Nat.mul_le_mul_left (q6 n p) hp
    omega
  have hL : 2 * Lc n p s ≤ 3 * n := by
    unfold Lc; split_ifs <;> omega
  have hTL : t ≤ 4 * (Lc n p s : ℤ) - 5 + (sig n p s : ℤ) := by
    unfold Lc sig; split_ifs <;> push_cast <;> omega
  have hs5 := sig_le n p s
  unfold cntRes
  have : (Icc 1 (3 * n)).filter (fun j => inc n p s j ≤ t) = Icc 1 ((t + 6 - (sig n p s : ℤ)) / 2).toNat := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    unfold inc
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      split_ifs at h3 with hc
      · omega
      · omega
    · rintro ⟨h1, h2⟩
      have hLj : j ≤ 2 * Lc n p s := by omega
      refine ⟨⟨h1, by omega⟩, ?_⟩
      have : ¬ (2 * Lc n p s < j) := by omega
      rw [if_neg this]; omega
  rw [this]; simp

end Arith

section Sums

variable {n p : ℕ}

lemma sum_thresh (b x y : ℕ) (hb : b ≤ p) :
    ∑ s ∈ range p, (if b ≤ s then x else y) = (p - b) * x + b * y := by
  have h1 : (range p).filter (fun s => b ≤ s) = Ico b p := by
    ext s; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have h2 : (range p).filter (fun s => ¬ b ≤ s) = range b := by
    ext s; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_ite, h1, h2]; simp

lemma sum_le_one (a : ℕ) (ha : a < p) : ∑ s ∈ range p, (if s ≤ a then 1 else 0) = a + 1 := by
  rw [Finset.sum_boole]
  have : (range p).filter (fun s => s ≤ a) = range (a + 1) := by
    ext s; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this]; simp

/-- closed form of the count, for `-1 ≤ t ≤ 4 q₆ - 7`. -/
lemma cnt_formula (h : Rng n p) (t : ℤ) (ht1 : -1 ≤ t) (ht2 : t ≤ 4 * (q6 n p : ℤ) - 7) :
    cnt n p t = (r6 n p + 1) + (p - r2 n p) * ((t + 4) / 2).toNat + r2 n p * ((t + 1) / 2).toNat := by
  have hp := h.p5
  have hr6 := r6_lt n p (by omega)
  have hr2 := r2_lt n p (by omega)
  unfold cnt
  have e1 : ∀ s ∈ range p, cntRes n p s t = (if s ≤ r6 n p then 1 else 0) +
      (if p - r2 n p ≤ s then ((t + 1) / 2).toNat else ((t + 4) / 2).toNat) := by
    intro s _
    rw [cntRes_formula h t ht1 ht2]
    unfold sig
    split_ifs <;> omega
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, sum_le_one _ hr6,
    sum_thresh _ _ _ (by omega)]
  have : p - (p - r2 n p) = r2 n p := by omega
  rw [this]; ring

end Sums

lemma aux_mul (p r A : ℕ) (h : r ≤ p) :
    (p - r) * (2 * A + 2) + r * (2 * A + 1) + r = p * (2 * A + 2) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]; ring

section MainS

variable {n p : ℕ}

lemma lam_ge_zero (h : Rng n p) : 0 ≤ lam n p := by
  have hp := h.p5; have hn := h.n2
  obtain ⟨hs1, hs2⟩ := lam_spec n p (by omega) (by omega)
  by_contra hc
  push_neg at hc
  have hm := cnt_mono n p (show lam n p ≤ -1 by omega)
  have hf := cnt_formula h (-1) le_rfl (by have := h.q6_ge; omega)
  have ha := (Rng.arith h).2
  have : ((-1 : ℤ) + 4) / 2 = 1 := by norm_num
  have h0 : ((-1 : ℤ) + 1) / 2 = 0 := by norm_num
  rw [this, h0] at hf
  simp at hf
  have := r2_lt n p (by omega)
  omega

lemma lam_le_top (h : Rng n p) : lam n p ≤ 4 * (q6 n p : ℤ) - 7 := by
  have hp := h.p5; have hn := h.n2
  obtain ⟨hs1, hs2⟩ := lam_spec n p (by omega) (by omega)
  by_contra hc
  push_neg at hc
  have hlt := hs2 (4 * (q6 n p : ℤ) - 7) hc
  have hq := h.q6_ge
  rw [cnt_formula h _ (by omega) le_rfl] at hlt
  have a6 := qr6 n p (by omega)
  have ha := (Rng.arith h).1
  have hr2 := r2_lt n p (by omega)
  have e1 : ((4 * (q6 n p : ℤ) - 7 + 4) / 2).toNat = 2 * q6 n p - 2 := by omega
  have e2 : ((4 * (q6 n p : ℤ) - 7 + 1) / 2).toNat = 2 * q6 n p - 3 := by omega
  rw [e1, e2] at hlt
  obtain ⟨A, hA⟩ : ∃ A, q6 n p = A + 2 := ⟨q6 n p - 2, by omega⟩
  rw [hA] at hlt a6
  have e3 : 2 * (A + 2) - 2 = 2 * A + 2 := by omega
  have e4 : 2 * (A + 2) - 3 = 2 * A + 1 := by omega
  rw [e3, e4] at hlt
  have : (p - r2 n p) * (2 * A + 2) + r2 n p * (2 * A + 1) + r2 n p = p * (2 * A + 2) :=
    aux_mul p (r2 n p) A hr2.le
  nlinarith

lemma mu_formula (h : Rng n p) {s : ℕ} (hs : s < p) :
    mu n p s = ((lam n p + 5 - (sig n p s : ℤ)) / 2).toNat := by
  unfold mu
  have h0 := lam_ge_zero h
  have h1 := lam_le_top h
  rw [cntRes_formula h _ (by omega) (by omega)]
  congr 2; ring

theorem lemmaS (h : Rng n p) :
    0 ≤ lam n p ∧ lam n p ≤ 4 * (q6 n p : ℤ) - 7 ∧
    (∀ s < p, 2 * (mu n p s : ℤ) + (sig n p s : ℤ) =
      lam n p + 4 + (if (lam n p - (sig n p s : ℤ)) % 2 = 0 then 0 else 1)) ∧
    (∀ s < p, (lam n p - (sig n p s : ℤ)) % 2 = 0 → mu n p s + 1 ≤ 2 * Lc n p s) := by
  have h0 := lam_ge_zero h
  have h1 := lam_le_top h
  have hq := h.q6_ge
  refine ⟨h0, h1, ?_, ?_⟩
  · intro s hs
    rw [mu_formula h hs]
    have := sig_le n p s
    split_ifs <;> omega
  · intro s hs hpar
    rw [mu_formula h hs]
    have := sig_le n p s
    unfold Lc sig at *
    split_ifs at * <;> omega

end MainS

section MainT

variable {n p : ℕ}

/-- the number `d` of increments equal to `λ` among the `3n` smallest. -/
noncomputable def dcnt (n p : ℕ) : ℕ := 3 * n - ∑ s ∈ range p, mu n p s

/-- the number of residues of the class union `N` (parity of `σ` different from that of `λ`). -/
noncomputable def Ncnt (n p : ℕ) : ℕ :=
  ((range p).filter (fun s => (lam n p - (sig n p s : ℤ)) % 2 ≠ 0)).card

/-- **Lemma T.**  `2d + |N| + 2 = p (2 q₆ - 3 q₂ - 2 - λ)`. -/
theorem lemmaT (h : Rng n p) :
    2 * (dcnt n p : ℤ) + (Ncnt n p : ℤ) + 2 = (p : ℤ) * (2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) := by
  have hp := h.p5; have hn := h.n2
  have h0 := lam_ge_zero h
  have h1 := lam_le_top h
  obtain ⟨hs1, hs2⟩ := lam_spec n p (by omega) (by omega)
  have hlt := hs2 (lam n p - 1) (by omega)
  have hsum : ∑ s ∈ range p, mu n p s = cnt n p (lam n p - 1) := rfl
  have hf := cnt_formula h (lam n p - 1) (by omega) (by omega)
  have hr2 := r2_lt n p (by omega)
  have a6 := qr6 n p (by omega); have a2 := qr2 n p (by omega)
  have hN : Ncnt n p = (p - (p - r2 n p)) * (if (lam n p - 1) % 2 ≠ 0 then 1 else 0) +
      (p - r2 n p) * (if lam n p % 2 ≠ 0 then 1 else 0) := by
    unfold Ncnt
    rw [Finset.card_filter]
    have e : ∀ s ∈ range p, (if (lam n p - (sig n p s : ℤ)) % 2 ≠ 0 then 1 else 0) =
        (if p - r2 n p ≤ s then (if (lam n p - 1) % 2 ≠ 0 then 1 else 0)
          else (if lam n p % 2 ≠ 0 then 1 else 0)) := by
      intro s _
      unfold sig
      split_ifs <;> omega
    rw [Finset.sum_congr rfl e, sum_thresh _ _ _ (by omega)]
  have hdz : (dcnt n p : ℤ) = 3 * n - cnt n p (lam n p - 1) := by
    unfold dcnt; rw [hsum]; push_cast [Nat.cast_sub hlt.le]; ring
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h0
  have hf' : (cnt n p (lam n p - 1) : ℤ) = (r6 n p + 1 : ℤ) + ((p : ℤ) - r2 n p) * (((lam n p + 3) / 2).toNat : ℤ) +
      (r2 n p : ℤ) * ((lam n p / 2).toNat : ℤ) := by
    rw [hf]; push_cast [Nat.cast_sub hr2.le]
    have e1 : lam n p - 1 + 4 = lam n p + 3 := by ring
    have e2 : lam n p - 1 + 1 = lam n p := by ring
    rw [e1, e2]
  rw [hdz, hf']
  have hNz : (Ncnt n p : ℤ) = (r2 n p : ℤ) * (if (lam n p - 1) % 2 ≠ 0 then 1 else 0) +
      ((p : ℤ) - r2 n p) * (if lam n p % 2 ≠ 0 then 1 else 0) := by
    rw [hN]; push_cast [Nat.cast_sub hr2.le, Nat.cast_sub (show p - r2 n p ≤ p by omega)]
    have : (p : ℤ) - ((p : ℤ) - r2 n p) = r2 n p := by ring
    split_ifs <;> simp [this]
  rw [hNz]
  have a6' : (6 * n : ℤ) = (q6 n p : ℤ) * p + r6 n p := by exact_mod_cast a6
  have a2' : (2 * n : ℤ) = (q2 n p : ℤ) * p + r2 n p := by exact_mod_cast a2
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  case inl =>
    have hl : lam n p = 2 * (k : ℤ) := by rw [hm, hk]; push_cast; ring
    have e1 : ((lam n p + 3) / 2).toNat = k + 1 := by omega
    have e2 : (lam n p / 2).toNat = k := by omega
    rw [e1, e2]
    have c1 : ¬ ((lam n p - 1) % 2 = 0) := by omega
    have c2 : (lam n p % 2 = 0) := by omega
    simp only [ne_eq, c1, c2, not_false_eq_true, if_true, not_true_eq_false, if_false]
    rw [hl]
    push_cast
    linear_combination (2 * a6' - 3 * a2')
  case inr =>
    have hl : lam n p = 2 * (k : ℤ) + 1 := by rw [hm, hk]; push_cast; ring
    have e1 : ((lam n p + 3) / 2).toNat = k + 2 := by omega
    have e2 : (lam n p / 2).toNat = k := by omega
    rw [e1, e2]
    have c1 : ((lam n p - 1) % 2 = 0) := by omega
    have c2 : ¬ (lam n p % 2 = 0) := by omega
    simp only [ne_eq, c1, c2, not_false_eq_true, if_true, not_true_eq_false, if_false]
    rw [hl]
    push_cast
    linear_combination (2 * a6' - 3 * a2')

end MainT

section TailT

/-- If `r₂ = 0` then `r₆ = 0` (`6n = 3 · 2n`). -/
lemma r6_eq_zero_of_r2 {n p : ℕ} (h0 : r2 n p = 0) : r6 n p = 0 := by
  unfold r6
  rw [show 6 * n = 3 * (2 * n) by ring, Nat.mul_mod]
  have : 2 * n % p = 0 := h0
  rw [this]; simp

/-- Residues `0` and `p - 1` lie in different classes: not all residues form a single class. -/
lemma sig_zero_ne_sig_last {n p : ℕ} (h : Rng n p) : sig n p 0 ≠ sig n p (p - 1) := by
  have hp := h.p5
  have hr2 := r2_lt n p (by omega)
  unfold sig
  by_cases h0 : r2 n p = 0
  · have := r6_eq_zero_of_r2 h0
    split_ifs <;> omega
  · split_ifs <;> omega

/-- **Lemma T, second part (arithmetic core).**  With `p = |Z| + |W| + |N|` and
`2d + |N| + 2 = p k`: if the second level is active (`|Z| + |N| < d` and `d + |N| < |W|`, i.e.
`x₂ > 0`) and the residues do not form a single class (`|Z| + |N| ≥ 1`), then `k = 1`, hence
`2d + 2 = |Z| + |W|`. -/
theorem lemmaT_tail (p d Z W Nn : ℕ) (k : ℤ) (hp : p = Z + W + Nn)
    (hT : 2 * (d : ℤ) + Nn + 2 = p * k) (hx : Z + Nn < d) (hd : d + Nn < W) (hne : 0 < Z + Nn) :
    k = 1 ∧ 2 * d + 2 = Z + W := by
  have hpz : (p : ℤ) = Z + W + Nn := by exact_mod_cast hp
  have hk1 : 1 ≤ k := by
    by_contra hc
    push_neg at hc
    have hk0 : k ≤ 0 := by omega
    have : (p : ℤ) * k ≤ 0 := by nlinarith [(Nat.cast_nonneg p : (0:ℤ) ≤ p)]
    omega
  have hk : k = 1 := by
    by_contra hc
    have hk2 : 2 ≤ k := by omega
    have : (p : ℤ) * 2 ≤ p * k := by nlinarith [(Nat.cast_nonneg p : (0:ℤ) ≤ p)]
    omega
  subst hk
  refine ⟨rfl, ?_⟩
  omega

end TailT

end CatalanCore.Content
end PartGreedy

section Axioms
end Axioms

#print axioms CatalanCore.Content.faulhaber_bridge
#print axioms CatalanCore.Content.fact_digits_mod
#print axioms CatalanCore.Content.choose_reflect_mod
#print axioms CatalanCore.Content.choose_unit_part
#print axioms CatalanCore.Content.hankel_generic_ne_zero
#print axioms CatalanCore.Content.lemmaS
#print axioms CatalanCore.Content.lemmaT
#print axioms CatalanCore.Content.lemmaT_tail
