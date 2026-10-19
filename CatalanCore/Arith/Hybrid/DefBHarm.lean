module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# Harmonic sums in `𝔽_p` and the reflection `H_{p-1-n} = H_n`

Finite-field facts behind the Schur identity of Theorem B (and DQ Lemma 3.1):
`hm p n = ∑_{s=1}^n 1/s`, `hm2 p n = ∑_{s=1}^n 1/s²` in `ZMod p`, with
* `hm_top : hm p (p-1) = 0` (`p ≥ 3`), `hm2_top : hm2 p (p-1) = 0` (`p ≥ 5`),
* `hm_refl : hm p (p-1-n) = hm p n`, `hm2_refl : hm2 p (p-1-n) = - hm2 p n` (`n ≤ p-1`).
-/

open Finset

namespace CatalanCore.Arith.Hybrid

variable (p : ℕ) [Fact p.Prime]

/-- `H_n = ∑_{s=1}^n 1/s` in `𝔽_p`. -/
def hm (n : ℕ) : ZMod p := ∑ s ∈ Icc 1 n, ((s : ℕ) : ZMod p)⁻¹

/-- `H^{(2)}_n = ∑_{s=1}^n 1/s²` in `𝔽_p`. -/
def hm2 (n : ℕ) : ZMod p := ∑ s ∈ Icc 1 n, (((s : ℕ) : ZMod p)⁻¹) ^ 2

variable {p}

lemma hm_succ (n : ℕ) : hm p (n + 1) = hm p n + (((n + 1 : ℕ) : ZMod p))⁻¹ := by
  unfold hm; rw [Finset.sum_Icc_succ_top (by omega)]

lemma hm2_succ (n : ℕ) : hm2 p (n + 1) = hm2 p n + ((((n + 1 : ℕ) : ZMod p))⁻¹) ^ 2 := by
  unfold hm2; rw [Finset.sum_Icc_succ_top (by omega)]

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ s ∈ Icc 1 n, f s = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- A sum over `ZMod p` of a function vanishing at `0` is the sum over `1 ≤ s ≤ p - 1`. -/
lemma sum_zmod_eq (g : ZMod p → ZMod p) (h0 : g 0 = 0) :
    ∑ x : ZMod p, g x = ∑ s ∈ Icc 1 (p - 1), g (s : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hinj : Set.InjOn (fun s : ℕ => (s : ZMod p)) (range p) := fun a ha b hb h =>
    CharP.natCast_injOn_Iio (ZMod p) p (by simpa using ha) (by simpa using hb) h
  have himg : (Finset.range p).image (fun s : ℕ => (s : ZMod p)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
  rw [← himg, Finset.sum_image hinj, sum_Icc_eq_range]
  have : range p = range ((p - 1) + 1) := by congr 1; omega
  rw [this, Finset.sum_range_succ']
  simp [h0]

lemma hm_top (hp3 : 3 ≤ p) : hm p (p - 1) = 0 := by
  unfold hm
  rw [← sum_zmod_eq (fun x : ZMod p => x⁻¹) (by simp)]
  have h1 : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x := 
    Fintype.sum_equiv (Function.Involutive.toPerm (fun x : ZMod p => x⁻¹) inv_involutive) _ _ (fun x => rfl)
  rw [h1]
  have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) (i := 1) (by rw [ZMod.card]; omega)
  simpa using this

lemma hm2_top (hp5 : 5 ≤ p) : hm2 p (p - 1) = 0 := by
  unfold hm2
  rw [← sum_zmod_eq (fun x : ZMod p => (x⁻¹) ^ 2) (by simp)]
  have h1 : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Fintype.sum_equiv (Function.Involutive.toPerm (fun x : ZMod p => x⁻¹) inv_involutive) _ _ (fun x => rfl)
  rw [h1]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (i := 2) (by rw [ZMod.card]; omega)

lemma cast_refl {n : ℕ} (hn : n ≤ p - 1) :
    (((p - 1 - n : ℕ)) : ZMod p) = -((n : ZMod p) + 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h : ((p - 1 - n : ℕ) : ZMod p) + ((n : ZMod p) + 1) = 0 := by
    have : ((p - 1 - n + (n + 1) : ℕ) : ZMod p) = 0 := by
      have : p - 1 - n + (n + 1) = p := by omega
      rw [this]; exact ZMod.natCast_self p
    push_cast at this
    exact this
  exact eq_neg_of_add_eq_zero_left h

/-- Reflection `H_{p-1-n} = H_n`. -/
lemma hm_refl (hp3 : 3 ≤ p) : ∀ n, n ≤ p - 1 → hm p (p - 1 - n) = hm p n := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : hm p 0 = 0 := by simp [hm]
    simpa [h0] using hm_top hp3
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hm_succ (p := p) (p - 1 - (n + 1))
    have e : p - 1 - (n + 1) + 1 = p - 1 - n := by omega
    rw [e] at h2
    rw [hm_succ n]
    rw [cast_refl (by omega)] at h2
    rw [h1] at h2
    have : hm p (p - 1 - (n + 1)) = hm p n + ((n + 1 : ℕ) : ZMod p)⁻¹ := by
      rw [h2]
      push_cast
      rw [inv_neg]; ring
    exact this

/-- Reflection `H^{(2)}_{p-1-n} = -H^{(2)}_n`. -/
lemma hm2_refl (hp5 : 5 ≤ p) : ∀ n, n ≤ p - 1 → hm2 p (p - 1 - n) = - hm2 p n := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : hm2 p 0 = 0 := by simp [hm2]
    simpa [h0] using hm2_top hp5
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hm2_succ (p := p) (p - 1 - (n + 1))
    have e : p - 1 - (n + 1) + 1 = p - 1 - n := by omega
    rw [e] at h2
    rw [hm2_succ n]
    rw [cast_refl (by omega)] at h2
    rw [h1] at h2
    have : hm2 p (p - 1 - (n + 1)) = -(hm2 p n + (((n + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
      have h3 : hm2 p (p - 1 - (n + 1)) = -hm2 p n - (-((n : ZMod p) + 1))⁻¹ ^ 2 := by
        rw [eq_sub_iff_add_eq]; exact h2.symm
      rw [h3]
      push_cast
      rw [inv_neg]; ring
    exact this

end CatalanCore.Arith.Hybrid
