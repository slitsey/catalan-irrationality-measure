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

/-! ### Shifted harmonic sums -/

lemma cast_nz {x : ℕ} (h0 : 0 < x) (hx : x < p) : ((x : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

lemma hm_diff (n : ℕ) : hm p (n + 1) - hm p n = (((n + 1 : ℕ) : ZMod p))⁻¹ := by
  rw [hm_succ]; ring

lemma hm2_diff (n : ℕ) : hm2 p (n + 1) - hm2 p n = ((((n + 1 : ℕ) : ZMod p))⁻¹) ^ 2 := by
  rw [hm2_succ]; ring

/-- `∑_{c=a}^{b-1} 1/(c-u) = H_{b-1-u} - H_{a-1-u}` for `u < a ≤ b`. -/
lemma sum_Ico_shift {u a : ℕ} (hu : u < a) :
    ∀ b, a ≤ b → ∑ c ∈ Ico a b, (((c : ℕ) : ZMod p) - (u : ZMod p))⁻¹ =
      hm p (b - 1 - u) - hm p (a - 1 - u) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    have e : b + 1 - 1 - u = (b - 1 - u) + 1 := by omega
    rw [e, hm_succ]
    have : ((b - 1 - u + 1 : ℕ) : ZMod p) = (b : ZMod p) - u := by
      have : b - 1 - u + 1 = b - u := by omega
      rw [this, Nat.cast_sub (by omega)]
    rw [this]; ring

lemma sum_Ico_shift2 {u a : ℕ} (hu : u < a) :
    ∀ b, a ≤ b → ∑ c ∈ Ico a b, ((((c : ℕ) : ZMod p) - (u : ZMod p))⁻¹) ^ 2 =
      hm2 p (b - 1 - u) - hm2 p (a - 1 - u) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    have e : b + 1 - 1 - u = (b - 1 - u) + 1 := by omega
    rw [e, hm2_succ]
    have : ((b - 1 - u + 1 : ℕ) : ZMod p) = (b : ZMod p) - u := by
      have : b - 1 - u + 1 = b - u := by omega
      rw [this, Nat.cast_sub (by omega)]
    rw [this]; ring

/-- `∑_{t=u+1}^{w} 1/(k-t) = H_{k-1-u} - H_{k-1-w}` for `u ≤ w < k`. -/
lemma sum_Ioc_rev {u k : ℕ} :
    ∀ w, u ≤ w → w < k → ∑ t ∈ Ioc u w, ((k : ZMod p) - (t : ℕ))⁻¹ =
      hm p (k - 1 - u) - hm p (k - 1 - w) := by
  intro w huw
  induction w, huw using Nat.le_induction with
  | base => intro _; simp
  | succ w huw ih =>
    intro hwk
    rw [Finset.sum_Ioc_succ_top huw, ih (by omega)]
    have e : k - 1 - w = (k - 1 - (w + 1)) + 1 := by omega
    rw [e, hm_succ]
    have : ((k - 1 - (w + 1) + 1 : ℕ) : ZMod p) = (k : ZMod p) - ((w + 1 : ℕ) : ZMod p) := by
      have : k - 1 - (w + 1) + 1 = k - (w + 1) := by omega
      rw [this, Nat.cast_sub (by omega)]
    rw [this]; ring

lemma sum_Ioc_rev2 {u k : ℕ} :
    ∀ w, u ≤ w → w < k → ∑ t ∈ Ioc u w, (((k : ZMod p) - (t : ℕ))⁻¹) ^ 2 =
      hm2 p (k - 1 - u) - hm2 p (k - 1 - w) := by
  intro w huw
  induction w, huw using Nat.le_induction with
  | base => intro _; simp
  | succ w huw ih =>
    intro hwk
    rw [Finset.sum_Ioc_succ_top huw, ih (by omega)]
    have e : k - 1 - w = (k - 1 - (w + 1)) + 1 := by omega
    rw [e, hm2_succ]
    have : ((k - 1 - (w + 1) + 1 : ℕ) : ZMod p) = (k : ZMod p) - ((w + 1 : ℕ) : ZMod p) := by
      have : k - 1 - (w + 1) + 1 = k - (w + 1) := by omega
      rw [this, Nat.cast_sub (by omega)]
    rw [this]; ring

/-- `∑_{t=u+1}^{w} 1/t = H_w - H_u`. -/
lemma sum_Ioc_hm {u : ℕ} : ∀ w, u ≤ w → ∑ t ∈ Ioc u w, ((t : ℕ) : ZMod p)⁻¹ = hm p w - hm p u := by
  intro w huw
  induction w, huw using Nat.le_induction with
  | base => simp
  | succ w huw ih => rw [Finset.sum_Ioc_succ_top huw, ih, hm_succ]; ring

lemma sum_Ioc_hm2 {u : ℕ} : ∀ w, u ≤ w →
    ∑ t ∈ Ioc u w, (((t : ℕ) : ZMod p)⁻¹) ^ 2 = hm2 p w - hm2 p u := by
  intro w huw
  induction w, huw using Nat.le_induction with
  | base => simp
  | succ w huw ih => rw [Finset.sum_Ioc_succ_top huw, ih, hm2_succ]; ring

/-- `∑_{i=1}^{d} 1/(u+i) = H_{u+d} - H_u`. -/
lemma sum_Icc_shift (u : ℕ) : ∀ d, ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ = hm p (u + d) - hm p u := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, ← add_assoc, hm_succ]
    push_cast; ring

lemma sum_Icc_shift2 (u : ℕ) : ∀ d, ∑ i ∈ Icc 1 d, (((u : ZMod p) + (i : ℕ))⁻¹) ^ 2 =
    hm2 p (u + d) - hm2 p u := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, ← add_assoc, hm2_succ]
    push_cast; ring

/-! ### The Schur identity of Theorem B -/

/-- **Off-diagonal Schur identity** (`16 S̄_{uw} = ∑_i E_{ui} E_{wi}`), `p = r + d`, `u < w < k ≤ r`. -/
theorem harm_off (hp3 : 3 ≤ p) {k r d u w : ℕ} (hrd : r + d = p) (hkr : k ≤ r) (huw : u < w)
    (hwk : w < k) :
    (16 * ((w : ZMod p) - u))⁻¹ *
        ∑ t ∈ Ioc u w, (((t : ℕ) : ZMod p)⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹)
      - (1 / 16) * ∑ c ∈ Ico k r, (((c : ℕ) : ZMod p) - u)⁻¹ * (((c : ℕ) : ZMod p) - w)⁻¹
      = (1 / 16) * ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ * ((w : ZMod p) + (i : ℕ))⁻¹ := by
  have hdiff : ((w : ZMod p) - u) = ((w - u : ℕ) : ZMod p) := by rw [Nat.cast_sub huw.le]
  have hwu : ((w : ZMod p) - u) ≠ 0 := by
    rw [hdiff]; exact cast_nz (by omega) (by omega)
  have hA : ∑ t ∈ Ioc u w, (((t : ℕ) : ZMod p)⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹) =
      (hm p w - hm p u) + (hm p (k - 1 - u) - hm p (k - 1 - w)) := by
    rw [← sum_Ioc_hm w huw.le, ← sum_Ioc_rev w huw.le hwk, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have : ((t : ZMod p) - (k : ZMod p))⁻¹ = -((k : ZMod p) - (t : ℕ))⁻¹ := by
      rw [← inv_neg]; congr 1; ring
    rw [this]; ring
  have hB : ∑ c ∈ Ico k r, (((c : ℕ) : ZMod p) - u)⁻¹ * (((c : ℕ) : ZMod p) - w)⁻¹ =
      (-((w : ZMod p) - u))⁻¹ * ((hm p (r - 1 - u) - hm p (k - 1 - u)) -
        (hm p (r - 1 - w) - hm p (k - 1 - w))) := by
    rw [← sum_Ico_shift (p := p) (u := u) (a := k) (by omega) r hkr,
      ← sum_Ico_shift (p := p) (u := w) (a := k) (by omega) r hkr, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    have h1 : (((c : ℕ) : ZMod p) - u) = ((c - u : ℕ) : ZMod p) := by rw [Nat.cast_sub (by omega)]
    have h2 : (((c : ℕ) : ZMod p) - w) = ((c - w : ℕ) : ZMod p) := by rw [Nat.cast_sub (by omega)]
    have n1 : (((c : ℕ) : ZMod p) - u) ≠ 0 := by rw [h1]; exact cast_nz (by omega) (by omega)
    have n2 : (((c : ℕ) : ZMod p) - w) ≠ 0 := by rw [h2]; exact cast_nz (by omega) (by omega)
    have n3 : (-((w : ZMod p) - u)) ≠ 0 := neg_ne_zero.2 hwu
    field_simp
    ring
  have hC : ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ * ((w : ZMod p) + (i : ℕ))⁻¹ =
      ((w : ZMod p) - u)⁻¹ * ((hm p (u + d) - hm p u) - (hm p (w + d) - hm p w)) := by
    rw [← sum_Icc_shift u d, ← sum_Icc_shift w d, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    have n1 : ((u : ZMod p) + (i : ℕ)) ≠ 0 := by
      have : ((u : ZMod p) + (i : ℕ)) = ((u + i : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]; exact cast_nz (by omega) (by omega)
    have n2 : ((w : ZMod p) + (i : ℕ)) ≠ 0 := by
      have : ((w : ZMod p) + (i : ℕ)) = ((w + i : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]; exact cast_nz (by omega) (by omega)
    field_simp
    ring
  have r1 : hm p (r - 1 - u) = hm p (u + d) := by
    have := hm_refl hp3 (u + d) (by omega)
    rw [show r - 1 - u = p - 1 - (u + d) by omega]; exact this
  have r2 : hm p (r - 1 - w) = hm p (w + d) := by
    have := hm_refl hp3 (w + d) (by omega)
    rw [show r - 1 - w = p - 1 - (w + d) by omega]; exact this
  rw [hA, hB, hC, r1, r2, mul_inv]
  have e : (-((w : ZMod p) - u))⁻¹ = -((w : ZMod p) - u)⁻¹ := inv_neg
  rw [e]
  ring

/-- **Diagonal Schur identity** (`16 S̄_{uu} = 16 X + H^{(2)}_{k-1} + ∑_i E_{ui}²`). -/
theorem harm_diag (hp5 : 5 ≤ p) {k r d u : ℕ} (hrd : r + d = p) (hkr : k ≤ r) (hu : u < k) :
    -(1 / 16) * ∑ t ∈ Icc 1 u, ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2)
      - (1 / 16) * ∑ c ∈ Ico k r, ((((c : ℕ) : ZMod p) - u)⁻¹) ^ 2
      = (1 / 16) * (hm2 p (k - 1) + ∑ i ∈ Icc 1 d, (((u : ZMod p) + (i : ℕ))⁻¹) ^ 2) := by
  have hIcc : Icc 1 u = Ioc 0 u := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hA : ∑ t ∈ Icc 1 u, ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2) =
      hm2 p u - (hm2 p (k - 1) - hm2 p (k - 1 - u)) := by
    rw [hIcc, Finset.sum_sub_distrib, sum_Ioc_hm2 u (Nat.zero_le u)]
    have : ∑ t ∈ Ioc 0 u, (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2 =
        ∑ t ∈ Ioc 0 u, (((k : ZMod p) - (t : ℕ))⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← neg_sub, inv_neg, neg_sq]
    rw [this, sum_Ioc_rev2 u (Nat.zero_le u) hu]
    simp [hm2]
  have hB : ∑ c ∈ Ico k r, ((((c : ℕ) : ZMod p) - u)⁻¹) ^ 2 =
      hm2 p (r - 1 - u) - hm2 p (k - 1 - u) :=
    sum_Ico_shift2 (p := p) (u := u) (a := k) hu r hkr
  have r1 : hm2 p (r - 1 - u) = - hm2 p (u + d) := by
    have := hm2_refl hp5 (u + d) (by omega)
    rw [show r - 1 - u = p - 1 - (u + d) by omega]; exact this
  have hC := sum_Icc_shift2 (p := p) u d
  rw [hA, hB, r1, hC]
  ring

end CatalanCore.Arith.Hybrid
