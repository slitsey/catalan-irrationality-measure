module

public import CatalanCore.Uniform.Content.UFMoments.DirOf

@[expose] public section

/-!
# UF moments, frame layer: shifting a chain inside one arc

For a `PoleData` frame, a shift `Δ` and nodes `a` whose windows `(a, a+Δ]` contain no singular
index (`NoSingWin`), and a frame whose regular increments reduce periodically (`RegRed`:
`red Δ_k` depends only on `k mod p` for regular `k`):

* `shift_mem`: `F(a+Δ) - F(a) ∈ ℤ_(p)`;
* `shift_cong`: for `a ≡ b (mod p)`, `(F(a+Δ) - F(a)) - (F(b+Δ) - F(b)) ∈ p ℤ_(p)`;
* `Mn_shift_mem`: for `a ≡ b`, `Mn(a+Δ, b+Δ) - Mn(a, b) ∈ ℤ_(p)` (off-diagonal and diagonal).

These are the rational facts behind `TypeData` (same chain digits, same arc).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- No singular index in the window `(a, a + Δ]`. -/
def NoSingWin (D : PoleData Fr p N) (a Δ : ℕ) : Prop :=
  ∀ k : ℕ, a < k → k ≤ a + Δ → ¬ D.singular (k : ℤ)

/-- Regular increments reduce periodically. -/
def RegRed (D : PoleData Fr p N) : Prop :=
  ∀ k k' : ℕ, 1 ≤ k → k < N → 1 ≤ k' → k' < N → ¬ D.singular (k : ℤ) → ¬ D.singular (k' : ℤ) →
    ((k : ℕ) : ZMod p) = ((k' : ℕ) : ZMod p) → red p (Fr.Delta k) = red p (Fr.Delta k')

theorem good_zero_dvd {x : ℚ} (h : Good p x 0) : ∃ w ∈ S p, x = p * w := by
  have hx := h.mem
  have h0 : redQ p ⟨x, hx⟩ = 0 := h.eq
  obtain ⟨w, hw⟩ := (redQ_eq_zero_iff p _).1 h0
  refine ⟨w, w.2, ?_⟩
  have := congrArg (fun z : LocRing p => (z : ℚ)) hw
  simpa using this

theorem Fp_succ (Fr : Frame) (n : ℕ) : Fp Fr (n + 1) = Fp Fr n + Fr.Delta (n + 1) := by
  unfold Fp
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

theorem shift_mem (D : PoleData Fr p N) (a Δ : ℕ) (hN : a + Δ < N) (hw : NoSingWin D a Δ) :
    Fp Fr (a + Δ) - Fp Fr a ∈ S p := by
  induction Δ with
  | zero => simpa using (S p).zero_mem
  | succ n ih =>
    have ih' := ih (by omega) (fun k h1 h2 => hw k h1 (by omega))
    rw [show a + (n + 1) = (a + n) + 1 by ring, Fp_succ]
    have hreg := D.regular_delta (a + n + 1) (by omega) (by omega) (by
      have := hw (a + n + 1) (by omega) (by omega); exact_mod_cast this)
    have e : Fp Fr (a + n) + Fr.Delta (a + n + 1) - Fp Fr a =
        (Fp Fr (a + n) - Fp Fr a) + Fr.Delta (a + n + 1) := by ring
    rw [e]
    exact (S p).add_mem ih' hreg

theorem shift_cong (D : PoleData Fr p N) (hR : RegRed D) (a b Δ : ℕ)
    (hab : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p))
    (ha : a + Δ < N) (hb : b + Δ < N) (hwa : NoSingWin D a Δ) (hwb : NoSingWin D b Δ) :
    ∃ w ∈ S p, (Fp Fr (a + Δ) - Fp Fr a) - (Fp Fr (b + Δ) - Fp Fr b) = p * w := by
  apply good_zero_dvd
  induction Δ with
  | zero => simpa using (Good.zero (ℓ := p))
  | succ n ih =>
    have ih' := ih (by omega) (by omega) (fun k h1 h2 => hwa k h1 (by omega))
      (fun k h1 h2 => hwb k h1 (by omega))
    have hsa : ¬ D.singular ((a + n + 1 : ℕ) : ℤ) := hwa (a + n + 1) (by omega) (by omega)
    have hsb : ¬ D.singular ((b + n + 1 : ℕ) : ℤ) := hwb (b + n + 1) (by omega) (by omega)
    have ga := good_red (D.regular_delta (a + n + 1) (by omega) (by omega) (by exact_mod_cast hsa))
    have gb := good_red (D.regular_delta (b + n + 1) (by omega) (by omega) (by exact_mod_cast hsb))
    have hrr : red p (Fr.Delta (a + n + 1)) = red p (Fr.Delta (b + n + 1)) :=
      hR _ _ (by omega) (by omega) (by omega) (by omega) hsa hsb (by push_cast; rw [hab])
    have g : Good p ((Fp Fr (a + n) - Fp Fr a - (Fp Fr (b + n) - Fp Fr b)) +
        (Fr.Delta (a + n + 1) - Fr.Delta (b + n + 1))) 0 :=
      (ih'.add (ga.sub gb)).congr (by rw [hrr, sub_self, add_zero])
    refine g.congr' ?_
    rw [show a + (n + 1) = (a + n) + 1 by ring, show b + (n + 1) = (b + n) + 1 by ring,
      Fp_succ, Fp_succ]
    ring

/-- A nonzero multiple of `p` below `p²`, divided by `p`, is a unit of `ℤ_(p)`. -/
theorem inv_digit_mem {a b : ℕ} (hab : a < b) (hb : b < p * p)
    (hcong : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) :
    ∃ δ : ℕ, 0 < δ ∧ δ < p ∧ (b : ℚ) - a = p * δ := by
  have hdvd : p ∣ b - a :=
    (Nat.modEq_iff_dvd' hab.le).1 ((ZMod.natCast_eq_natCast_iff a b p).1 hcong)
  obtain ⟨δ, hδ⟩ := hdvd
  have hp := (Fact.out : p.Prime).pos
  refine ⟨δ, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos δ with h | h
    · rw [h, mul_zero] at hδ; omega
    · exact h
  · by_contra h
    push Not at h
    have : p * p ≤ p * δ := Nat.mul_le_mul_left p h
    omega
  · have : ((b - a : ℕ) : ℚ) = (p * δ : ℕ) := by rw [hδ]
    push_cast [Nat.cast_sub hab.le] at this
    exact this

end CatalanCore.Uniform.Content.UFMoments
