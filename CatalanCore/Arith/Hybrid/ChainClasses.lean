module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

@[expose] public section

/-!
# Translation of residue chains within a cut interval

The arithmetic application cuts at singular nodes and at the exits `r + j*p`.
This elementary geometry is independent of a frame, a prime, or a matrix model.
Working in integers avoids truncated subtraction at the bottom of a chain.
-/

namespace CatalanCore.Arith.Hybrid.ChainClasses

/-- No cut occurs in the half-open interval `(a,b]`. -/
def NoCut (cut : ℤ → Prop) (a b : ℤ) : Prop :=
  ∀ t, a < t → t ≤ b → ¬ cut t

/-- A positive translate of `z` lies in the core `[0,r)`. -/
def InChain (p r z i : ℤ) : Prop := 0 < i ∧ 0 ≤ z - i * p ∧ z - i * p < r

/-- Entry and exit cuts, together with an arbitrary periodic singular set. -/
def Cut (p r : ℤ) (sing : ℤ → Prop) (t : ℤ) : Prop :=
  sing t ∨ (∃ j : ℤ, t = j * p) ∨ ∃ j : ℤ, t = r + j * p

theorem chain_iff {p r a b i : ℤ} {sing : ℤ → Prop} (hab : a ≤ b)
    (h : NoCut (Cut p r sing) a b) : InChain p r a i ↔ InChain p r b i := by
  constructor
  · rintro ⟨hi, ha0, har⟩
    refine ⟨hi, by omega, ?_⟩
    by_contra hb
    have hc : Cut p r sing (r + i * p) := Or.inr (Or.inr ⟨i, rfl⟩)
    exact h _ (by omega) (by omega) hc
  · rintro ⟨hi, hb0, hbr⟩
    refine ⟨hi, ?_, by omega⟩
    by_contra ha
    have hc : Cut p r sing (i * p) := Or.inr (Or.inl ⟨i, rfl⟩)
    exact h _ (by omega) (by omega) hc

/-- Translating down any number of periods preserves the absence of singular cuts. -/
theorem noCut_translate {p r a b i : ℤ} {sing : ℤ → Prop}
    (hperiod : ∀ t j : ℤ, sing (t + j * p) ↔ sing t)
    (h : NoCut (Cut p r sing) a b) : NoCut sing (a - i * p) (b - i * p) := by
  intro t hat htb ht
  have hc : Cut p r sing (t + i * p) := Or.inl ((hperiod t i).mpr ht)
  exact h _ (by omega) (by omega) hc

/-- Any datum constant across intervals free of singular cuts is preserved at
every corresponding pair of core-chain nodes. -/
theorem chain_data_eq {α : Type*} {p r a b i : ℤ} {sing : ℤ → Prop}
    (v : ℤ → α) (hab : a ≤ b)
    (hperiod : ∀ t j : ℤ, sing (t + j * p) ↔ sing t)
    (hv : ∀ x y, x ≤ y → NoCut sing x y → v x = v y)
    (h : NoCut (Cut p r sing) a b) : v (a - i * p) = v (b - i * p) :=
  hv _ _ (by omega) (noCut_translate hperiod h)

/-- The two arithmetic singular residue classes for a λ-like frame. -/
def Singular (p o t : ℤ) : Prop := p ∣ t ∨ p ∣ 4 * t - o

theorem singular_periodic (p o t j : ℤ) :
    Singular p o (t + j * p) ↔ Singular p o t := by
  unfold Singular
  have h1 : p ∣ t + j * p ↔ p ∣ t := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - j, by linear_combination hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k + j, by linear_combination hk⟩
  have h2 : p ∣ 4 * (t + j * p) - o ↔ p ∣ 4 * t - o := by
    have he : 4 * (t + j * p) - o = (4 * t - o) + (4 * j) * p := by ring
    rw [he]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - 4 * j, by linear_combination hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k + 4 * j, by linear_combination hk⟩
  rw [h1, h2]

end CatalanCore.Arith.Hybrid.ChainClasses
