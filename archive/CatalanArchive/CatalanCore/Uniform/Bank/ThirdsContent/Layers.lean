import CatalanCore.Uniform.Bank.ThirdsContent.Assemble
set_option Elab.async false

/-! # Layer list for the thirds content (lane B, B4b)

A `Layer` is a member-level pricing valid at the primes not dividing `M`: an exponent `price`
with `GLE`, vanishing above `cut`.  Layers combine by pointwise minimum, so the UF layer (when
available) is a further `Layer.min` with no rework of the assembly. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid CatalanCore.Basic

structure Layer (Fam : PolyFamily) (M : ℕ) where
  price : Fam.ι → ℕ → ℕ
  cut : Fam.ι → ℕ
  gle : ∀ i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → GLE p (price i p) (Fam.Q i)
  zero_ge : ∀ i, Fam.Adm i → ∀ p : ℕ, p.Prime → ¬ p ∣ M → cut i ≤ p → price i p = 0

namespace Layer
variable {Fam : PolyFamily} {M : ℕ}

/-- Pointwise minimum of two layers (via `if`, to keep the case analysis explicit). -/
def min (A B : Layer Fam M) : Layer Fam M where
  price i p := if A.price i p ≤ B.price i p then A.price i p else B.price i p
  cut i := if A.cut i ≤ B.cut i then A.cut i else B.cut i
  gle i hi p _ hM := by
    by_cases h : A.price i p ≤ B.price i p
    · simp only [if_pos h]; exact A.gle i hi p hM
    · simp only [if_neg h]; exact B.gle i hi p hM
  zero_ge i hi p hp hM hc := by
    by_cases h : A.cut i ≤ B.cut i
    · simp only [if_pos h] at hc
      have := A.zero_ge i hi p hp hM hc
      simp [this]
    · simp only [if_neg h] at hc
      have := B.zero_ge i hi p hp hM hc
      simp [this]

theorem min_le_left (A B : Layer Fam M) (i p) : (A.min B).price i p ≤ A.price i p := by
  show (if A.price i p ≤ B.price i p then A.price i p else B.price i p) ≤ _
  split_ifs with h <;> omega

theorem min_le_right (A B : Layer Fam M) (i p) : (A.min B).price i p ≤ B.price i p := by
  show (if A.price i p ≤ B.price i p then A.price i p else B.price i p) ≤ _
  split_ifs with h <;> omega

end Layer

end CatalanCore.Uniform.Bank.ThirdsContent
