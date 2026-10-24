module

public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section

/-! # Residue dictionaries restricted to the actual good primes

A class can contain a finite bad prime (for example3 in class3 modulo4).
The good-prime predicate is therefore an input, rather than a conclusion
asserted for every prime of the residue class.
-/

namespace CatalanFrames.HybGen

/-- Linear first-pole bounds on the good primes of an arbitrary residue class.
All modulus, pole, band and exceptional-prime data remain parameters. -/
def GoodClassBand {M : ℕ} (c : ZMod M) (Good : ℕ → Prop)
    (kq : ℕ → ℕ) (d j lo hi : ℕ) : Prop :=
  ∀ p, p.Prime → Good p → (p : ZMod M) = c →
    j * p + lo ≤ d * kq p ∧ d * kq p ≤ j * p + hi

end CatalanFrames.HybGen
