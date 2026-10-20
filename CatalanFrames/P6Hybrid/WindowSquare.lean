module

public import CatalanFrames.P6Hybrid.Admissible
public import CatalanCore.NT.PowerDvd

@[expose] public section

open CatalanCore

namespace CatalanFrames.P6Hybrid

/-- Discard all primes whose squares divide the supplied denominator. -/
def P6BadSquare (l q : ℕ) : Prop := l ^ 2 ∣ q

/-- The full class `1 mod 6` with square-divisor bad primes has window cost 1. -/
theorem p6_window_square : HasWindowC P6Cls1 P6BadSquare (((1 : ℚ)) : ℝ) := by
  have h := PrimeRule.hasWindowSet (PrimeRule.ofPowDvd 6 1 isUnit_one 2)
    (PrimeRule.ofPowDvd_badBound 6 1 isUnit_one (by norm_num)) ({1} : Finset (ZMod 6))
    (fun c hc => by
      have e : c = 1 := Finset.mem_singleton.mp (show c ∈ ({1} : Finset (ZMod 6)) from hc)
      rw [e]; exact isUnit_one)
    (Finset.singleton_nonempty 1) (s := (((1 : ℚ)) : ℝ))
    (by simp [PrimeRule.ofPowDvd, show Nat.totient 6 = 2 by decide])
  exact h


end CatalanFrames.P6Hybrid
