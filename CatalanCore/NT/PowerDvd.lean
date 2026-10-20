module

public import CatalanCore.NT.Rules

@[expose] public section

/-!
# Prime windows excluding power divisors

`ofPowDvd` discards every prime whose `k`th power divides the denominator.
Unlike `ofSqDvd`, it makes no assertion about larger valuations.  It is useful
when nonvanishing is known only at denominator valuations below `k`.
-/

namespace CatalanCore

/-- Exclude all `k`th-power divisors, with bad-prime mass at most `1/k`. -/
def PrimeRule.ofPowDvd (m : ℕ) (r : ZMod m) (hr : IsUnit r) (k : ℕ) : PrimeRule where
  m := m
  r := r
  hr := hr
  Bad := fun l q => l ^ k ∣ q
  weight := 1 / k

instance (m : ℕ) (r : ZMod m) (hr : IsUnit r) (k : ℕ) [NeZero m] :
    NeZero (PrimeRule.ofPowDvd m r hr k).m := ‹NeZero m›

theorem PrimeRule.ofPowDvd_badBound (m : ℕ) (r : ZMod m) (hr : IsUnit r)
    {k : ℕ} (hk : 0 < k) : (PrimeRule.ofPowDvd m r hr k).BadBound :=
  PrimeRule.badBound_of_pow_dvd _ hk (fun _ _ h => h) (by rfl)

theorem PrimeRule.ofPowDvd_hasWindow (m : ℕ) (r : ZMod m) (hr : IsUnit r)
    [NeZero m] {k : ℕ} (hk : 0 < k) : (PrimeRule.ofPowDvd m r hr k).HasWindow :=
  PrimeRule.hasWindow _ (PrimeRule.ofPowDvd_badBound m r hr hk)

/-- Reduction of a rational fraction cannot introduce a new power divisor
of its denominator. No coprimality hypothesis on the supplied fraction is needed. -/
theorem not_pow_dvd_rat_den (l k : ℕ) (p q : ℤ)
    (h : ¬ l ^ k ∣ q.natAbs) : ¬ l ^ k ∣ ((p : ℚ) / q).den := by
  intro hd
  apply h
  have hden := Rat.den_dvd p q
  rw [Rat.divInt_eq_div] at hden
  exact hd.trans (Int.natCast_dvd.mp hden)

end CatalanCore
