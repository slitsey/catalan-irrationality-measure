module

public import CatalanCore.NT.PowerDvd
public import CatalanCore.NT.Rules

@[expose] public section

/-! # Generic prime window for power-divisor bad primes (M9)

For a modulus `M`, a set `S` of unit classes and a power `k > 0`, primes in the classes `S`
avoiding `l ^ k ∣ q` form a window of cost `s` whenever `(1/k) φ(M) / |S| ≤ s`.
The thirds frames use `M = 6`, `S = {1}`, `k = 2`, `s = 1`.
-/

open CatalanCore

namespace CatalanFrames.Thirds

/-- Bad primes: those whose `k`-th power divides the denominator. -/
def PowBad (k l q : ℕ) : Prop := l ^ k ∣ q

/-- Prime class: residue mod `M` lies in `S`. -/
def ClsIn (M : ℕ) (S : Finset (ZMod M)) (l : ℕ) : Prop := (l : ZMod M) ∈ S

theorem hasWindow_powBad (M : ℕ) [NeZero M] (S : Finset (ZMod M)) (hS : ∀ c ∈ S, IsUnit c)
    (hne : S.Nonempty) {k : ℕ} (hk : 0 < k) {s : ℝ}
    (hs : (1 / (k : ℝ)) * (Nat.totient M : ℝ) / (S.card : ℝ) ≤ s) :
    HasWindowC (ClsIn M S) (PowBad k) s := by
  have h := PrimeRule.hasWindowSet (PrimeRule.ofPowDvd M 1 isUnit_one k)
    (PrimeRule.ofPowDvd_badBound M 1 isUnit_one hk) S hS hne (s := s)
    (by simpa [PrimeRule.ofPowDvd] using hs)
  exact h

/-- Class `1 mod 6`, bad primes `l ^ 2 ∣ q`: window cost `1`. -/
theorem window_one_mod_six : HasWindowC (ClsIn 6 {1}) (PowBad 2) 1 :=
  hasWindow_powBad 6 {1} (fun c hc => by
      rw [Finset.mem_singleton.mp hc]; exact isUnit_one)
    (Finset.singleton_nonempty 1) (by norm_num) (by
      have : Nat.totient 6 = 2 := by decide
      simp [this])

end CatalanFrames.Thirds
