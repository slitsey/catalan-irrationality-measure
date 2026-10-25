module
public import CatalanFrames.HybGen.ClassBand
@[expose] public section
namespace CatalanFrames.HybGen

/-- Away from primes dividing the offset, prime-power zeros split into the two linear factors. -/
theorem primePower_split {M u p n k : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u)
    (huk : u ≤ M*k) (hd : p^n ∣ k*(M*k-u)) :
    p^n ∣ k ∨ p^n ∣ M*k-u := by
  by_cases hpk : p ∣ k
  · left
    have hcop : Nat.Coprime p (M*k-u) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have hMk : p ∣ M*k := Dvd.dvd.mul_left hpk M
      have hu : p ∣ u := by
        have hh := Nat.dvd_sub hMk h
        have he : M*k-(M*k-u)=u := by omega
        rwa [he] at hh
      exact hpu hu
    exact (Nat.Coprime.pow_left n hcop).dvd_of_dvd_mul_right hd
  · right
    have hcop : Nat.Coprime (p^n) k :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
    exact hcop.dvd_of_dvd_mul_left hd
end CatalanFrames.HybGen
#print axioms CatalanFrames.HybGen.primePower_split
