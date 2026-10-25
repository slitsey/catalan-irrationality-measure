module
public import CatalanFrames.Fifths.Roots
@[expose] public section
namespace CatalanFrames.Fifths
/-- Precisely the finite primes handled by the fifths local clearer. -/
def badPrimes : Finset ℕ := {2,3,5}
theorem prime_ge_seven {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) :
    7 ≤ p := by
  have hodd : p%2 = 1 := by have := hp.eq_two_or_odd; omega
  have := hp.two_le
  omega
theorem good_power_base {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hb : ∀ b ∈ badPrimes, ¬ b ∣ p^n) : 7 ≤ p := by
  have hd : p ∣ p^n := dvd_pow_self p hn.ne'
  apply prime_ge_seven hp
  · intro h; subst p; exact hb 2 (by simp [badPrimes]) hd
  · intro h; subst p; exact hb 3 (by simp [badPrimes]) hd
  · intro h; subst p; exact hb 5 (by simp [badPrimes]) hd
theorem good_primePower_inputs {q : ℕ} (hq : IsPrimePow q)
    (hb : ∀ b ∈ badPrimes, ¬ b ∣ q) : 5 ≤ q ∧ q%5 ≠ 0 := by
  obtain ⟨p,n,hp,hn,rfl⟩ := hq
  have hp7 := good_power_base hp.nat_prime hn hb
  have hle : p ≤ p^n := Nat.le_self_pow hn.ne' p
  refine ⟨by omega,?_⟩
  intro hz
  exact hb 5 (by simp [badPrimes]) (Nat.dvd_of_mod_eq_zero hz)
/-- The displayed first root actually divides Phi, not only a lower bound for possible roots. -/
theorem firstRoot_att {u q : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5) (hq : 5 ≤ q)
    (hunit : q%5 ≠ 0) :
    0 < firstRoot u q ∧ q ∣ firstRoot u q*(5*firstRoot u q-u) := by
  have hs := firstRoot_spec hu0 hu1 hq hunit
  refine ⟨hs.2.1,?_⟩
  have he : 5*firstRoot u q-u = classIndex u q*q := by omega
  rw [he]
  refine ⟨firstRoot u q*classIndex u q,?_⟩
  ring
theorem firstRoot_att_good {u q : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5)
    (hq : IsPrimePow q) (hb : ∀ b ∈ badPrimes, ¬ b ∣ q) :
    0 < firstRoot u q ∧ q ∣ firstRoot u q*(5*firstRoot u q-u) := by
  obtain ⟨hq5,hunit⟩ := good_primePower_inputs hq hb
  exact firstRoot_att hu0 hu1 hq5 hunit
/-- Full ContentData minimality, uniformly over all prime powers avoiding2,3,5. -/
theorem firstRoot_minimal_good {u q k : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5)
    (hq : IsPrimePow q) (hb : ∀ b ∈ badPrimes, ¬ b ∣ q) (hk : 0 < k)
    (hd : q ∣ k*(5*k-u)) : firstRoot u q ≤ k ∧ q ≤ 5*k := by
  obtain ⟨p,n,hp,hn,rfl⟩ := hq
  have hp7 := good_power_base hp.nat_prime hn hb
  have hq5 : 5 ≤ p^n := le_trans (by omega : 5 ≤ p) (Nat.le_self_pow hn.ne' p)
  have hunit : p^n%5 ≠ 0 := by
    intro hz
    exact hb 5 (by simp [badPrimes]) (Nat.dvd_of_mod_eq_zero hz)
  have hpu : ¬ p ∣ u := by
    intro hd
    have hle : p ≤ u := Nat.le_of_dvd (by omega) hd
    omega
  exact firstRoot_le_of_dvd hp.nat_prime hn hu0 hu1 hq5 hunit hpu hk hd
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.firstRoot_att_good
#print axioms CatalanFrames.Fifths.firstRoot_minimal_good
