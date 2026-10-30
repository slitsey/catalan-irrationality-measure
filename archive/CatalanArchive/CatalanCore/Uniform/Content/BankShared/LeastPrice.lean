import CatalanCore.Uniform.Content.ClearMin
set_option Elab.async false
namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Arith.Hybrid Polynomial

/-- The least valid exponent of the same actual polynomial. Existence must be proved. -/
noncomputable def leastGLE (p : ℕ) [Fact p.Prime] (f : ℚ[X])
    (h : ∃ e : ℕ, GLE p e f) : ℕ := by
  classical
  exact Nat.find h

theorem leastGLE_valid (p : ℕ) [Fact p.Prime] (f : ℚ[X])
    (h : ∃ e : ℕ, GLE p e f) : GLE p (leastGLE p f h) f := by
  classical
  exact Nat.find_spec h

theorem leastGLE_le (p : ℕ) [Fact p.Prime] (f : ℚ[X])
    (h : ∃ e : ℕ, GLE p e f) (e : ℕ) (he : GLE p e f) : leastGLE p f h ≤ e := by
  classical
  exact Nat.find_min' h he

/-- A finite cutoff containing every possible coefficient-denominator prime. -/
noncomputable def coefficientCut (f : ℚ[X]) : ℕ :=
  max 1 (f.support.sup (fun k => (f.coeff k).den)) + 1

theorem gle_zero_of_coefficientCut (p : ℕ) [Fact p.Prime] (f : ℚ[X])
    (hp : coefficientCut f ≤ p) : GLE p 0 f := by
  intro k
  simp only [pow_zero, one_mul]
  by_cases hk : k ∈ f.support
  · have hden : (f.coeff k).den < p := by
      have hs := Finset.le_sup (f := fun k => (f.coeff k).den) hk
      unfold coefficientCut at hp
      omega
    intro hd
    have hle := Nat.le_of_dvd (f.coeff k).den_pos hd
    omega
  · have hz : f.coeff k = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hk
    rw [hz]
    exact (LocRing p).zero_mem

#print axioms leastGLE_valid
#print axioms leastGLE_le
end CatalanCore.Uniform.Content.BankShared
