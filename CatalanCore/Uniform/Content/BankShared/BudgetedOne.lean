import CatalanCore.Uniform.Content.BankShared.Budgeted
import CatalanCore.Uniform.Content.BankShared.ExceptionSmall
set_option Elab.async false

/-! # Shared contract 4, single-template form and the crude-exponent budget (lane H17)

* `hasScaledContent_budgeted`: one finite template, constant `contentConstant M tmpl`, the prime
  cutoff `⌊commonEnd * scale⌋ + M + 1` of `SmallPrimes.ContentCoverB`; the pointwise hypothesis
  `price <= K * r` at the primes dividing `M` is replaced by the `o(scale^2)` budget `exc`.
* `exc_of_Ecrude`: the budget `exc` holds when the price at every prime dividing `M` is at most the
  crude exponent `Ecrude c (scale i) p` (contract 3). -/

namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset Polynomial
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.SmallPrimes

/-- **Shared contract 4 (`hasScaledContent_budgeted`).** -/
theorem hasScaledContent_budgeted (Fam : PolyFamily) (sc : Fam.ι → ℕ) (M : ℕ) [NeZero M]
    (hnat : ∀ i, (Fam.Q i).natDegree ≤ Fam.deg i)
    (price : Fam.ι → ℕ → ℕ)
    (gle : ∀ i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], GLE p (price i p) (Fam.Q i))
    (B : SmallBudget) (tmpl : ZMod M → Template)
    (tail : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * sc i⌋₊ < p → price i p = 0)
    (pre : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl c).t1 * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
        (price i p : ℝ) ≤ (tmpl c).α0 * sc i + B.X (sc i) p)
    (cov : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l,
      Covers c (fun p => (price i p : ℝ)) (sc i) P)
    (exc : ∀ ε : ℝ, 0 < ε → ∃ R0 : ℕ, ∀ i, Fam.Adm i → R0 ≤ sc i →
      ∑ p ∈ M.primeFactors, (price i p : ℝ) * Real.log p ≤ ε * (sc i : ℝ) ^ 2) :
    HasScaledContent Fam sc (contentConstant M tmpl) := by
  have hlt : ∀ i (c : ZMod M), ⌊(tmpl c).tend * sc i⌋₊ <
      ⌊commonEnd M tmpl * sc i⌋₊ + M + 1 := by
    intro i c
    have h1 : (tmpl c).tend * sc i ≤ commonEnd M tmpl * sc i :=
      mul_le_mul_of_nonneg_right (tend_le_commonEnd M tmpl c) (Nat.cast_nonneg _)
    have h2 := Nat.floor_le_floor h1
    omega
  refine hasScaledContent_budgeted_lim Fam sc M hnat price
    (fun i => ⌊commonEnd M tmpl * sc i⌋₊ + M + 1) gle ?_ B (contentConstant M tmpl)
    (fun _ => tmpl) (fun ε hε => by show contentConstant M tmpl ≤ _; linarith)
    (fun _ _ i hi c hc p hp hpc hlt' => tail i hi c hc p hp hpc hlt')
    (fun _ _ i _ c _ => hlt i c)
    (fun _ _ i hi c hc p h1 hp hpc => pre i hi c hc p h1 hp hpc)
    (fun _ _ i hi c hc P hP => cov i hi c hc P hP) exc
  intro i hi p hp hcut
  by_cases hd : p ∣ M
  · have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hd
    omega
  · have hc : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
    exact tail i hi (p : ZMod M) hc p hp rfl
      (lt_of_lt_of_le (hlt i _) hcut)

/-- The budget `exc` from the crude exponent: if the price at each prime dividing `M` is at most
`Ecrude c (sc i) p` (here `c` is the fixed frame constant), the weighted sum is `o(scale^2)`. -/
theorem exc_of_Ecrude (Fam : PolyFamily) (sc : Fam.ι → ℕ) (M : ℕ) [NeZero M]
    (price : Fam.ι → ℕ → ℕ) (c : ℕ)
    (hE : ∀ i, Fam.Adm i → ∀ p ∈ M.primeFactors, price i p ≤ Ecrude c (sc i) p) :
    ∀ ε : ℝ, 0 < ε → ∃ R0 : ℕ, ∀ i, Fam.Adm i → R0 ≤ sc i →
      ∑ p ∈ M.primeFactors, (price i p : ℝ) * Real.log p ≤ ε * (sc i : ℝ) ^ 2 := by
  intro ε hε
  have hF : ∀ p ∈ M.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.1 (fixed_exception_E_crude_small M.primeFactors hF c ε hε)
  refine ⟨R0, fun i hi hR => ?_⟩
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (hR0 (sc i) hR)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hE i hi p hp) (Real.log_natCast_nonneg p)

end CatalanCore.Uniform.Content.BankShared
