import CatalanCore.Uniform.Bank.Fifths.Final
import CatalanCore.Uniform.Content.BankShared.BudgetedOne
import CatalanCore.Uniform.Content.BankShared.Budgeted
set_option Elab.async false

/-! # Fifths content: the assembly interface (lane B, B5b)

`fifths_content_of_pricing` instantiates the shared budgeted assembler (H17, contract 4) on the
even-scale restriction of the fifths family `F5.family Fr depth`, with the exact constant `Lam5`.
The exceptional-prime hypothesis is the crude exponent (`Ecrude`) at the primes dividing the
modulus.  Everything that remains is the member-level pricing: a `price` with `GLE` at every prime
(layers T, R, S, LP1/LP2, M3D) and the piece covers of the epsilon-templates. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid Filter Finset

/-- The fifths family at even scales. -/
noncomputable abbrev FamE (Fr : Frame) (depth : ℕ) :=
  (F5.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)

theorem fifths_content_of_pricing (Fr : Frame) (depth : ℕ) (M : ℕ) [NeZero M] (cE : ℕ)
    (price : (FamE Fr depth).ι → ℕ → ℕ) (cut : (FamE Fr depth).ι → ℕ)
    (gle : ∀ i, (FamE Fr depth).Adm i → ∀ (p : ℕ) [Fact p.Prime],
      GLE p (price i p) ((FamE Fr depth).Q i))
    (zero_ge : ∀ i, (FamE Fr depth).Adm i → ∀ p : ℕ, p.Prime → cut i ≤ p → price i p = 0)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Lam5 + ε)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ p : ℕ, p.Prime → (p : ZMod M) = c → ⌊(tmpl ε c).tend * F5.scale i⌋₊ < p → price i p = 0)
    (tail_lt : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ⌊(tmpl ε c).tend * F5.scale i⌋₊ < cut i)
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl ε c).t1 * F5.scale i⌋₊ → p.Prime → (p : ZMod M) = c →
        (price i p : ℝ) ≤ (tmpl ε c).α0 * F5.scale i + B.X (F5.scale i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ P ∈ (tmpl ε c).l, Covers c (fun p => (price i p : ℝ)) (F5.scale i) P)
    (hE : ∀ i, (FamE Fr depth).Adm i → ∀ p ∈ M.primeFactors,
      price i p ≤ Ecrude cE (F5.scale i) p) :
    HasScaledContent (FamE Fr depth) F5.scale Lam5 :=
  hasScaledContent_budgeted_lim (FamE Fr depth) F5.scale M
    (fun i => NodeFamily.family_degree Fr F5.geometry depth i) price cut gle zero_ge B Lam5 tmpl
    hmass tail tail_lt pre cov
    (exc_of_Ecrude (FamE Fr depth) F5.scale M price cE hE)

end CatalanCore.Uniform.Bank.FifthsContent
