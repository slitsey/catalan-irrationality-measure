module

public import CatalanCore.Uniform.Bank.ThirdsContent.Alt
public import CatalanCore.Uniform.Bank.Thirds.Final
public import CatalanCore.Uniform.Content.BankShared.BudgetedOne
public import CatalanCore.Uniform.Content.BankShared.Budgeted

@[expose] public section
set_option Elab.async false

/-! # Thirds content: assembly with the exceptional primes discharged (lane B, B4b)

`thirds_content_of_layers`: `ThirdsContent Fr depth` follows from layer pricing `lp` that is
only needed at primes NOT dividing the modulus `M`.  At primes dividing `M` the price is the crude
exponent `Ecrude (cFr Fr)`, which clears every member (`altGeom_gle_Ecrude`, proved here with no
hypothesis); the cutoff is raised above `M`, so no condition on the exceptional primes remains.
The remaining hypotheses are exactly the member-level layer pricing and the epsilon-templates. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset

/-- The thirds family at even scales. -/
noncomputable abbrev FamE (Fr : Frame) (depth : ℕ) :=
  (G310.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)

lemma not_dvd_of_unit {M : ℕ} {p : ℕ} (hp : p.Prime) {c : ZMod M} (hc : IsUnit c)
    (hpc : (p : ZMod M) = c) : ¬ p ∣ M := by
  rw [← ZMod.isUnit_prime_iff_not_dvd hp, hpc]; exact hc

theorem thirds_content_of_layers (Fr : Frame) (depth : ℕ) (M : ℕ) [NeZero M] (Lam : ℝ)
    (lp : (FamE Fr depth).ι → ℕ → ℕ) (lcut : (FamE Fr depth).ι → ℕ)
    (gle : ∀ i, (FamE Fr depth).Adm i → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
      GLE p (lp i p) ((FamE Fr depth).Q i))
    (zero_ge : ∀ i, (FamE Fr depth).Adm i → ∀ p : ℕ, p.Prime → ¬ p ∣ M → lcut i ≤ p →
      lp i p = 0)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Lam + ε)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ p : ℕ, p.Prime → (p : ZMod M) = c → ⌊(tmpl ε c).tend * G310.scale i⌋₊ < p → lp i p = 0)
    (tail_lt : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ⌊(tmpl ε c).tend * G310.scale i⌋₊ < lcut i)
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl ε c).t1 * G310.scale i⌋₊ → p.Prime → (p : ZMod M) = c →
        (lp i p : ℝ) ≤ (tmpl ε c).α0 * G310.scale i + B.X (G310.scale i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ P ∈ (tmpl ε c).l, Covers c (fun p => (lp i p : ℝ)) (G310.scale i) P) :
    HasScaledContent (FamE Fr depth) G310.scale Lam := by
  classical
  let price : (FamE Fr depth).ι → ℕ → ℕ := fun i p =>
    if p ∣ M then Ecrude (cFr Fr) i.1 p else lp i p
  have hpr : ∀ i p, ¬ p ∣ M → price i p = lp i p := fun i p h => by simp [price, h]
  refine hasScaledContent_budgeted_lim (FamE Fr depth) G310.scale M
    (fun i => NodeFamily.family_degree Fr G310.geometry depth i) price
    (fun i => max (lcut i) (M + 1)) ?_ ?_ B Lam tmpl hmass ?_ ?_ ?_ ?_
    (exc_of_Ecrude (FamE Fr depth) G310.scale M price (cFr Fr) ?_)
  · intro i hi p hpF
    by_cases h : p ∣ M
    · simp only [price, h, if_true]
      exact altGeom_gle_Ecrude (3 / 10) c310_pos (by norm_num) Fr depth i hi.2 p
    · simp only [price, h, if_false]
      exact gle i hi p h
  · intro i hi p hp hcut
    have hM : ¬ p ∣ M := fun h => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h
      have := (le_max_right (lcut i) (M + 1)).trans hcut
      omega
    rw [hpr i p hM]
    exact zero_ge i hi p hp hM ((le_max_left _ _).trans hcut)
  · intro ε hε i hi c hc p hp hpc hlt
    rw [hpr i p (not_dvd_of_unit hp hc hpc)]
    exact tail ε hε i hi c hc p hp hpc hlt
  · intro ε hε i hi c hc
    exact (tail_lt ε hε i hi c hc).trans_le (le_max_left _ _)
  · intro ε hε i hi c hc p h1 hp hpc
    rw [show (price i p : ℝ) = (lp i p : ℝ) from by rw [hpr i p (not_dvd_of_unit hp hc hpc)]]
    exact pre ε hε i hi c hc p h1 hp hpc
  · intro ε hε i hi c hc P hP p h1 h2 hp hpc
    show (price i p : ℝ) ≤ _
    rw [show (price i p : ℝ) = (lp i p : ℝ) from by rw [hpr i p (not_dvd_of_unit hp hc hpc)]]
    exact cov ε hε i hi c hc P hP p h1 h2 hp hpc
  · intro i hi p hp
    simp [price, (Nat.dvd_of_mem_primeFactors hp)]


end CatalanCore.Uniform.Bank.ThirdsContent
