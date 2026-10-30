import CatalanCore.Uniform.Bank.FifthsContent.Ecrude
import CatalanCore.Uniform.Content.BankShared.BudgetedOne
import CatalanCore.Uniform.Content.BankShared.Budgeted
set_option Elab.async false

/-! # Scaled content of an alternating-geometry family from `GLE` bounds (lane B, B5c)

Generic in the slope `c` (`G = altGeom c`, `0 < c ≤ 1`).  The price of a member at a prime is its
OPTIMAL clearing exponent `lpOpt`; every layer (tropical, M3D, LP1/LP2, rank, UF) enters only by
proving a `GLE p n (Q i)` statement below the template line.  Primes dividing `M` are priced by the
crude exponent (`altGeom_gle_Ecrude`), so no exceptional-prime hypothesis remains. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset

/-- The alternating family at even scales. -/
noncomputable abbrev AltE (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) :=
  ((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)

lemma not_dvd_of_unit5 {M : ℕ} {p : ℕ} (hp : p.Prime) {c : ZMod M} (hc : IsUnit c)
    (hpc : (p : ZMod M) = c) : ¬ p ∣ M := by
  rw [← ZMod.isUnit_prime_iff_not_dvd hp, hpc]; exact hc

open Classical in
/-- The optimal clearing exponent of a member at a prime (`0` at non-primes). -/
noncomputable def lpOpt5 (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (i : (AltE c hc Fr depth).ι)
    (p : ℕ) : ℕ :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    if h : ∃ n, GLE p n ((AltE c hc Fr depth).Q i) then Nat.find h else 0
  else 0

theorem lpOpt5_gle (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (i : (AltE c hc Fr depth).ι)
    (p : ℕ) [hp : Fact p.Prime] (h : ∃ n, GLE p n ((AltE c hc Fr depth).Q i)) :
    GLE p (lpOpt5 c hc Fr depth i p) ((AltE c hc Fr depth).Q i) := by
  classical
  unfold lpOpt5
  rw [dif_pos hp.out, dif_pos h]
  exact Nat.find_spec h

theorem lpOpt5_le (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (i : (AltE c hc Fr depth).ι)
    (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (h : GLE p n ((AltE c hc Fr depth).Q i)) :
    lpOpt5 c hc Fr depth i p ≤ n := by
  classical
  unfold lpOpt5
  rw [dif_pos hp.out, dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

theorem exists_gle_even5 (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (Fr : Frame) (depth : ℕ)
    (i : (AltE c hc Fr depth).ι) (hi : (AltE c hc Fr depth).Adm i) (p : ℕ) [Fact p.Prime] :
    ∃ n, GLE p n ((AltE c hc Fr depth).Q i) :=
  ⟨_, altGeom_gle_Ecrude c hc hc1 Fr depth i hi.2 p⟩

theorem alt_content_of_bounds (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (Fr : Frame) (depth : ℕ)
    (M : ℕ) [NeZero M] (Lam : ℝ)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template) (τ : ℝ)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Lam + ε)
    (tend_le : ∀ ε : ℝ, 0 < ε → ∀ c' : ZMod M, IsUnit c' → (tmpl ε c').tend ≤ τ)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, (AltE c hc Fr depth).Adm i → ∀ c' : ZMod M, IsUnit c' →
      ∀ p : ℕ, p.Prime → (p : ZMod M) = c' → ⌊(tmpl ε c').tend * (altGeom c hc).scale i⌋₊ < p →
        ∀ [Fact p.Prime], GLE p 0 ((AltE c hc Fr depth).Q i))
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, (AltE c hc Fr depth).Adm i → ∀ c' : ZMod M, IsUnit c' →
      ∀ p : ℕ, p ≤ ⌊(tmpl ε c').t1 * (altGeom c hc).scale i⌋₊ → p.Prime → (p : ZMod M) = c' →
        ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((AltE c hc Fr depth).Q i) ∧
          (n : ℝ) ≤ (tmpl ε c').α0 * (altGeom c hc).scale i + B.X ((altGeom c hc).scale i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, (AltE c hc Fr depth).Adm i → ∀ c' : ZMod M, IsUnit c' →
      ∀ P ∈ (tmpl ε c').l, ∀ p : ℕ, ⌊P.s * (altGeom c hc).scale i⌋₊ < p →
        p ≤ ⌊P.t * (altGeom c hc).scale i⌋₊ → p.Prime → (p : ZMod M) = c' →
        ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((AltE c hc Fr depth).Q i) ∧
          (n : ℝ) ≤ P.α * (altGeom c hc).scale i + P.β * p + P.C) :
    HasScaledContent (AltE c hc Fr depth) (altGeom c hc).scale Lam := by
  classical
  let sc := (altGeom c hc).scale
  -- price: crude exponent at primes dividing `M`, the optimal exponent elsewhere
  let price : (AltE c hc Fr depth).ι → ℕ → ℕ := fun i p =>
    if p ∣ M then Ecrude (cFr Fr) i.1 p else lpOpt5 c hc Fr depth i p
  have hpr : ∀ i p, ¬ p ∣ M → price i p = lpOpt5 c hc Fr depth i p := fun i p h => by
    simp [price, h]
  have hlcut : ∀ i, (AltE c hc Fr depth).Adm i → ∀ ε : ℝ, 0 < ε → ∀ c' : ZMod M, IsUnit c' →
      ⌊(tmpl ε c').tend * sc i⌋₊ ≤ ⌊τ * sc i⌋₊ := by
    intro i _ ε hε c' hc'
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right (tend_le ε hε c' hc') (Nat.cast_nonneg _))
  refine hasScaledContent_budgeted_lim (AltE c hc Fr depth) sc M
    (fun i => NodeFamily.family_degree Fr (altGeom c hc).geometry depth i) price
    (fun i => max (⌊τ * sc i⌋₊ + 1) (M + 1)) ?_ ?_ B Lam tmpl hmass ?_ ?_ ?_ ?_
    (exc_of_Ecrude (AltE c hc Fr depth) sc M price (cFr Fr) ?_)
  · intro i hi p hpF
    by_cases h : p ∣ M
    · simp only [price, h, if_true]
      exact altGeom_gle_Ecrude c hc hc1 Fr depth i hi.2 p
    · simp only [price, h, if_false]
      exact lpOpt5_gle c hc Fr depth i p (exists_gle_even5 c hc hc1 Fr depth i hi p)
  · intro i hi p hp hcut
    have hM : ¬ p ∣ M := fun h => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h
      have := (le_max_right (⌊τ * sc i⌋₊ + 1) (M + 1)).trans hcut
      omega
    have hunit : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hM
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt : ⌊(tmpl 1 (p : ZMod M)).tend * sc i⌋₊ < p := by
      have := hlcut i hi 1 one_pos _ hunit
      have := (le_max_left (⌊τ * sc i⌋₊ + 1) (M + 1)).trans hcut
      omega
    rw [hpr i p hM]
    exact Nat.le_zero.1 (lpOpt5_le c hc Fr depth i p (tail 1 one_pos i hi _ hunit p hp rfl hlt))
  · intro ε hε i hi c' hc' p hp hpc hlt
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hpr i p (not_dvd_of_unit5 hp hc' hpc)]
    exact Nat.le_zero.1 (lpOpt5_le c hc Fr depth i p (tail ε hε i hi c' hc' p hp hpc hlt))
  · intro ε hε i hi c' hc'
    have := hlcut i hi ε hε c' hc'
    exact lt_of_le_of_lt this (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
  · intro ε hε i hi c' hc' p h1 hp hpc
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hpr i p (not_dvd_of_unit5 hp hc' hpc)]
    obtain ⟨n, hn, hb⟩ := pre ε hε i hi c' hc' p h1 hp hpc
    exact (Nat.cast_le.2 (lpOpt5_le c hc Fr depth i p hn)).trans hb
  · intro ε hε i hi c' hc' P hP p h1 h2 hp hpc
    haveI : Fact p.Prime := ⟨hp⟩
    show (price i p : ℝ) ≤ _
    rw [hpr i p (not_dvd_of_unit5 hp hc' hpc)]
    obtain ⟨n, hn, hb⟩ := cov ε hε i hi c' hc' P hP p h1 h2 hp hpc
    exact (Nat.cast_le.2 (lpOpt5_le c hc Fr depth i p hn)).trans hb
  · intro i hi p hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    simp only [price, hd, if_true]
    exact le_rfl

#print axioms alt_content_of_bounds
end CatalanCore.Uniform.Bank.FifthsContent
