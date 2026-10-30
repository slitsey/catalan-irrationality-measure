module

public import CatalanCore.Uniform.Content.SmallPrimes.Cover
public import CatalanCore.Uniform.Measure.NV0

@[expose] public section
set_option Elab.async false

/-! # Shared contract 4 (lane H17): the content assembler with an exceptional-prime budget

`SmallPrimes.ContentCoverB.hasContent_of_cover` needs `price <= K * r` at each prime dividing the
modulus `M` (field `exc`).  For the exceptional primes of the hybrid banks the honest price is only
`O(r log r)` (the crude exponent `Ecrude`), so the assumption is replaced by

    exc : for all eps > 0, eventually (in the scale), sum_{p | M} price i p * log p <= eps * (scale i)^2.

All prime factors are retained in the denominator `prod_{p < cut} p ^ price p`.  The conclusion is
stated in scale units (`HasScaledContent`), with constant exactly `Lambda`:

* `hasScaledContent_budgeted`: one template, `Lambda = contentConstant M tmpl`;
* `hasScaledContent_budgeted_lim`: an `eps`-indexed family of finite templates (the same price and
  the same denominator for every `eps`) whose constants are `<= Lambda + eps`; conclusion at the
  limit `Lambda`.
-/

namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset Polynomial
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.SmallPrimes

/-- The prime-sum fibre over a unit class is the class sum. -/
lemma fiber_eq_clsSum_cut (M : ℕ) [NeZero M] (τ : Template) (price : ℕ → ℕ) (cut : ℕ)
    (r : ℕ) (c : ZMod M)
    (htail : ∀ p : ℕ, p.Prime → (p : ZMod M) = c → ⌊τ.tend * r⌋₊ < p → price p = 0)
    (hlt : ⌊τ.tend * r⌋₊ < cut) (hc : IsUnit c) :
    ∑ p ∈ (((range cut).filter Nat.Prime).filter (fun p => ¬ p ∣ M)).filter
        (fun p : ℕ => (p : ZMod M) = c), (price p : ℝ) * Real.log p =
      clsSum M c (fun p => (price p : ℝ)) 0 ⌊τ.tend * r⌋₊ := by
  unfold clsSum
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp ⊢
    obtain ⟨⟨hp0, hpB⟩, hpp, hpc⟩ := hp
    refine ⟨⟨⟨?_, hpp⟩, ?_⟩, hpc⟩
    · exact lt_of_le_of_lt hpB hlt
    · rw [← ZMod.isUnit_prime_iff_not_dvd hpp, hpc]; exact hc
  · intro p hp hpn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, not_and] at hp hpn
    obtain ⟨⟨⟨hpb, hpp⟩, hpd⟩, hpc⟩ := hp
    have hB : ⌊τ.tend * r⌋₊ < p := by
      by_contra hcon
      exact hpn ⟨hpp.pos, not_lt.mp hcon⟩ hpp hpc
    have h0 := htail p hpp hpc hB
    simp only [h0, Nat.cast_zero, zero_mul]

/-- The class sum of the price: the prefix is bounded by `alpha0 r` once the small-prime budget `X`
is removed, and the budget costs `<= eps1/2 * r^2`. -/
lemma clsSum_le_budget (M : ℕ) [NeZero M] (τ : Template) (price : ℕ → ℕ) (B : SmallBudget)
    (r : ℕ) (c : ZMod M) {ε1 : ℝ}
    (hpre : ∀ p : ℕ, p ≤ ⌊τ.t1 * r⌋₊ → p.Prime → (p : ZMod M) = c →
      (price p : ℝ) ≤ τ.α0 * r + B.X r p)
    (hcov : ∀ P ∈ τ.l, Covers c (fun p => (price p : ℝ)) r P)
    (hH : ∀ w : ℕ → ℝ,
      (∀ p, p ≤ ⌊τ.t1 * r⌋₊ → p.Prime → (p : ZMod M) = c → w p ≤ τ.α0 * r) →
      (∀ P ∈ τ.l, Covers c w r P) →
      clsSum M c w 0 ⌊τ.tend * r⌋₊ ≤ (r : ℝ) ^ 2 * (τ.mass / (M.totient : ℝ) + ε1 / 2))
    (hB : ∑ p ∈ (range (B.cut r + 1)).filter Nat.Prime, B.X r p * Real.log p ≤
      ε1 / 2 * (r : ℝ) ^ 2) :
    clsSum M c (fun p => (price p : ℝ)) 0 ⌊τ.tend * r⌋₊ ≤
      (r : ℝ) ^ 2 * (τ.mass / (M.totient : ℝ) + ε1) := by
  classical
  let w : ℕ → ℝ := fun p => max ((price p : ℝ) - B.X r p) 0
  have hwle : ∀ p, w p ≤ (price p : ℝ) := fun p =>
    max_le (by linarith [B.nonneg r p]) (Nat.cast_nonneg _)
  have hwge : ∀ p, (price p : ℝ) ≤ w p + B.X r p := fun p => by
    have := le_max_left ((price p : ℝ) - B.X r p) 0
    simp only [w]; linarith
  have hpre' : ∀ p, p ≤ ⌊τ.t1 * r⌋₊ → p.Prime → (p : ZMod M) = c → w p ≤ τ.α0 * r :=
    fun p h1 hp hpc =>
      max_le (by linarith [hpre p h1 hp hpc, B.nonneg r p])
        (mul_nonneg τ.hα0 (Nat.cast_nonneg _))
  have hcov' : ∀ P ∈ τ.l, Covers c w r P := fun P hP p h1 h2 hp hpc =>
    (hwle p).trans (hcov P hP p h1 h2 hp hpc)
  have hw1 := hH w hpre' hcov'
  unfold clsSum at hw1 ⊢
  set F := (Finset.Ioc 0 ⌊τ.tend * r⌋₊).filter
    (fun p : ℕ => p.Prime ∧ (p : ZMod M) = c) with hF
  have h1 : ∑ p ∈ F, (price p : ℝ) * Real.log p ≤
      ∑ p ∈ F, w p * Real.log p + ∑ p ∈ F, B.X r p * Real.log p := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    calc (price p : ℝ) * Real.log p ≤ (w p + B.X r p) * Real.log p :=
          mul_le_mul_of_nonneg_right (hwge p) hl
      _ = w p * Real.log p + B.X r p * Real.log p := by ring
  have h2 : ∑ p ∈ F, B.X r p * Real.log p ≤
      ∑ p ∈ (range (B.cut r + 1)).filter Nat.Prime, B.X r p * Real.log p := by
    have hne : ∀ p ∈ F, B.X r p * Real.log p ≠ 0 → p ≤ B.cut r := by
      intro p _ hne
      by_contra hlt
      push_neg at hlt
      exact hne (by rw [B.supp r p hlt]; simp)
    rw [← Finset.sum_filter_of_ne hne]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [hF, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp ⊢
      exact ⟨by omega, hp.1.2.1⟩
    · intro p _ _
      exact mul_nonneg (B.nonneg _ _) (Real.log_natCast_nonneg p)
  have e : (r : ℝ) ^ 2 * (τ.mass / (M.totient : ℝ) + ε1 / 2) + ε1 / 2 * (r : ℝ) ^ 2 =
      (r : ℝ) ^ 2 * (τ.mass / (M.totient : ℝ) + ε1) := by ring
  linarith

/-- **The log of the denominator.**  Prime factors dividing `M` are kept; their total weighted price
enters as an additive term, the unit classes are bounded by the template. -/
lemma log_den_le_budget (M : ℕ) [NeZero M] (tmpl : ZMod M → Template) (price : ℕ → ℕ)
    (cut r : ℕ) {ε1 : ℝ} (hε1 : 0 ≤ ε1)
    (H : ∀ c ∈ unitClasses M,
      clsSum M c (fun p => (price p : ℝ)) 0 ⌊(tmpl c).tend * r⌋₊ ≤
        (r : ℝ) ^ 2 * ((tmpl c).mass / (M.totient : ℝ) + ε1))
    (htail : ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
      ⌊(tmpl c).tend * r⌋₊ < p → price p = 0)
    (hlt : ∀ c : ZMod M, IsUnit c → ⌊(tmpl c).tend * r⌋₊ < cut) :
    Real.log (primeDenominator cut price) ≤
      (r : ℝ) ^ 2 * (contentConstant M tmpl + M * ε1) +
        ∑ p ∈ M.primeFactors, (price p : ℝ) * Real.log p := by
  classical
  rw [log_primeDenominator]
  set S := (range cut).filter Nat.Prime with hS
  set g : ℕ → ℝ := fun p => (price p : ℝ) * Real.log p with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p =>
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∣ M) g]
  have hexc : ∑ p ∈ S.filter (fun p => p ∣ M), g p ≤ ∑ p ∈ M.primeFactors, g p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.2 ⟨(Finset.mem_filter.mp hpS).2, hpd, NeZero.ne M⟩
    · intro p _ _; exact hg0 p
  have hmaps : ∀ p ∈ S.filter (fun p => ¬ p ∣ M), (p : ZMod M) ∈ unitClasses M := by
    intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    exact mem_unitClasses.2 ((ZMod.isUnit_prime_iff_not_dvd (Finset.mem_filter.mp hpS).2).2 hpd)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ => (p : ZMod M)) hmaps g]
  have hunit : ∑ c ∈ unitClasses M, ∑ p ∈ (S.filter (fun p => ¬ p ∣ M)).filter
        (fun p : ℕ => (p : ZMod M) = c), g p ≤
      (r : ℝ) ^ 2 * (contentConstant M tmpl + M * ε1) := by
    have h1 : ∀ c ∈ unitClasses M, ∑ p ∈ (S.filter (fun p => ¬ p ∣ M)).filter
        (fun p : ℕ => (p : ZMod M) = c), g p ≤
        (r : ℝ) ^ 2 * ((tmpl c).mass / (M.totient : ℝ) + ε1) := by
      intro c hc
      have hcu := mem_unitClasses.1 hc
      have := fiber_eq_clsSum_cut M (tmpl c) price cut r c (htail c hcu) (hlt c hcu) hcu
      exact this.le.trans (H c hc)
    calc _ ≤ ∑ c ∈ unitClasses M, (r : ℝ) ^ 2 * ((tmpl c).mass / (M.totient : ℝ) + ε1) :=
          Finset.sum_le_sum h1
      _ = (r : ℝ) ^ 2 * (contentConstant M tmpl + (unitClasses M).card * ε1) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            contentConstant, Finset.sum_div]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have : ((unitClasses M).card : ℝ) ≤ M := by exact_mod_cast card_unitClasses_le M
          nlinarith
  linarith

/-- **Shared contract 4, limit form (`hasScaledContent_budgeted_lim`).**  One price function and one
denominator `prod_{p < cut i} p ^ price i p` (all prime factors retained, including those dividing
`M`), an `eps`-indexed family of finite templates with `contentConstant M (tmpl eps) <= Lambda + eps`,
and an exceptional-prime weighted sum that is `o(scale^2)`: the coefficient content is exactly
`Lambda` in scale units. -/
theorem hasScaledContent_budgeted_lim (Fam : PolyFamily) (sc : Fam.ι → ℕ) (M : ℕ) [NeZero M]
    (hnat : ∀ i, (Fam.Q i).natDegree ≤ Fam.deg i)
    (price : Fam.ι → ℕ → ℕ) (cut : Fam.ι → ℕ)
    (gle : ∀ i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], GLE p (price i p) (Fam.Q i))
    (zero_ge : ∀ i, Fam.Adm i → ∀ p : ℕ, p.Prime → cut i ≤ p → price i p = 0)
    (B : SmallBudget) (Λ : ℝ) (tmpl : ℝ → ZMod M → Template)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Λ + ε)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime →
      (p : ZMod M) = c → ⌊(tmpl ε c).tend * sc i⌋₊ < p → price i p = 0)
    (tail_lt : ∀ ε : ℝ, 0 < ε → ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c →
      ⌊(tmpl ε c).tend * sc i⌋₊ < cut i)
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl ε c).t1 * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
        (price i p : ℝ) ≤ (tmpl ε c).α0 * sc i + B.X (sc i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl ε c).l,
      Covers c (fun p => (price i p : ℝ)) (sc i) P)
    (exc : ∀ ε : ℝ, 0 < ε → ∃ R0 : ℕ, ∀ i, Fam.Adm i → R0 ≤ sc i →
      ∑ p ∈ M.primeFactors, (price i p : ℝ) * Real.log p ≤ ε * (sc i : ℝ) ^ 2) :
    HasScaledContent Fam sc Λ := by
  classical
  have hden : ∀ i, 0 < primeDenominator (cut i) (price i) := fun i =>
    primeDenominator_pos _ _
  refine ⟨fun i => primeDenominator (cut i) (price i), hden, ?_, ?_⟩
  · intro i hi p q hq
    refine int_clear' (Fam.Q i) (Fam.deg i) (hnat i) _ ?_ p q hq
    intro k
    refine primeDenominator_integral (cut i) (price i) (Fam.Q i) ?_ k
    intro p hp
    by_cases hb : p < cut i
    · simpa only [if_pos hb] using gle i hi p
    · have h0 := zero_ge i hi p hp.out (not_lt.mp hb)
      have := gle i hi p
      rw [h0] at this
      simpa only [if_neg hb] using this
  · intro ε hε
    set ε3 : ℝ := ε / 3 with hε3
    have hε3p : 0 < ε3 := by positivity
    set τ : ZMod M → Template := tmpl ε3 with hτ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
    set ε1 : ℝ := ε / (3 * ((M : ℝ) + 1)) with hε1def
    have hε1 : 0 < ε1 := by positivity
    have hMε1 : (M : ℝ) * ε1 ≤ ε3 := by
      have : (M : ℝ) * ε1 = ε / 3 * ((M : ℝ) / ((M : ℝ) + 1)) := by
        rw [hε1def]; field_simp
      rw [this, hε3]
      have h1 : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith [div_pos hε (by norm_num : (0 : ℝ) < 3)]
    obtain ⟨Ra, hRa⟩ := Filter.eventually_atTop.1
      ((eventually_classes τ (half_pos hε1)).and (B.small (ε1 / 2) (half_pos hε1)))
    obtain ⟨Rb, hRb⟩ := exc ε3 hε3p
    refine ⟨max Ra Rb, fun i hi hR => ?_⟩
    have hRa' : Ra ≤ sc i := (le_max_left _ _).trans hR
    have hRb' : Rb ≤ sc i := (le_max_right _ _).trans hR
    obtain ⟨hH, hBu⟩ := hRa (sc i) hRa'
    have hmain := log_den_le_budget M τ (price i) (cut i) (sc i) hε1.le
      (fun c hc => clsSum_le_budget M (τ c) (price i) B (sc i) c
        (pre ε3 hε3p i hi c (mem_unitClasses.1 hc))
        (cov ε3 hε3p i hi c (mem_unitClasses.1 hc)) (hH c hc) hBu)
      (tail ε3 hε3p i hi) (tail_lt ε3 hε3p i hi)
    have hexc := hRb i hi hRb'
    have hcc : contentConstant M τ ≤ Λ + ε3 := hmass ε3 hε3p
    have hsq0 : (0 : ℝ) ≤ (sc i : ℝ) ^ 2 := sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_left (by linarith : contentConstant M τ + M * ε1 ≤ Λ + 2 * ε3) hsq0
    show Real.log ((primeDenominator (cut i) (price i) : ℕ) : ℝ) ≤ _
    nlinarith [hmain, hexc, h2]

end CatalanCore.Uniform.Content.BankShared
